const std = @import("std");
const ir = @import("ir.zig");
const diagnostics = @import("diagnostics.zig");
const validation = @import("validate.zig");
const pre_resolution_admission = @import("pre_resolution_admission.zig");
const proof_orchestrator = @import("proof_orchestrator.zig");
const solver_backend = @import("solver_backend.zig");
const emit_luau = @import("emit_luau.zig");
const checked_emission = @import("checked_emission.zig");
const control_flow = @import("control_flow.zig");

pub const Options = struct {
    profile: ir.AdmissionProfile,
    emit_luau: ?emit_luau.Target = null,
    preserve_admitted_readable: bool = false,
    /// Force the solver-free admitted-readable path when the caller already
    /// owns a completed readable admission. This keeps exact branch values
    /// from routing a finished IR back through whole-program resolution.
    force_preserve_admitted_readable: bool = false,
};

pub const Outcome = struct {
    allocator: std.mem.Allocator,
    resolved: ?proof_orchestrator.ResolvedProgram,
    report: diagnostics.Report,
    luau_source: ?[]u8 = null,

    pub fn deinit(self: *Outcome) void {
        if (self.luau_source) |source| self.allocator.free(source);
        self.report.deinit();
        if (self.resolved) |*resolved| resolved.deinit();
        self.* = undefined;
    }

    pub fn isAdmitted(self: *const Outcome) bool {
        return self.resolved != null and self.report.isClean();
    }

    pub fn program(self: *const Outcome) ?*const ir.Program {
        if (self.resolved) |*resolved| return &resolved.program;
        return null;
    }
};

pub const CheckedOutcome = struct {
    pipeline: Outcome,
    publication: ?checked_emission.Outcome,

    pub fn deinit(self: *CheckedOutcome) void {
        if (self.publication) |*publication| publication.deinit();
        self.pipeline.deinit();
        self.* = undefined;
    }

    pub fn isPublished(self: CheckedOutcome) bool {
        return self.pipeline.isAdmitted() and self.publication != null and self.publication.?.succeeded();
    }
};

pub fn runAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    engine: solver_backend.Backend,
    options: Options,
) !Outcome {
    if (options.emit_luau != null and options.profile != .readable_luau) return error.InvalidPipelineOptions;
    const emission_target = options.emit_luau;

    var preflight = try pre_resolution_admission.validateAlloc(allocator, program);
    if (!preflight.isClean()) {
        return .{
            .allocator = allocator,
            .resolved = null,
            .report = preflight,
        };
    }
    var preflight_owned = true;

    // Core-resolution callers already have a complete admission report. A
    // normalized no-solver program with authenticated rewrite history needs no
    // second admission pass or proof composition; retain the clean report and
    // publish the existing program directly.
    if (options.profile == .core and
        !proof_orchestrator.hasSerializedSolverState(program) and
        program.edge_rewrites.len != 0)
    {
        const resolved = try proof_orchestrator.preserveAdmittedAlloc(allocator, program);
        return .{
            .allocator = allocator,
            .resolved = resolved,
            .report = preflight,
        };
    }

    if (options.profile == .readable_luau and
        !options.preserve_admitted_readable and
        !proof_orchestrator.hasSerializedSolverState(program) and
        program.edge_rewrites.len != 0)
    {
        var readable_report = try validateReadableForEmission(
            allocator,
            program,
            emission_target orelse .standard_luau,
        );
        preflight.deinit();
        preflight_owned = false;
        if (readable_report.isClean()) {
            errdefer readable_report.deinit();
            var resolved = try proof_orchestrator.preserveAdmittedAlloc(allocator, program);
            errdefer resolved.deinit();

            var source: ?[]u8 = null;
            if (options.emit_luau) |target| {
                source = try emit_luau.emitAdmittedAllocForTarget(allocator, &resolved.program, target);
            }
            return .{
                .allocator = allocator,
                .resolved = resolved,
                .report = readable_report,
                .luau_source = source,
            };
        }
        readable_report.deinit();
    }
    if (preflight_owned) preflight.deinit();

    // A readable-admitted frontend may intentionally publish no solver state:
    // there is no pending proof or optional branch specialization to apply.
    // Re-running derived planner work can make a proven readable CFG less
    // structured, so preserve its authenticated history and let the ordinary
    // emitter perform the remaining backend work.
    const has_exact_branch_truth = if (options.preserve_admitted_readable and
        options.profile == .readable_luau and
        !proof_orchestrator.hasSerializedSolverState(program))
        control_flow.hasExactBranchTruth(program)
    else
        false;
    // A non-empty rewrite history is part of the admitted CFG contract. When
    // no solver state remains, its exact branches were already consumed by
    // the frontend or an earlier authenticated backend pass; applying the
    // direct exact-branch adapter again can invalidate that history.
    const has_authenticated_rewrite_history = program.edge_rewrites.len != 0;

    if (options.preserve_admitted_readable and
        options.profile == .readable_luau and
        (options.force_preserve_admitted_readable or
            !proof_orchestrator.hasSerializedSolverState(program)) and
        (!has_exact_branch_truth or
            options.force_preserve_admitted_readable or
            has_authenticated_rewrite_history))
    {
        var readable_report = try validateReadableForEmission(
            allocator,
            program,
            emission_target orelse .standard_luau,
        );
        if (readable_report.isClean() and has_authenticated_rewrite_history) {
            errdefer readable_report.deinit();
            var resolved = try proof_orchestrator.preserveAdmittedAlloc(allocator, program);
            errdefer resolved.deinit();

            var source: ?[]u8 = null;
            if (options.emit_luau) |target| {
                source = try emit_luau.emitAdmittedAllocForTarget(allocator, &resolved.program, target);
            }
            return .{
                .allocator = allocator,
                .resolved = resolved,
                .report = readable_report,
                .luau_source = source,
            };
        }
        if (readable_report.isClean()) {
            defer readable_report.deinit();
            var resolved = if (!has_authenticated_rewrite_history)
                // The caller's engine solves the pending proofs on this path.
                // Partial scope: unlike resolveAlloc, this path never calls
                // verifyCoreCertificatesAlloc, so persisted unsat cores are
                // still not replayed with `engine` here.
                try proof_orchestrator.preserveAdmittedWithExactControlAlloc(
                    allocator,
                    program,
                    engine,
                )
            else
                try proof_orchestrator.preserveAdmittedAlloc(allocator, program);
            errdefer resolved.deinit();

            // The direct adapter may authenticate and rewrite exact control
            // edges before emission. Re-admit the transformed program so
            // publication cannot rely on the original graph's report.
            var transformed_report = try validateReadableForEmission(
                allocator,
                &resolved.program,
                emission_target orelse .standard_luau,
            );
            errdefer transformed_report.deinit();
            try transformed_report.append(&resolved.solve_report);

            var source: ?[]u8 = null;
            if (transformed_report.isClean()) {
                if (options.emit_luau) |target| source = try emit_luau.emitAdmittedAllocForTarget(allocator, &resolved.program, target);
            }
            return .{
                .allocator = allocator,
                .resolved = resolved,
                .report = transformed_report,
                .luau_source = source,
            };
        }
        readable_report.deinit();
    }

    var resolved = try proof_orchestrator.resolveAlloc(allocator, program, engine);
    errdefer resolved.deinit();
    if (resolved.control_result.conflicting_certificate) |certificate_index| {
        var conflict_report = diagnostics.Report.init(allocator);
        errdefer conflict_report.deinit();
        try conflict_report.append(&resolved.solve_report);
        try conflict_report.add(.contradictory_solver_proof, certificate_index);
        return .{
            .allocator = allocator,
            .resolved = resolved,
            .report = conflict_report,
        };
    }
    var report = if (options.profile == .readable_luau and emission_target != null)
        try validateReadableForEmission(allocator, &resolved.program, emission_target.?)
    else
        try validation.validate(allocator, &resolved.program, options.profile);
    errdefer report.deinit();
    try report.append(&resolved.solve_report);

    var source: ?[]u8 = null;
    if (report.isClean()) {
        if (options.emit_luau) |target| {
            source = try emit_luau.emitAdmittedAllocForTarget(allocator, &resolved.program, target);
        }
    }
    return .{
        .allocator = allocator,
        .resolved = resolved,
        .report = report,
        .luau_source = source,
    };
}

fn validateReadableForEmission(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    target: emit_luau.Target,
) !diagnostics.Report {
    return validation.validateForTarget(allocator, program, .readable_luau, target);
}

pub fn runCheckedAlloc(
    allocator: std.mem.Allocator,
    io: std.Io,
    program: *const ir.Program,
    engine: solver_backend.Backend,
    target: emit_luau.Target,
    output_path: []const u8,
    compiler_path: []const u8,
) !CheckedOutcome {
    return runCheckedWithOptionsAlloc(
        allocator,
        io,
        program,
        engine,
        output_path,
        compiler_path,
        .{ .profile = .readable_luau, .emit_luau = target },
    );
}

pub fn runCheckedAdmittedReadableAlloc(
    allocator: std.mem.Allocator,
    io: std.Io,
    program: *const ir.Program,
    target: emit_luau.Target,
    output_path: []const u8,
    compiler_path: []const u8,
) !CheckedOutcome {
    return runCheckedWithOptionsAlloc(
        allocator,
        io,
        program,
        solver_backend.internalFacts(),
        output_path,
        compiler_path,
        .{
            .profile = .readable_luau,
            .emit_luau = target,
            .preserve_admitted_readable = true,
        },
    );
}

pub fn runCheckedDirectAdmittedReadableAlloc(
    allocator: std.mem.Allocator,
    io: std.Io,
    program: *const ir.Program,
    target: emit_luau.Target,
    output_path: []const u8,
    compiler_path: []const u8,
) !CheckedOutcome {
    return runCheckedWithOptionsAlloc(
        allocator,
        io,
        program,
        solver_backend.internalFacts(),
        output_path,
        compiler_path,
        .{
            .profile = .readable_luau,
            .emit_luau = target,
            .preserve_admitted_readable = true,
            .force_preserve_admitted_readable = true,
        },
    );
}

fn runCheckedWithOptionsAlloc(
    allocator: std.mem.Allocator,
    io: std.Io,
    program: *const ir.Program,
    engine: solver_backend.Backend,
    output_path: []const u8,
    compiler_path: []const u8,
    options: Options,
) !CheckedOutcome {
    var outcome = try runAlloc(
        allocator,
        program,
        engine,
        options,
    );
    errdefer outcome.deinit();
    if (!outcome.isAdmitted()) return .{ .pipeline = outcome, .publication = null };
    return .{
        .pipeline = outcome,
        .publication = checked_emission.publish(allocator, io, output_path, compiler_path, outcome.luau_source.?),
    };
}

test "pipeline admits and emits through one ordered outcome" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var outcome = try runAlloc(
        std.testing.allocator,
        &fixture.program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expect(outcome.program() != null);
    try std.testing.expect(outcome.luau_source != null);
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "return fn_add_and_double") != null);
}

test "explicit readable preservation keeps an admitted solver-free program" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var outcome = try runAlloc(
        std.testing.allocator,
        &fixture.program,
        solver_backend.internalFacts(),
        .{
            .profile = .readable_luau,
            .emit_luau = .standard_luau,
            .preserve_admitted_readable = true,
        },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expectEqual(@as(usize, 0), outcome.program().?.queries.len);
    try std.testing.expectEqual(@as(usize, 0), outcome.program().?.obligations.len);
    try std.testing.expect(outcome.luau_source != null);
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "return fn_add_and_double") != null);
}

const EngineProbe = struct {
    attempts: usize = 0,

    fn backend(self: *EngineProbe) solver_backend.Backend {
        return .{ .engine = .internal_facts, .context = self, .solve_fn = solve };
    }

    fn solve(context: ?*anyopaque, _: std.mem.Allocator, program: *const ir.Program, query: ir.SolverQuery) !solver_backend.Result {
        const self: *EngineProbe = @ptrCast(@alignCast(context.?));
        self.attempts += 1;
        const resolution = @import("solver.zig").solve(program, query);
        return .{
            .engine = .internal_facts,
            .resolution = resolution,
            .unknown_reason = if (resolution == .unknown) .bounded_internal_incompleteness else null,
        };
    }
};

test "readable preservation resolves pending proofs with the caller's engine" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const terms = [_]ir.SolverTerm{.{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } }};
    const queries = [_]ir.SolverQuery{.{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(0) }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(0),
        .status = .unproven,
        .evidence = &.{fixture.proof},
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;
    const options: Options = .{
        .profile = .readable_luau,
        .emit_luau = .standard_luau,
        .preserve_admitted_readable = true,
        .force_preserve_admitted_readable = true,
    };

    var probe: EngineProbe = .{};
    var outcome = try runAlloc(std.testing.allocator, &program, probe.backend(), options);
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expectEqual(@as(usize, 1), probe.attempts); // fails today: 0
    try std.testing.expectEqual(@as(usize, 1), outcome.program().?.certificates.len);
    try std.testing.expectEqual(ir.ClaimStatus.proved, outcome.program().?.claims[0].status);

    // A selected engine that cannot run must surface, not be silently replaced (no Z3 needed:
    // z3_disabled.zig is a plain Zig file whose backend reports engine .z3 and fails with Z3Disabled).
    try std.testing.expectError(
        error.Z3Disabled,
        runAlloc(std.testing.allocator, &program, @import("z3_disabled.zig").defaultBackend(), options),
    );
}

test "readable preservation resolves exact pure branches before structuring" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_is_negative.index()].operation = .{ .constant = .{ .boolean = true } };
    var program = fixture.program;
    program.instructions = &instructions;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{
            .profile = .readable_luau,
            .emit_luau = .standard_luau,
            .preserve_admitted_readable = true,
        },
    );
    defer outcome.deinit();

    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expect(outcome.luau_source != null);
    try std.testing.expectEqual(@as(usize, 1), outcome.resolved.?.control_result.rewritten_blocks);
    try std.testing.expectEqual(@as(usize, 1), outcome.program().?.queries.len);
    try std.testing.expectEqual(
        fixture.b_negative,
        outcome.program().?.blocks[fixture.b_entry.index()].terminator.jump.target,
    );
}

test "pipeline returns typed solver preflight blockers without invoking a backend" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(9),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .core },
    );
    defer outcome.deinit();
    try std.testing.expect(!outcome.isAdmitted());
    try std.testing.expect(outcome.program() == null);
    try std.testing.expect(outcome.report.contains(.invalid_query_reference));
}

test "pipeline preserves unknown obligations as typed emission blockers" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .semantic_atom = .{ .instruction_effects = fixture.i_sum } },
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .effect_proof,
        .subject = .{ .instruction = fixture.i_sum },
        .status = .open,
        .blocks_profile = .readable_luau,
        .detail = "internal facts cannot prove an unassumed semantic atom",
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.obligations = &obligations;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(!outcome.isAdmitted());
    try std.testing.expect(outcome.program() != null);
    try std.testing.expect(outcome.luau_source == null);
    try std.testing.expect(outcome.report.contains(.open_profile_obligation));
    try std.testing.expect(outcome.report.contains(.solver_unknown));
    try std.testing.expectEqual(ir.ObligationStatus.open, outcome.program().?.obligations[0].status);
    try std.testing.expect(outcome.program().?.obligations[0].certificate == null);
    try std.testing.expect(outcome.resolved.?.solve_report.isClean());

    var checked = try runCheckedAlloc(
        std.testing.allocator,
        std.testing.io,
        &program,
        solver_backend.internalFacts(),
        .standard_luau,
        "unused-blocked-output.luau",
        "compiler-must-not-run",
    );
    defer checked.deinit();
    try std.testing.expect(!checked.pipeline.isAdmitted());
    try std.testing.expect(checked.publication == null);
    try std.testing.expect(!checked.isPublished());

    var found_bounded_unknown = false;
    for (outcome.report.diagnostics.items) |diagnostic| {
        if (diagnostic.code != .solver_unknown) continue;
        try std.testing.expectEqual(@as(?u32, 0), diagnostic.entity_index);
        try std.testing.expectEqual(
            solver_backend.UnknownReason.bounded_internal_incompleteness,
            diagnostic.detail.solver_unknown.reason,
        );
        found_bounded_unknown = true;
    }
    try std.testing.expect(found_bounded_unknown);

    var core_outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .core },
    );
    defer core_outcome.deinit();
    try std.testing.expect(core_outcome.isAdmitted());
    try std.testing.expect(core_outcome.report.isClean());
    try std.testing.expect(core_outcome.report.contains(.solver_unknown));
}

const DominatingErrorLevelCase = struct {
    sum_operation: ir.Operation,
    factor_operation: ir.Operation,
    result_operation: ir.Operation,
    level: ir.ValueId,
    message: ir.ValueId,
    resolution: ir.SolverResolution,
    admitted: bool,
    tamper_cfg: bool = false,
};

fn expectDominatingErrorLevel(case: DominatingErrorLevelCase) !void {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const throw_block = ir.BlockId.fromIndex(fixture.blocks.len);
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation = case.sum_operation;
    instructions[fixture.i_sum.index()].effects = .pure;
    instructions[fixture.i_factor.index()].operation = case.factor_operation;
    instructions[fixture.i_factor.index()].effects = .pure;
    instructions[fixture.i_result.index()].operation = case.result_operation;
    instructions[fixture.i_result.index()].effects = .pure;
    var blocks = fixture.blocks ++ [_]ir.Block{.{
        .id = throw_block,
        .function = fixture.f_add,
        .terminator = .{ .throw_error = .{
            .value = case.message,
            .level = 0,
            .dynamic_level = case.level,
        } },
        .evidence = &.{fixture.proof},
    }};
    blocks[fixture.b_add.index()].terminator = .{ .jump = .{ .target = throw_block } };
    const function_blocks = [_]ir.BlockId{ fixture.b_add, throw_block };
    var functions = fixture.functions;
    functions[fixture.f_add.index()].blocks = &function_blocks;
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;

    var raw_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer raw_report.deinit();
    try std.testing.expect(raw_report.contains(.unsupported_readable_error_location));

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expectEqual(case.admitted, outcome.isAdmitted());
    try std.testing.expectEqual(case.admitted, outcome.luau_source != null);
    try std.testing.expect(!outcome.report.contains(.unsupported_readable_error_location));
    try std.testing.expectEqual(!case.admitted, outcome.report.contains(.open_profile_obligation));

    const resolved = outcome.program().?;
    try std.testing.expectEqual(@as(usize, 1), resolved.queries.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.obligations.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.certificates.len);
    const obligation = resolved.obligations[0];
    try std.testing.expectEqual(throw_block, obligation.subject.block);
    try std.testing.expectEqual(if (case.admitted) ir.ObligationStatus.discharged else .open, obligation.status);
    const certificate = resolved.certificates[obligation.certificate.?.index()];
    try std.testing.expectEqual(case.resolution, certificate.resolution);
    const query = resolved.queries[obligation.query.?.index()];
    const comparison = resolved.solver_terms[query.goal.index()].operation.binary;
    try std.testing.expectEqual(case.level, resolved.solver_terms[comparison.left.index()].operation.value_definition.value);
    if (case.admitted) {
        try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "__lifter_error") != null);
    }

    if (case.tamper_cfg) {
        const tampered_functions = try std.testing.allocator.dupe(ir.Function, resolved.functions);
        defer std.testing.allocator.free(tampered_functions);
        tampered_functions[fixture.f_add.index()].entry_block = throw_block;
        var tampered = resolved.*;
        tampered.functions = tampered_functions;
        var replay = try runAlloc(
            std.testing.allocator,
            &tampered,
            solver_backend.internalFacts(),
            .{ .profile = .core },
        );
        defer replay.deinit();
        try std.testing.expect(!replay.isAdmitted());
        try std.testing.expect(replay.program() == null);
        try std.testing.expect(replay.report.contains(.non_dominating_value_use));
    }
}

const UnpromotedPredecessorLevel = enum {
    parameter,
    effectful,
    nonfinite,
};

fn expectUnpromotedPredecessorLevel(kind: UnpromotedPredecessorLevel) !void {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const throw_block = ir.BlockId.fromIndex(fixture.blocks.len);
    var values = fixture.values;
    var instructions = fixture.instructions;
    const level = switch (kind) {
        .parameter => fixture.v_left,
        .effectful => blk: {
            instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "-1" } };
            instructions[fixture.i_factor.index()].effects = .{ .precision = .exact, .may_throw = true };
            break :blk fixture.v_factor;
        },
        .nonfinite => blk: {
            values[fixture.v_sum.index()].type = .number;
            values[fixture.v_factor.index()].type = .number;
            values[fixture.v_result.index()].type = .number;
            instructions[fixture.i_sum.index()].operation = .{ .constant = .{ .special_number = .negative_infinity } };
            instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .number = 1.0 } };
            instructions[fixture.i_result.index()].operation = .{ .binary = .{
                .operator = .add,
                .left = fixture.v_sum,
                .right = fixture.v_factor,
            } };
            break :blk fixture.v_sum;
        },
    };
    var blocks = fixture.blocks ++ [_]ir.Block{.{
        .id = throw_block,
        .function = fixture.f_add,
        .terminator = .{ .throw_error = .{
            .value = fixture.v_result,
            .level = 0,
            .dynamic_level = level,
        } },
        .evidence = &.{fixture.proof},
    }};
    blocks[fixture.b_add.index()].terminator = .{ .jump = .{ .target = throw_block } };
    const function_blocks = [_]ir.BlockId{ fixture.b_add, throw_block };
    var functions = fixture.functions;
    functions[fixture.f_add.index()].blocks = &function_blocks;
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(!outcome.isAdmitted());
    try std.testing.expect(outcome.program() != null);
    try std.testing.expect(outcome.luau_source == null);
    try std.testing.expect(outcome.report.contains(.unsupported_readable_error_location));
    try std.testing.expectEqual(@as(usize, 0), outcome.program().?.queries.len);
    try std.testing.expectEqual(@as(usize, 0), outcome.program().?.obligations.len);
    try std.testing.expectEqual(@as(usize, 0), outcome.program().?.certificates.len);
}

test "pipeline proves exact error levels from dominating predecessor blocks" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    try expectDominatingErrorLevel(.{
        .sum_operation = .{ .binary = .{ .operator = .add, .left = fixture.v_left, .right = fixture.v_right } },
        .factor_operation = .{ .constant = .{ .integer = "-1" } },
        .result_operation = .{ .binary = .{ .operator = .multiply, .left = fixture.v_sum, .right = fixture.v_factor } },
        .level = fixture.v_factor,
        .message = fixture.v_result,
        .resolution = .proved,
        .admitted = true,
    });
    try expectDominatingErrorLevel(.{
        .sum_operation = .{ .constant = .{ .integer = "-2" } },
        .factor_operation = .{ .constant = .{ .integer = "1" } },
        .result_operation = .{ .binary = .{ .operator = .add, .left = fixture.v_sum, .right = fixture.v_factor } },
        .level = fixture.v_result,
        .message = fixture.v_factor,
        .resolution = .proved,
        .admitted = true,
        .tamper_cfg = true,
    });
    try expectDominatingErrorLevel(.{
        .sum_operation = .{ .constant = .{ .integer = "1" } },
        .factor_operation = .{ .constant = .{ .integer = "1" } },
        .result_operation = .{ .binary = .{ .operator = .add, .left = fixture.v_sum, .right = fixture.v_factor } },
        .level = fixture.v_result,
        .message = fixture.v_factor,
        .resolution = .disproved,
        .admitted = false,
    });
}

test "pipeline keeps path-dependent and inexact predecessor levels unresolved" {
    inline for (std.meta.tags(UnpromotedPredecessorLevel)) |kind| {
        try expectUnpromotedPredecessorLevel(kind);
    }

    const fixture = @import("fixtures.zig").absolute_value_module;
    var blocks = fixture.blocks;
    blocks[fixture.b_join.index()].terminator = .{ .throw_error = .{
        .value = fixture.v_zero,
        .level = 0,
        .dynamic_level = fixture.v_absolute,
    } };
    var program = fixture.program;
    program.blocks = &blocks;
    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(!outcome.isAdmitted());
    try std.testing.expect(outcome.program() != null);
    try std.testing.expect(outcome.report.contains(.unsupported_readable_error_location));
    try std.testing.expectEqual(@as(usize, 0), outcome.program().?.queries.len);
    try std.testing.expectEqual(@as(usize, 0), outcome.program().?.obligations.len);
}

const BlockParameterErrorLevelCase = enum {
    shared_predecessors,
    duplicate_branch_edges,
    unreachable_disagreement,
    proved_dead_edge,
    reachable_disagreement,
    positive,
    parameter,
    effectful,
    nonfinite,
};

fn expectBlockParameterErrorLevel(kind: BlockParameterErrorLevelCase) !void {
    const fixture = @import("fixtures.zig").absolute_value_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_zero.index()].operation = .{ .constant = .{ .number = -1.0 } };
    instructions[fixture.i_negate.index()].operation = .{ .constant = .{ .number = -2.0 } };
    instructions[fixture.i_negate.index()].effects = .pure;
    var blocks = fixture.blocks;
    blocks[fixture.b_negative.index()].terminator = .{ .jump = .{
        .target = fixture.b_join,
        .arguments = &.{fixture.v_zero},
    } };
    blocks[fixture.b_nonnegative.index()].terminator = .{ .jump = .{
        .target = fixture.b_join,
        .arguments = &.{fixture.v_zero},
    } };
    blocks[fixture.b_join.index()].terminator = .{ .throw_error = .{
        .value = fixture.v_input,
        .level = 0,
        .dynamic_level = fixture.v_absolute,
    } };

    switch (kind) {
        .shared_predecessors => {},
        .duplicate_branch_edges => {
            blocks[fixture.b_entry.index()].terminator = .{ .branch = .{
                .condition = fixture.v_is_negative,
                .then_edge = .{ .target = fixture.b_join, .arguments = &.{fixture.v_zero} },
                .else_edge = .{ .target = fixture.b_join, .arguments = &.{fixture.v_zero} },
            } };
        },
        .unreachable_disagreement => {
            blocks[fixture.b_entry.index()].terminator = .{ .jump = .{ .target = fixture.b_nonnegative } };
            blocks[fixture.b_negative.index()].terminator.jump.arguments = &.{fixture.v_negated};
        },
        .proved_dead_edge => {
            instructions[fixture.i_is_negative.index()].operation = .{ .constant = .{ .boolean = false } };
            blocks[fixture.b_entry.index()].terminator = .{ .branch = .{
                .condition = fixture.v_is_negative,
                .then_edge = .{ .target = fixture.b_join, .arguments = &.{fixture.v_zero} },
                .else_edge = .{ .target = fixture.b_nonnegative },
            } };
            blocks[fixture.b_negative.index()].terminator = .{ .return_values = &.{fixture.v_negated} };
            blocks[fixture.b_nonnegative.index()].terminator = .{ .return_values = &.{fixture.v_input} };
        },
        .reachable_disagreement => {
            blocks[fixture.b_negative.index()].terminator.jump.arguments = &.{fixture.v_negated};
        },
        .positive => instructions[fixture.i_zero.index()].operation.constant.number = 1.0,
        .parameter => {
            blocks[fixture.b_negative.index()].terminator.jump.arguments = &.{fixture.v_input};
            blocks[fixture.b_nonnegative.index()].terminator.jump.arguments = &.{fixture.v_input};
        },
        .effectful => instructions[fixture.i_zero.index()].effects = .{ .precision = .exact, .may_throw = true },
        .nonfinite => instructions[fixture.i_zero.index()].operation = .{ .constant = .{ .special_number = .negative_infinity } },
    }

    var program = fixture.program;
    program.instructions = &instructions;
    program.blocks = &blocks;
    var raw_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer raw_report.deinit();
    try std.testing.expect(raw_report.contains(.unsupported_readable_error_location));

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    const expected_admission = kind == .shared_predecessors or kind == .duplicate_branch_edges or
        kind == .unreachable_disagreement or kind == .proved_dead_edge;
    // A solver-proved dead edge removes the error block from the admitted
    // program, so only the control-branch obligation remains in that case.
    const expected_obligation = (expected_admission and kind != .proved_dead_edge) or kind == .positive;
    const expected_unsupported_error = !expected_obligation and kind != .proved_dead_edge;
    try std.testing.expectEqual(expected_admission, outcome.isAdmitted());
    try std.testing.expectEqual(expected_admission, outcome.luau_source != null);
    try std.testing.expectEqual(expected_unsupported_error, outcome.report.contains(.unsupported_readable_error_location));
    try std.testing.expectEqual(kind == .positive, outcome.report.contains(.open_profile_obligation));

    const resolved = outcome.program().?;
    var error_obligation: ?ir.Obligation = null;
    for (resolved.obligations) |obligation| {
        if (obligation.kind == .numeric_domain and obligation.subject == .block and
            obligation.subject.block == fixture.b_join)
        {
            try std.testing.expect(error_obligation == null);
            error_obligation = obligation;
        }
    }
    try std.testing.expectEqual(expected_obligation, error_obligation != null);
    if (error_obligation) |obligation| {
        try std.testing.expectEqual(
            if (expected_admission) ir.ObligationStatus.discharged else .open,
            obligation.status,
        );
        const query = resolved.queries[obligation.query.?.index()];
        const comparison = resolved.solver_terms[query.goal.index()].operation.binary;
        const definition = resolved.solver_terms[comparison.left.index()].operation.value_definition;
        try std.testing.expectEqual(fixture.v_zero, definition.value);
        const certificate = resolved.certificates[obligation.certificate.?.index()];
        try std.testing.expectEqual(
            if (expected_admission) ir.SolverResolution.proved else .disproved,
            certificate.resolution,
        );
    }

    if (kind == .shared_predecessors) {
        const tampered_blocks = try std.testing.allocator.dupe(ir.Block, resolved.blocks);
        defer std.testing.allocator.free(tampered_blocks);
        tampered_blocks[fixture.b_negative.index()].terminator.jump.arguments = &.{fixture.v_negated};
        var tampered = resolved.*;
        tampered.blocks = tampered_blocks;
        var tampered_report = try validation.validate(std.testing.allocator, &tampered, .readable_luau);
        defer tampered_report.deinit();
        try std.testing.expect(tampered_report.contains(.unsupported_readable_error_location));
    }
    if (kind == .proved_dead_edge) {
        try std.testing.expectEqual(fixture.b_nonnegative, resolved.blocks[fixture.b_entry.index()].terminator.jump.target);
        try std.testing.expectEqual(@as(usize, 1), resolved.obligations.len);

        var core_report = try validation.validate(std.testing.allocator, resolved, .core);
        defer core_report.deinit();
        try std.testing.expect(core_report.isClean());

        const tampered_obligations = try std.testing.allocator.dupe(ir.Obligation, resolved.obligations);
        defer std.testing.allocator.free(tampered_obligations);
        var control_index: ?usize = null;
        for (tampered_obligations, 0..) |candidate, index| {
            if (candidate.subject != .control_branch) continue;
            control_index = index;
            break;
        }
        try std.testing.expect(control_index != null);
        tampered_obligations[control_index.?].subject.control_branch.branch.then_edge.arguments = &.{fixture.v_input};
        var tampered = resolved.*;
        tampered.obligations = tampered_obligations;
        var tampered_report = try validation.validate(std.testing.allocator, &tampered, .core);
        defer tampered_report.deinit();
        try std.testing.expect(tampered_report.contains(.certificate_digest_mismatch));
    }
}

test "pipeline authenticates shared reachable inputs for block-parameter error levels" {
    inline for (std.meta.tags(BlockParameterErrorLevelCase)) |kind| {
        try expectBlockParameterErrorLevel(kind);
    }
}

test "pipeline rejects sibling and cross-function error-level definitions before promotion" {
    const absolute = @import("fixtures.zig").absolute_value_module;
    var sibling_blocks = absolute.blocks;
    sibling_blocks[absolute.b_nonnegative.index()].terminator = .{ .throw_error = .{
        .value = absolute.v_input,
        .level = 0,
        .dynamic_level = absolute.v_negated,
    } };
    var sibling_program = absolute.program;
    sibling_program.blocks = &sibling_blocks;
    var sibling = try runAlloc(
        std.testing.allocator,
        &sibling_program,
        solver_backend.internalFacts(),
        .{ .profile = .core },
    );
    defer sibling.deinit();
    try std.testing.expect(!sibling.isAdmitted());
    try std.testing.expect(sibling.program() == null);
    try std.testing.expect(sibling.report.contains(.non_dominating_value_use));

    const arithmetic = @import("fixtures.zig").arithmetic_module;
    var cross_blocks = arithmetic.blocks;
    cross_blocks[arithmetic.b_add.index()].terminator = .{ .throw_error = .{
        .value = arithmetic.v_result,
        .level = 0,
        .dynamic_level = arithmetic.v_export,
    } };
    var cross_program = arithmetic.program;
    cross_program.blocks = &cross_blocks;
    var cross = try runAlloc(
        std.testing.allocator,
        &cross_program,
        solver_backend.internalFacts(),
        .{ .profile = .core },
    );
    defer cross.deinit();
    try std.testing.expect(!cross.isAdmitted());
    try std.testing.expect(cross.program() == null);
    try std.testing.expect(cross.report.contains(.cross_function_operand));
}

test "pipeline proves same-block nonpositive dynamic error levels" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "-1" } };
    var blocks = fixture.blocks;
    blocks[fixture.b_add.index()].terminator = .{ .throw_error = .{
        .value = fixture.v_result,
        .level = 0,
        .dynamic_level = fixture.v_factor,
    } };
    var program = fixture.program;
    program.instructions = &instructions;
    program.blocks = &blocks;

    var raw_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer raw_report.deinit();
    try std.testing.expect(raw_report.contains(.unsupported_readable_error_location));

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expect(outcome.luau_source != null);
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "__lifter_error") != null);

    const resolved = outcome.program().?;
    try std.testing.expectEqual(@as(usize, 1), resolved.queries.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.obligations.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.certificates.len);
    const obligation = resolved.obligations[0];
    try std.testing.expectEqual(ir.ObligationKind.numeric_domain, obligation.kind);
    try std.testing.expectEqual(fixture.b_add, obligation.subject.block);
    try std.testing.expectEqual(ir.ObligationStatus.discharged, obligation.status);
    try std.testing.expect(obligation.certificate != null);
    const query = resolved.queries[obligation.query.?.index()];
    try std.testing.expectEqual(ir.QueryKind.prove_true, query.kind);
    const comparison = resolved.solver_terms[query.goal.index()].operation.binary;
    try std.testing.expectEqual(ir.SolverBinaryOperator.less_equal, comparison.operator);

    const tampered_blocks = try std.testing.allocator.dupe(ir.Block, resolved.blocks);
    defer std.testing.allocator.free(tampered_blocks);
    tampered_blocks[fixture.b_add.index()].terminator.throw_error.dynamic_level = fixture.v_result;
    var tampered = resolved.*;
    tampered.blocks = tampered_blocks;
    var tampered_report = try validation.validate(std.testing.allocator, &tampered, .readable_luau);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.unsupported_readable_error_location));
    try std.testing.expect(tampered_report.contains(.certificate_digest_mismatch));
}

test "pipeline proves exact rounded binary number error levels" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var values = fixture.values;
    values[fixture.v_sum.index()].type = .number;
    values[fixture.v_factor.index()].type = .number;
    values[fixture.v_result.index()].type = .number;
    var instructions = fixture.instructions;
    instructions[fixture.i_sum.index()].operation = .{ .constant = .{ .number = -0.1 } };
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .number = 0.2 } };
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .subtract,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
    } };
    var blocks = fixture.blocks;
    blocks[fixture.b_add.index()].terminator = .{ .throw_error = .{
        .value = fixture.v_factor,
        .level = 0,
        .dynamic_level = fixture.v_result,
    } };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.blocks = &blocks;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expect(outcome.luau_source != null);

    const resolved = outcome.program().?;
    try std.testing.expectEqual(@as(usize, 1), resolved.queries.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.obligations.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.certificates.len);
    const obligation = resolved.obligations[0];
    try std.testing.expectEqual(ir.ObligationStatus.discharged, obligation.status);
    try std.testing.expectEqual(ir.SolverResolution.proved, resolved.certificates[obligation.certificate.?.index()].resolution);
    const comparison = resolved.solver_terms[resolved.queries[obligation.query.?.index()].goal.index()].operation.binary;
    const definition = resolved.solver_terms[comparison.left.index()];
    try std.testing.expectEqual(ir.SolverSortKind.real, definition.sort.kind);
    try std.testing.expectEqual(fixture.v_result, definition.operation.value_definition.value);
    const literal = resolved.solver_terms[definition.operation.value_definition.expression.index()].operation.real_literal;
    try std.testing.expectEqualStrings("-1351079888211149", literal.numerator);
    try std.testing.expectEqualStrings("4503599627370496", literal.denominator);

    const tampered_terms = try std.testing.allocator.dupe(ir.SolverTerm, resolved.solver_terms);
    defer std.testing.allocator.free(tampered_terms);
    tampered_terms[definition.operation.value_definition.expression.index()].operation = .{ .real_literal = .{
        .numerator = "-3",
        .denominator = "2",
    } };
    var tampered = resolved.*;
    tampered.solver_terms = tampered_terms;
    var tampered_report = try validation.validate(std.testing.allocator, &tampered, .readable_luau);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.invalid_solver_value_definition));
    try std.testing.expect(tampered_report.contains(.certificate_digest_mismatch));
    var tampered_replay = try runAlloc(
        std.testing.allocator,
        &tampered,
        solver_backend.internalFacts(),
        .{ .profile = .core },
    );
    defer tampered_replay.deinit();
    try std.testing.expect(!tampered_replay.isAdmitted());
    try std.testing.expect(tampered_replay.program() == null);
    try std.testing.expect(tampered_replay.report.contains(.invalid_solver_value_definition));

    instructions[fixture.i_sum.index()].operation.constant.number = 0.5;
    var positive_outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer positive_outcome.deinit();
    try std.testing.expect(!positive_outcome.isAdmitted());
    try std.testing.expect(positive_outcome.report.contains(.open_profile_obligation));
    try std.testing.expect(!positive_outcome.report.contains(.unsupported_readable_error_location));
    const positive = positive_outcome.program().?;
    try std.testing.expectEqual(@as(usize, 1), positive.certificates.len);
    try std.testing.expectEqual(ir.SolverResolution.disproved, positive.certificates[0].resolution);
}

test "pipeline blocks positive dynamic error levels with disproved certificates" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "1" } };
    var blocks = fixture.blocks;
    blocks[fixture.b_add.index()].terminator = .{ .throw_error = .{
        .value = fixture.v_result,
        .level = 0,
        .dynamic_level = fixture.v_factor,
    } };
    var program = fixture.program;
    program.instructions = &instructions;
    program.blocks = &blocks;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(!outcome.isAdmitted());
    try std.testing.expect(outcome.program() != null);
    try std.testing.expect(outcome.luau_source == null);
    try std.testing.expect(outcome.report.contains(.open_profile_obligation));
    try std.testing.expect(!outcome.report.contains(.unsupported_readable_error_location));

    const resolved = outcome.program().?;
    try std.testing.expectEqual(@as(usize, 1), resolved.queries.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.obligations.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.certificates.len);
    const obligation = resolved.obligations[0];
    try std.testing.expectEqual(ir.ObligationKind.numeric_domain, obligation.kind);
    try std.testing.expectEqual(fixture.b_add, obligation.subject.block);
    try std.testing.expectEqual(ir.ObligationStatus.open, obligation.status);
    try std.testing.expect(obligation.certificate != null);
    try std.testing.expectEqual(
        ir.SolverResolution.disproved,
        resolved.certificates[obligation.certificate.?.index()].resolution,
    );
}

test "pipeline leaves unresolved nonpositive error levels as typed obligations" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_factor.index()].operation = .{ .binary = .{
        .operator = .add,
        .left = fixture.v_left,
        .right = fixture.v_right,
    } };
    var blocks = fixture.blocks;
    blocks[fixture.b_add.index()].terminator = .{ .throw_error = .{
        .value = fixture.v_result,
        .level = 0,
        .dynamic_level = fixture.v_factor,
    } };
    var program = fixture.program;
    program.instructions = &instructions;
    program.blocks = &blocks;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(!outcome.isAdmitted());
    try std.testing.expect(outcome.program() != null);
    try std.testing.expect(outcome.luau_source == null);
    try std.testing.expect(outcome.report.contains(.open_profile_obligation));
    try std.testing.expect(outcome.report.contains(.solver_unknown));
    try std.testing.expect(!outcome.report.contains(.unsupported_readable_error_location));
    try std.testing.expectEqual(@as(usize, 1), outcome.program().?.obligations.len);
    try std.testing.expectEqual(ir.ObligationStatus.open, outcome.program().?.obligations[0].status);
    try std.testing.expect(outcome.program().?.obligations[0].certificate == null);
}

test "pipeline does not plan error-level proofs for unreachable blocks" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const live_block = ir.BlockId.fromIndex(fixture.blocks.len);
    var instructions = fixture.instructions;
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "-1" } };
    var blocks = fixture.blocks ++ [_]ir.Block{.{
        .id = live_block,
        .function = fixture.f_add,
        .terminator = .{ .return_values = &.{fixture.v_left} },
        .evidence = &.{fixture.proof},
    }};
    blocks[fixture.b_add.index()].terminator = .{ .throw_error = .{
        .value = fixture.v_result,
        .level = 0,
        .dynamic_level = fixture.v_factor,
    } };
    const function_blocks = [_]ir.BlockId{ live_block, fixture.b_add };
    var functions = fixture.functions;
    functions[fixture.f_add.index()].blocks = &function_blocks;
    functions[fixture.f_add.index()].entry_block = live_block;
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expectEqual(@as(usize, 0), outcome.program().?.obligations.len);
    try std.testing.expectEqual(@as(usize, 0), outcome.program().?.queries.len);
    try std.testing.expectEqual(@as(usize, 0), outcome.program().?.certificates.len);
}

test "pipeline rewrites a solver-proved branch before Luau structuring" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_is_negative.index()].operation = .{ .constant = .{ .boolean = true } };
    var program = fixture.program;
    program.instructions = &instructions;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expectEqual(@as(usize, 1), outcome.program().?.solver_terms.len);
    try std.testing.expectEqual(@as(usize, 1), outcome.program().?.queries.len);
    try std.testing.expectEqual(@as(usize, 1), outcome.program().?.obligations.len);
    try std.testing.expectEqual(ir.ObligationStatus.discharged, outcome.program().?.obligations[0].status);
    try std.testing.expect(outcome.program().?.blocks[fixture.b_entry.index()].terminator == .jump);
    const goal = outcome.program().?.solver_terms[outcome.program().?.queries[0].goal.index()];
    // The exact-branch prepass proves the condition through its value ID;
    // constant resolution comes from the IR definition, not a duplicate term.
    try std.testing.expect(goal.operation == .value);
    try std.testing.expectEqual(fixture.v_is_negative, goal.operation.value);
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "if ") == null);
    const certificate_id = outcome.program().?.obligations[0].certificate.?;
    try std.testing.expectEqualSlices(ir.EvidenceId, &.{fixture.proof}, outcome.program().?.certificates[certificate_id.index()].evidence);

    var tampered_instructions = instructions;
    tampered_instructions[fixture.i_is_negative.index()].operation = .{ .constant = .{ .boolean = false } };
    var tampered = outcome.program().?.*;
    tampered.instructions = &tampered_instructions;
    var tampered_report = try validation.validate(std.testing.allocator, &tampered, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.certificate_digest_mismatch));
}

test "pipeline replays edge-anchored scopes after authenticated branch selection" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_is_negative.index()].operation = .{ .constant = .{ .boolean = true } };
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const constraints = [_]ir.Constraint{
        .{
            .id = ir.ConstraintId.fromIndex(0),
            .predicate = ir.SolverTermId.fromIndex(0),
            .evidence = &.{fixture.proof},
            .scope = .{ .edge = .{
                .source = fixture.b_entry,
                .kind = .branch_then,
                .target = fixture.b_negative,
            } },
        },
        .{
            .id = ir.ConstraintId.fromIndex(1),
            .predicate = ir.SolverTermId.fromIndex(0),
            .evidence = &.{fixture.proof},
            .scope = .{ .edge = .{
                .source = fixture.b_entry,
                .kind = .branch_else,
                .target = fixture.b_nonnegative,
            } },
        },
    };
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    var first = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer first.deinit();
    try std.testing.expect(first.isAdmitted());
    const first_program = first.program().?;
    try std.testing.expectEqual(fixture.b_negative, first_program.blocks[fixture.b_entry.index()].terminator.jump.target);
    try std.testing.expectEqual(
        fixture.b_negative,
        @import("edge_path.zig").constraintEffectiveTarget(first_program, first_program.constraints[0]).?,
    );
    try std.testing.expectEqual(
        fixture.b_nonnegative,
        @import("edge_path.zig").constraintEffectiveTarget(first_program, first_program.constraints[1]).?,
    );

    var second = try runAlloc(
        std.testing.allocator,
        first_program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer second.deinit();
    try std.testing.expect(second.isAdmitted());
    const second_program = second.program().?;
    try std.testing.expectEqual(fixture.b_negative, second_program.blocks[fixture.b_entry.index()].terminator.jump.target);
    var branch_obligations: usize = 0;
    for (second_program.obligations) |obligation| switch (obligation.subject) {
        .control_branch => |subject| branch_obligations += @intFromBool(subject.block == fixture.b_entry),
        else => {},
    };
    try std.testing.expectEqual(@as(usize, 1), branch_obligations);

    var unwitnessed = second_program.*;
    unwitnessed.obligations = &.{};
    var unwitnessed_report = try validation.validate(std.testing.allocator, &unwitnessed, .core);
    defer unwitnessed_report.deinit();
    try std.testing.expect(unwitnessed_report.contains(.invalid_constraint_scope));
    try std.testing.expect(unwitnessed_report.contains(.certificate_digest_mismatch));
}

test "pipeline proves exact predicates before deriving branch arm facts" {
    const fixture = @import("fixtures.zig").automatic_promotion_module;
    try std.testing.expectEqual(@as(usize, 0), fixture.program.solver_terms.len);

    var outcome = try runAlloc(
        std.testing.allocator,
        &fixture.program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    const resolved = outcome.program().?;
    try std.testing.expectEqual(@as(usize, 1), resolved.solver_terms.len);
    try std.testing.expectEqual(@as(usize, 0), resolved.constraints.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.queries.len);
    try std.testing.expectEqual(@as(usize, 0), resolved.queries[0].assumptions.len);
    try std.testing.expectEqual(@as(usize, 1), resolved.obligations.len);
    try std.testing.expectEqual(ir.ObligationStatus.discharged, resolved.obligations[0].status);
    try std.testing.expectEqual(@as(usize, 1), resolved.certificates.len);
    const goal = resolved.queries[0].goal;
    switch (resolved.solver_terms[goal.index()].operation) {
        .value => |value| try std.testing.expectEqual(fixture.v_condition, value),
        .value_definition => |definition| {
            try std.testing.expectEqual(fixture.v_condition, definition.value);
            switch (resolved.solver_terms[definition.expression.index()].operation) {
                .boolean_literal => |value| try std.testing.expect(value),
                else => return error.TestUnexpectedResult,
            }
        },
        else => return error.TestUnexpectedResult,
    }
    try std.testing.expectEqual(ir.SolverResolution.proved, @import("solver.zig").solve(resolved, resolved.queries[0]));
    const certificate_id = resolved.obligations[0].certificate orelse return error.TestUnexpectedResult;
    const certificate = resolved.certificates[certificate_id.index()];
    try std.testing.expectEqual(ir.SolverEngine.internal_facts, certificate.engine);
    try std.testing.expectEqual(ir.SolverResolution.proved, certificate.resolution);
    const rewritten = resolved.blocks[fixture.b_entry.index()].terminator;
    try std.testing.expect(rewritten == .jump);
    try std.testing.expectEqual(fixture.b_matched, rewritten.jump.target);
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "if ") == null);
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "bit32.band") == null);
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "unreachable") == null);
}

test "pipeline rejects a mismatched claim before query promotion" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_result } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = false } },
    };
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(1),
    }};
    const claims = [_]ir.Claim{.{
        .id = ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = ir.SolverTermId.fromIndex(2),
        .status = .unproven,
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .core },
    );
    defer outcome.deinit();
    try std.testing.expect(!outcome.isAdmitted());
    try std.testing.expect(outcome.program() == null);
    try std.testing.expect(outcome.report.contains(.invalid_claim_query_reference));
    try std.testing.expectEqual(queries[0].goal, program.queries[0].goal);
    try std.testing.expectEqual(claims[0].predicate, program.claims[0].predicate);
}

test "query promotion resolves an obligation-only model consumer" {
    const fixture = @import("fixtures.zig").arithmetic_module;
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
        .detail = "find an exact model for the normalized result identity",
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.obligations = &obligations;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    const resolved = outcome.program().?;
    try std.testing.expect(resolved.queries[0].goal != queries[0].goal);
    try std.testing.expectEqual(ir.ObligationStatus.discharged, resolved.obligations[0].status);
    try std.testing.expectEqual(@as(usize, 1), resolved.solver_models.len);
    try std.testing.expectEqual(ir.QueryId.fromIndex(0), resolved.solver_models[0].query);
    const certificate = resolved.certificates[resolved.obligations[0].certificate.?.index()];
    try std.testing.expectEqual(ir.SolverEngine.internal_facts, certificate.engine);
    try std.testing.expectEqual(ir.SolverResolution.proved, certificate.resolution);
    try std.testing.expectEqual(resolved.solver_models[0].id, certificate.model.?);
    try std.testing.expect(certificate.unsat_core == null);
}

test "pipeline reports contradictory imported Boolean proofs" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = fixture.v_is_negative },
    }};
    const queries = [_]ir.SolverQuery{
        .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(0) },
        .{ .id = ir.QueryId.fromIndex(1), .kind = .prove_false, .goal = ir.SolverTermId.fromIndex(0) },
    };
    const certificates = [_]ir.SolverCertificate{
        .{
            .id = ir.CertificateId.fromIndex(0),
            .query = ir.QueryId.fromIndex(0),
            .engine = .imported,
            .resolution = .proved,
            .evidence = &.{fixture.proof},
            .certificate_digest = "fixture:true-proof",
        },
        .{
            .id = ir.CertificateId.fromIndex(1),
            .query = ir.QueryId.fromIndex(1),
            .engine = .imported,
            .resolution = .proved,
            .evidence = &.{fixture.proof},
            .certificate_digest = "fixture:false-proof",
        },
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.certificates = &certificates;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .core },
    );
    defer outcome.deinit();
    try std.testing.expect(!outcome.isAdmitted());
    try std.testing.expect(outcome.report.contains(.contradictory_solver_proof));
}

test "scoped frontend facts automatically drive nonconstant branch proofs" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = fixture.v_is_negative },
    }};
    var constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{fixture.proof},
        .scope = .{ .block = fixture.b_entry },
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expectEqual(@as(usize, 2), outcome.program().?.queries.len);
    try std.testing.expectEqual(@as(usize, 2), outcome.program().?.claims.len);
    try std.testing.expectEqual(ir.ClaimStatus.proved, outcome.program().?.claims[0].status);
    try std.testing.expectEqual(ir.ClaimStatus.unproven, outcome.program().?.claims[1].status);
    try std.testing.expectEqual(fixture.b_negative, outcome.program().?.blocks[fixture.b_entry.index()].terminator.jump.target);
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "if ") == null);

    constraints[0].evidence = &.{};
    var invalid = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .core },
    );
    defer invalid.deinit();
    try std.testing.expect(!invalid.isAdmitted());
    try std.testing.expect(invalid.program() == null);
    try std.testing.expect(invalid.report.contains(.scoped_constraint_without_evidence));
}

test "inconsistent scoped branch facts cannot select an arbitrary edge" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    const terms = [_]ir.SolverTerm{
        .{
            .id = ir.SolverTermId.fromIndex(0),
            .sort = .{ .kind = .boolean },
            .operation = .{ .value = fixture.v_is_negative },
        },
        .{
            .id = ir.SolverTermId.fromIndex(1),
            .sort = .{ .kind = .boolean },
            .operation = .{ .logical_not = ir.SolverTermId.fromIndex(0) },
        },
    };
    const constraints = [_]ir.Constraint{
        .{
            .id = ir.ConstraintId.fromIndex(0),
            .predicate = ir.SolverTermId.fromIndex(0),
            .evidence = &.{fixture.proof},
            .scope = .{ .block = fixture.b_entry },
        },
        .{
            .id = ir.ConstraintId.fromIndex(1),
            .predicate = ir.SolverTermId.fromIndex(1),
            .evidence = &.{fixture.proof},
            .scope = .{ .block = fixture.b_entry },
        },
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(!outcome.isAdmitted());
    try std.testing.expect(outcome.report.contains(.contradictory_solver_proof));
    try std.testing.expect(outcome.luau_source == null);
}

test "readable blockers inside a proved dead region do not escape its scope" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_is_negative.index()].operation = .{ .constant = .{ .boolean = false } };
    instructions[fixture.i_negate.index()].operation.unary.operator = .bit_not;
    instructions[fixture.i_negate.index()].effects = .{};
    instructions[fixture.i_negate.index()].evidence = &.{};
    var values = fixture.values;
    values[fixture.v_negated.index()].type = .integer;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = fixture.v_is_negative },
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_false,
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    const obligations = [_]ir.Obligation{
        .{
            .id = ir.ObligationId.fromIndex(0),
            .kind = .control_structure,
            .subject = .{ .block = fixture.b_entry },
            .status = .open,
            .blocks_profile = .readable_luau,
            .detail = "prove the live branch",
            .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
            .query = ir.QueryId.fromIndex(0),
        },
        .{
            .id = ir.ObligationId.fromIndex(1),
            .kind = .target_support,
            .subject = .{ .instruction = fixture.i_negate },
            .status = .open,
            .blocks_profile = .readable_luau,
            .detail = "dead target operation is intentionally unsupported",
        },
    };
    var program = fixture.program;
    program.instructions = &instructions;
    program.values = &values;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.obligations = &obligations;

    var before = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer before.deinit();
    try std.testing.expect(before.contains(.unsupported_readable_bit_operation));
    try std.testing.expect(before.contains(.open_profile_obligation));
    try std.testing.expect(before.contains(.missing_emission_evidence));

    var outcome = try runAlloc(
        std.testing.allocator,
        &program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer outcome.deinit();
    try std.testing.expect(outcome.isAdmitted());
    try std.testing.expectEqual(ir.ObligationStatus.open, outcome.program().?.obligations[1].status);
    try std.testing.expect(!outcome.report.contains(.unsupported_readable_bit_operation));
    try std.testing.expect(!outcome.report.contains(.open_profile_obligation));
    try std.testing.expect(!outcome.report.contains(.missing_emission_evidence));
    try std.testing.expect(std.mem.indexOf(u8, outcome.luau_source.?, "bit32") == null);

    var core_obligations = obligations;
    core_obligations[1].blocks_profile = .core;
    var core_blocked_program = program;
    core_blocked_program.obligations = &core_obligations;
    var core_blocked = try runAlloc(
        std.testing.allocator,
        &core_blocked_program,
        solver_backend.internalFacts(),
        .{ .profile = .readable_luau, .emit_luau = .standard_luau },
    );
    defer core_blocked.deinit();
    try std.testing.expect(!core_blocked.isAdmitted());
    try std.testing.expect(core_blocked.report.contains(.open_profile_obligation));
}
