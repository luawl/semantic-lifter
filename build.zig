const std = @import("std");

fn luneExe(b: *std.Build) []const u8 {
    return b.pathFromRoot("../../../../lune.exe");
}

fn luauCompileExe(b: *std.Build) []const u8 {
    return b.pathFromRoot("../../../../tools/bin/luau-compile.exe");
}

fn addStructureAstAudit(
    b: *std.Build,
    fixture_name: []const u8,
    generated_luau: std.Build.LazyPath,
) *std.Build.Step.Run {
    const command = b.addSystemCommand(&.{ luneExe(b), "run" });
    command.addFileArg(b.path("luau/structure_ast_audit.luau"));
    command.addFileInput(b.path("luau/structure_ast_audit.luau"));
    command.addFileArg(b.path("../../../../tools/luau-0.720/luau-ast.exe"));
    command.addArg(fixture_name);
    command.addFileArg(generated_luau);
    return command;
}

fn luauAnalyzeExe(b: *std.Build) []const u8 {
    return b.pathFromRoot("../../../../tools/bin/luau-analyze.exe");
}

fn addRegisterBudgetOracle(b: *std.Build) *std.Build.Step.Run {
    const command = b.addSystemCommand(&.{ luneExe(b), "run" });
    command.addFileArg(b.path("luau/register_budget_oracle.luau"));
    command.addFileArg(b.path("../../../../tools/bin/luau-compile.exe"));
    _ = command.addOutputFileArg("register-budget-oracle.txt");
    const cases = [_][]const u8{
        "local-200",
        "local-201",
        "invocation-254",
        "invocation-256",
        "table-255",
        "table-257",
        "interpolation-255",
        "interpolation-257",
        "reordered-return-255",
        "reordered-return-257",
        "expanded-return-254",
        "expanded-return-256",
        "stored-expanded-return-254",
        "stored-expanded-return-256",
        "reentrant-stored-expanded-return-local-200",
        "reentrant-stored-expanded-return-local-202",
        "stored-adjustment-local-200",
        "stored-adjustment-local-201",
        "fixed-return-254",
        "fixed-return-255",
        "fixed-results-254",
        "fixed-results-255",
        "expression-depth-998",
        "expression-depth-999",
        "syntax-depth-998",
        "syntax-depth-999",
        "combined-depth-512",
        "combined-depth-640",
        "upvalue-200",
        "upvalue-201",
        "closure-32768",
        "closure-32769",
        "jump-distance-8388604",
        "jump-distance-8388611",
        "constant-loadkx-32768",
    };
    for (cases) |case_name| {
        _ = command.addOutputFileArg(b.fmt("register-budget-{s}.luau", .{case_name}));
    }
    return command;
}

const FixtureConformance = struct {
    validate: *std.Build.Step,
    compile: *std.Build.Step,
    runtime: *std.Build.Step,
    source_compile: ?*std.Build.Step = null,
    source_runtime: ?*std.Build.Step = null,
    input_ir: std.Build.LazyPath,
    resolved_ir: std.Build.LazyPath,
    generated_luau: std.Build.LazyPath,

    fn addTo(self: FixtureConformance, step: *std.Build.Step) void {
        step.dependOn(self.validate);
        step.dependOn(self.compile);
        step.dependOn(self.runtime);
        if (self.source_compile) |source_compile| step.dependOn(source_compile);
        if (self.source_runtime) |source_runtime| step.dependOn(source_runtime);
    }
};

const CompileOnlyConformance = struct {
    validate: *std.Build.Step,
    compile: *std.Build.Step,
    lexical: ?*std.Build.Step = null,
    resolved_ir: std.Build.LazyPath,
    generated_luau: std.Build.LazyPath,

    fn addTo(self: CompileOnlyConformance, step: *std.Build.Step) void {
        step.dependOn(self.validate);
        step.dependOn(self.compile);
        if (self.lexical) |lexical| step.dependOn(lexical);
    }
};

const RecoveryObligationConformance = struct {
    core_validate: *std.Build.Step,
    readable_rejection: *std.Build.Step,
    census: *std.Build.Step,

    fn addTo(self: RecoveryObligationConformance, step: *std.Build.Step) void {
        step.dependOn(self.core_validate);
        step.dependOn(self.readable_rejection);
        step.dependOn(self.census);
    }
};

const BlockerCensusRow = struct {
    kind: []const u8,
    subject: []const u8,
    operation: []const u8,
    producer: []const u8,
    value_type: []const u8,
    place_flow: []const u8,
    proof_links: []const u8,
    count: usize,
};

fn addZigFixtureConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    fixture_name: []const u8,
) FixtureConformance {
    const fixture_command = b.addRunArtifact(exe);
    if (z3_enabled) fixture_command.addPathDir(b.pathFromRoot(z3_bin));
    fixture_command.addArgs(&.{ "fixture-json", fixture_name });
    const fixture_json = fixture_command.addOutputFileArg(b.fmt("{s}.lifter-ir.json", .{fixture_name}));

    return addSerializedConformance(b, exe, z3_enabled, z3_bin, fixture_name, fixture_json);
}

fn addLuauFixtureConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    script_path: []const u8,
    fixture_name: []const u8,
) FixtureConformance {
    return addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        script_path,
        fixture_name,
        if (z3_enabled) "z3" else "internal",
    );
}

fn addLuauFixtureConformanceWithEngine(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    script_path: []const u8,
    fixture_name: []const u8,
    engine_name: []const u8,
) FixtureConformance {
    const fixture_command = b.addSystemCommand(&.{ luneExe(b), "run" });
    fixture_command.addFileArg(b.path(script_path));
    fixture_command.addFileInput(b.path("luau/lifter_ir.luau"));
    fixture_command.addFileInput(b.path("luau/json_codec.luau"));
    const fixture_json = fixture_command.addOutputFileArg(b.fmt("{s}.lifter-ir.json", .{fixture_name}));

    return addSerializedConformanceWithEngine(b, exe, z3_enabled, z3_bin, fixture_name, fixture_json, engine_name);
}

fn addLuauSourceConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    source_path: []const u8,
    fixture_name: []const u8,
) FixtureConformance {
    const fixture_json = addLuauSourceIr(b, source_path, null, fixture_name);
    var result = addSerializedConformance(b, exe, z3_enabled, z3_bin, fixture_name, fixture_json);
    result.source_compile = addSourceCompileConformance(b, source_path);
    result.source_runtime = addSourceRuntimeConformance(b, source_path, fixture_name, result.generated_luau);
    return result;
}

fn addLuauSourceManifestConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    source_path: []const u8,
    manifest_path: []const u8,
    fixture_name: []const u8,
) FixtureConformance {
    const fixture_json = addLuauSourceIr(b, source_path, manifest_path, fixture_name);
    var result = addSerializedConformance(b, exe, z3_enabled, z3_bin, fixture_name, fixture_json);
    result.source_compile = addSourceCompileConformance(b, source_path);
    result.source_runtime = addSourceRuntimeConformance(b, source_path, fixture_name, result.generated_luau);
    return result;
}

fn addLuauSourceManifestProofConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    proof_attest: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    source_path: []const u8,
    manifest_path: []const u8,
    proof_bundle_path: []const u8,
    trusted_public_key: []const u8,
    fixture_name: []const u8,
) FixtureConformance {
    const fixture_json = addLuauSourceIrConfigured(b, source_path, manifest_path, fixture_name, .{
        .verifier = proof_attest,
        .path = proof_bundle_path,
        .trusted_public_key = trusted_public_key,
    });
    var result = addSerializedConformance(b, exe, z3_enabled, z3_bin, fixture_name, fixture_json);
    result.source_compile = addSourceCompileConformance(b, source_path);
    result.source_runtime = addSourceRuntimeConformance(b, source_path, fixture_name, result.generated_luau);
    return result;
}

fn addSourceCompileConformance(b: *std.Build, source_path: []const u8) *std.Build.Step {
    const compile_command = b.addSystemCommand(&.{ luauCompileExe(b), "--null" });
    compile_command.addFileArg(b.path(source_path));
    return &compile_command.step;
}

fn addSourceRuntimeConformance(
    b: *std.Build,
    source_path: []const u8,
    fixture_name: []const u8,
    generated_luau: std.Build.LazyPath,
) *std.Build.Step {
    const runtime_command = b.addSystemCommand(&.{ luneExe(b), "run" });
    runtime_command.addFileArg(b.path("luau/runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/source_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/pack_multi_latch_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/pack_return_storage_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/iteration_exit_transfer_runtime_oracle.luau"));
    runtime_command.addArg(fixture_name);
    runtime_command.addFileArg(b.path(source_path));
    runtime_command.addFileArg(generated_luau);
    runtime_command.step.dependOn(addGeneratedLexicalConformance(b, source_path, generated_luau));
    return &runtime_command.step;
}

fn addGeneratedLexicalConformance(
    b: *std.Build,
    source_path: []const u8,
    generated_luau: std.Build.LazyPath,
) *std.Build.Step {
    const command = b.addSystemCommand(&.{ luneExe(b), "run" });
    command.addFileArg(b.path("luau/generated_lexical_oracle.luau"));
    command.addArg("check");
    command.addFileArg(b.path("../../../../tools/bin/luau-analyze.exe"));
    command.addFileArg(b.path(source_path));
    command.addFileArg(generated_luau);
    return &command.step;
}

fn addLuauSourceCompileConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    source_path: []const u8,
    fixture_name: []const u8,
    engine_name: []const u8,
) CompileOnlyConformance {
    const fixture_json = addLuauSourceIr(b, source_path, null, fixture_name);
    var result = addSerializedCompileConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        fixture_name,
        fixture_json,
        engine_name,
    );
    result.lexical = addGeneratedLexicalConformance(b, source_path, result.generated_luau);
    return result;
}

fn addLuauSourceRecoveryObligationConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    source_path: []const u8,
    manifest_path: []const u8,
    fixture_name: []const u8,
    engine_name: []const u8,
    expected_total: usize,
    expected_rows: []const BlockerCensusRow,
) RecoveryObligationConformance {
    const fixture_json = addLuauSourceIr(b, source_path, manifest_path, fixture_name);

    const resolve_command = b.addRunArtifact(exe);
    if (z3_enabled) resolve_command.addPathDir(b.pathFromRoot(z3_bin));
    resolve_command.addArg("resolve-ir");
    resolve_command.addFileArg(fixture_json);
    const resolved_json = resolve_command.addOutputFileArg(b.fmt("{s}.resolved.lifter-ir.json", .{fixture_name}));
    resolve_command.addArg(engine_name);

    const core_validate = b.addRunArtifact(exe);
    if (z3_enabled) core_validate.addPathDir(b.pathFromRoot(z3_bin));
    core_validate.addArg("validate");
    core_validate.addFileArg(resolved_json);
    core_validate.addArg("core");

    const readable_rejection = b.addRunArtifact(exe);
    if (z3_enabled) readable_rejection.addPathDir(b.pathFromRoot(z3_bin));
    readable_rejection.addArg("expect-diagnostic");
    readable_rejection.addFileArg(resolved_json);
    readable_rejection.addArgs(&.{ "readable-luau", "open_profile_obligation" });

    const census = b.addRunArtifact(exe);
    if (z3_enabled) census.addPathDir(b.pathFromRoot(z3_bin));
    census.addArg("expect-blocker-proof-census");
    census.addFileArg(resolved_json);
    census.addArg("readable-luau");
    census.addArg(b.fmt("{d}", .{expected_total}));
    for (expected_rows) |row| {
        census.addArgs(&.{ row.kind, row.subject, row.operation, row.producer, row.value_type, row.place_flow, row.proof_links, b.fmt("{d}", .{row.count}) });
    }

    return .{
        .core_validate = &core_validate.step,
        .readable_rejection = &readable_rejection.step,
        .census = &census.step,
    };
}

fn addLuauSourceIr(
    b: *std.Build,
    source_path: []const u8,
    manifest_path: ?[]const u8,
    fixture_name: []const u8,
) std.Build.LazyPath {
    return addLuauSourceIrConfigured(b, source_path, manifest_path, fixture_name, null);
}

const ProofBundleConfig = struct {
    verifier: *std.Build.Step.Compile,
    path: []const u8,
    trusted_public_key: []const u8,
};

fn addLuauSourceIrConfigured(
    b: *std.Build,
    source_path: []const u8,
    manifest_path: ?[]const u8,
    fixture_name: []const u8,
    proof_bundle: ?ProofBundleConfig,
) std.Build.LazyPath {
    const frontend_command = b.addSystemCommand(&.{ luneExe(b), "run" });
    frontend_command.addFileArg(b.path("luau/lift_source.luau"));
    frontend_command.addFileInput(b.path("luau/ast_frontend.luau"));
    frontend_command.addFileInput(b.path("luau/ast_local_binding.luau"));
    frontend_command.addFileInput(b.path("luau/ast_local_identity.luau"));
    frontend_command.addFileInput(b.path("luau/ast_lexical_scope.luau"));
    frontend_command.addFileInput(b.path("luau/ast_runtime_context.luau"));
    frontend_command.addFileInput(b.path("luau/ast_expression_slots.luau"));
    frontend_command.addFileInput(b.path("luau/ast_expression_scalar.luau"));
    frontend_command.addFileInput(b.path("luau/ast_statement_slots.luau"));
    frontend_command.addFileInput(b.path("luau/ast_admission.luau"));
    frontend_command.addFileInput(b.path("luau/ast_target_recovery.luau"));
    frontend_command.addFileInput(b.path("luau/ast_frontend_outcome.luau"));
    frontend_command.addFileInput(b.path("luau/ast_frontend_expressions.luau"));
    frontend_command.addFileInput(b.path("luau/ast_frontend_tables.luau"));
    frontend_command.addFileInput(b.path("luau/ast_frontend_operator_domains.luau"));
    frontend_command.addFileInput(b.path("luau/ast_frontend_place_domains.luau"));
    frontend_command.addFileInput(b.path("luau/ast_frontend_control.luau"));
    frontend_command.addFileInput(b.path("luau/ast_frontend_iteration.luau"));
    frontend_command.addFileInput(b.path("luau/intrinsic_bindings.luau"));
    frontend_command.addFileInput(b.path("luau/recovery_admission.luau"));
    frontend_command.addFileInput(b.path("luau/lifter_ir.luau"));
    frontend_command.addFileInput(b.path("luau/json_codec.luau"));
    frontend_command.addFileInput(b.path("luau/recovery_manifest.luau"));
    addTemporalIdentityInputs(b, frontend_command);
    frontend_command.addFileInput(b.path("luau/target_recovery.luau"));
    frontend_command.addFileInput(b.path("luau/target_result_contracts.luau"));
    frontend_command.addFileInput(b.path("luau/target_proof_bundle.luau"));
    frontend_command.addFileArg(b.path("../../../../tools/luau-0.720/luau-ast.exe"));
    frontend_command.addFileArg(b.path(source_path));
    frontend_command.addArg(fixture_name);
    const fixture_json = frontend_command.addOutputFileArg(b.fmt("{s}.lifter-ir.json", .{fixture_name}));
    frontend_command.addArg(fixture_name);
    if (manifest_path) |path| frontend_command.addFileArg(b.path(path));
    if (proof_bundle) |bundle| {
        frontend_command.addFileArg(b.path(bundle.path));
        frontend_command.addArtifactArg(bundle.verifier);
        frontend_command.addArg(bundle.trusted_public_key);
    }
    return fixture_json;
}

fn addSerializedConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    fixture_name: []const u8,
    fixture_json: std.Build.LazyPath,
) FixtureConformance {
    return addSerializedConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        fixture_name,
        fixture_json,
        if (z3_enabled) "z3" else "internal",
    );
}

fn addSerializedConformanceWithEngine(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    fixture_name: []const u8,
    fixture_json: std.Build.LazyPath,
    engine_name: []const u8,
) FixtureConformance {
    const resolve_command = b.addRunArtifact(exe);
    if (z3_enabled) resolve_command.addPathDir(b.pathFromRoot(z3_bin));
    resolve_command.addArg("resolve-ir");
    resolve_command.addFileArg(fixture_json);
    const resolved_json = resolve_command.addOutputFileArg(b.fmt("{s}.resolved.lifter-ir.json", .{fixture_name}));
    resolve_command.addArg(engine_name);

    const validate_command = b.addRunArtifact(exe);
    if (z3_enabled) validate_command.addPathDir(b.pathFromRoot(z3_bin));
    validate_command.addArg("validate");
    validate_command.addFileArg(resolved_json);
    validate_command.addArg("readable-luau");

    const emit_command = b.addRunArtifact(exe);
    if (z3_enabled) emit_command.addPathDir(b.pathFromRoot(z3_bin));
    emit_command.addArg("emit-luau-solved");
    emit_command.addFileArg(resolved_json);
    const emitted_luau = emit_command.addOutputFileArg(b.fmt("{s}.generated.luau", .{fixture_name}));
    emit_command.addArg(engine_name);
    emit_command.addArg("standard-luau");
    emit_command.addFileArg(b.path("../../../../tools/bin/luau-compile.exe"));

    const runtime_command = b.addSystemCommand(&.{ luneExe(b), "run" });
    runtime_command.addFileArg(b.path("luau/runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/source_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/pack_multi_latch_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/pack_return_storage_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/iteration_exit_transfer_runtime_oracle.luau"));
    runtime_command.addArg(fixture_name);
    runtime_command.addFileArg(emitted_luau);

    return .{
        .validate = &validate_command.step,
        .compile = &emit_command.step,
        .runtime = &runtime_command.step,
        .input_ir = fixture_json,
        .resolved_ir = resolved_json,
        .generated_luau = emitted_luau,
    };
}

fn addSerializedCompileConformanceWithEngine(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    fixture_name: []const u8,
    fixture_json: std.Build.LazyPath,
    engine_name: []const u8,
) CompileOnlyConformance {
    const resolve_command = b.addRunArtifact(exe);
    if (z3_enabled) resolve_command.addPathDir(b.pathFromRoot(z3_bin));
    resolve_command.addArg("resolve-ir");
    resolve_command.addFileArg(fixture_json);
    const resolved_json = resolve_command.addOutputFileArg(b.fmt("{s}.resolved.lifter-ir.json", .{fixture_name}));
    resolve_command.addArg(engine_name);

    const validate_command = b.addRunArtifact(exe);
    if (z3_enabled) validate_command.addPathDir(b.pathFromRoot(z3_bin));
    validate_command.addArg("validate");
    validate_command.addFileArg(resolved_json);
    validate_command.addArg("readable-luau");

    const emit_command = b.addRunArtifact(exe);
    if (z3_enabled) emit_command.addPathDir(b.pathFromRoot(z3_bin));
    emit_command.addArg("emit-luau-solved");
    emit_command.addFileArg(resolved_json);
    const emitted_luau = emit_command.addOutputFileArg(b.fmt("{s}.generated.luau", .{fixture_name}));
    emit_command.addArg(engine_name);
    emit_command.addArg("standard-luau");
    emit_command.addFileArg(b.path("../../../../tools/bin/luau-compile.exe"));

    return .{
        .validate = &validate_command.step,
        .compile = &emit_command.step,
        .resolved_ir = resolved_json,
        .generated_luau = emitted_luau,
    };
}

fn addTemporalIdentityInputs(b: *std.Build, command: *std.Build.Step.Run) void {
    command.addFileInput(b.path("luau/ast_expression_scalar.luau"));
    command.addFileInput(b.path("luau/ast_expression_slots.luau"));
    command.addFileInput(b.path("luau/target_origin_expression_matcher.luau"));
    command.addFileInput(b.path("luau/target_origin_return_selector.luau"));
    command.addFileInput(b.path("luau/target_origin_matcher.luau"));
    command.addFileInput(b.path("luau/structured_definition_sets.luau"));
    command.addFileInput(b.path("luau/temporal_alias_graph.luau"));
    command.addFileInput(b.path("luau/temporal_callee_resolver.luau"));
    command.addFileInput(b.path("luau/temporal_invocation_flow.luau"));
    command.addFileInput(b.path("luau/temporal_source_index.luau"));
    command.addFileInput(b.path("luau/temporal_target_identity.luau"));
}

fn addTemporalTestInputs(b: *std.Build, command: *std.Build.Step.Run) void {
    addTemporalIdentityInputs(b, command);
    command.addFileInput(b.path("luau/temporal_test_support.luau"));
    command.addFileInput(b.path("luau/temporal_invocation_test_support.luau"));
}

fn addStandaloneTests(
    b: *std.Build,
    module: *std.Build.Module,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    z3_enabled: bool,
    z3_bin: []const u8,
    source_path: []const u8,
) *std.Build.Step.Run {
    const tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path(source_path),
            .target = target,
            .optimize = optimize,
            .imports = &.{.{ .name = "semantic_lifter", .module = module }},
        }),
    });
    const run_tests = b.addRunArtifact(tests);
    if (z3_enabled) run_tests.addPathDir(b.pathFromRoot(z3_bin));
    return run_tests;
}
