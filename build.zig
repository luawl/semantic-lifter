const std = @import("std");

// External tools (the Lune runtime, the Luau 0.720 tools and Node) are resolved once at the top of
// build() from the -Dlune / -Dluau-compile / -Dluau-ast / -Dluau-analyze / -Dnode options and cached here,
// so a clone that passes the options (or has the tools on PATH) can build and test. This machine's
// workspace paths are never hard-coded; see resolveExternalTool.
var resolved_lune: []const u8 = "";
var resolved_luau_compile: []const u8 = "";
var resolved_luau_ast: []const u8 = "";
var resolved_luau_analyze: []const u8 = "";
var resolved_node: []const u8 = "";

fn failMissingTool(name: []const u8) noreturn {
    std.debug.print(
        "semantic-lifter: external tool {s} not found; pass -D{s}=<path> (needs Lune 0.10.4, the Luau 0.720 tools and Node 24)\n",
        .{ name, name },
    );
    std.process.exit(1);
}

fn resolveExternalTool(b: *std.Build, option_value: ?[]const u8, name: []const u8) []const u8 {
    if (option_value) |value| {
        const resolved = if (std.fs.path.isAbsolute(value)) value else b.pathFromRoot(value);
        std.Io.Dir.cwd().access(b.graph.io, resolved, .{}) catch failMissingTool(name);
        return resolved;
    }
    return b.findProgram(&.{name}, &.{}) catch failMissingTool(name);
}

const z3_dir_hint = "pass -Dz3-dir=<path> (an unpacked Z3 4.16.0 release with include/z3.h, bin/libz3.lib and bin/libz3.dll)";

fn failMissingZ3(comptime detail: []const u8, args: anytype) noreturn {
    std.debug.print("semantic-lifter: " ++ detail ++ "; " ++ z3_dir_hint ++ "\n", args);
    std.process.exit(1);
}

// -Dz3=true needs -Dz3-dir, and the three files the build consumes must exist, checked at configure time
// like the external tools. The value is returned as given (absolute, or relative to the build root);
// every use resolves it with b.pathFromRoot, as the addPathDir(b.pathFromRoot(z3_bin)) sites do.
fn checkZ3Dir(b: *std.Build, option_value: ?[]const u8) []const u8 {
    const value = option_value orelse failMissingZ3("-Dz3=true needs the Z3 C API", .{});
    for ([_][]const u8{ "include/z3.h", "bin/libz3.lib", "bin/libz3.dll" }) |entry| {
        const file = b.pathFromRoot(b.pathJoin(&.{ value, entry }));
        std.Io.Dir.cwd().access(b.graph.io, file, .{}) catch failMissingZ3("Z3 file {s} not found", .{file});
    }
    return value;
}

fn luneExe(b: *std.Build) []const u8 {
    _ = b;
    return resolved_lune;
}

fn luauCompileExe(b: *std.Build) []const u8 {
    _ = b;
    return resolved_luau_compile;
}

fn luauAstExe(b: *std.Build) []const u8 {
    _ = b;
    return resolved_luau_ast;
}

fn addStructureAstAudit(
    b: *std.Build,
    fixture_name: []const u8,
    generated_luau: std.Build.LazyPath,
) *std.Build.Step.Run {
    const command = b.addSystemCommand(&.{ luneExe(b), "run" });
    command.addFileArg(b.path("luau/structure_ast_audit.luau"));
    command.addFileInput(b.path("luau/structure_ast_audit.luau"));
    command.addFileArg(.{ .cwd_relative = luauAstExe(b) });
    command.addArg(fixture_name);
    command.addFileArg(generated_luau);
    return command;
}

fn luauAnalyzeExe(b: *std.Build) []const u8 {
    _ = b;
    return resolved_luau_analyze;
}

fn nodeExe(b: *std.Build) []const u8 {
    _ = b;
    return resolved_node;
}

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const z3_enabled = b.option(bool, "z3", "Enable the direct Z3 C API backend") orelse false;
    const z3_dir_option = b.option([]const u8, "z3-dir", "Path to an unpacked Z3 4.16.0 release (include/z3.h, bin/libz3.lib, bin/libz3.dll); required with -Dz3=true");
    const install_proof_attest = b.option(
        bool,
        "install-proof-attest",
        "Install the proof-attestation helper with the semantic-lifter executable",
    ) orelse true;
    const trace_normalize_phases = b.option(
        bool,
        "trace-normalize-phases",
        "Enable bounded phase timing diagnostics for control normalization",
    ) orelse false;

    const lune_option = b.option([]const u8, "lune", "Path to the Lune 0.10.4 runtime (default: lune on PATH)");
    const luau_compile_option = b.option([]const u8, "luau-compile", "Path to luau-compile from the Luau 0.720 tools (default: luau-compile on PATH)");
    const luau_ast_option = b.option([]const u8, "luau-ast", "Path to luau-ast from the Luau 0.720 tools (default: luau-ast on PATH)");
    const luau_analyze_option = b.option([]const u8, "luau-analyze", "Path to luau-analyze from the Luau 0.720 tools (default: luau-analyze on PATH)");
    const node_option = b.option([]const u8, "node", "Path to the Node 24 runtime, which runs the compiler-disassembly adapter tests (default: node on PATH)");
    resolved_lune = resolveExternalTool(b, lune_option, "lune");
    resolved_luau_compile = resolveExternalTool(b, luau_compile_option, "luau-compile");
    resolved_luau_ast = resolveExternalTool(b, luau_ast_option, "luau-ast");
    resolved_luau_analyze = resolveExternalTool(b, luau_analyze_option, "luau-analyze");
    resolved_node = resolveExternalTool(b, node_option, "node");

    const z3_dir = if (z3_enabled) checkZ3Dir(b, z3_dir_option) else "";
    const z3_include = b.pathJoin(&.{ z3_dir, "include" });
    const z3_library = b.pathJoin(&.{ z3_dir, "bin", "libz3.lib" });
    const z3_bin = b.pathJoin(&.{ z3_dir, "bin" });

    const build_options = b.addOptions();
    build_options.addOption(bool, "z3_enabled", z3_enabled);
    build_options.addOption(bool, "trace_normalize_phases", trace_normalize_phases);

    const module = b.addModule("semantic_lifter", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
    });
    module.addOptions("build_options", build_options);
    if (z3_enabled) {
        module.link_libc = true; // z3.h includes <stdio.h>, so the C import needs the libc headers
        module.addIncludePath(.{ .cwd_relative = b.pathFromRoot(z3_include) });
        module.addObjectFile(.{ .cwd_relative = b.pathFromRoot(z3_library) });
    }

    const exe = b.addExecutable(.{
        .name = "semantic-lifter",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{.{ .name = "semantic_lifter", .module = module }},
        }),
    });
    // Readable validation and emission walk nested regions recursively, and a Debug build's frames are several times
    // a release build's: on the default 16 MiB main-thread stack a Debug build overflowed on a chain of about 150
    // nested transfer wrappers. 128 MiB covers more than twice the nesting the syntax-depth budget admits in every
    // build mode; the module tests, which validate such chains, get the same stack.
    const main_thread_stack_size = 128 * 1024 * 1024;
    exe.stack_size = main_thread_stack_size;
    b.installArtifact(exe);

    const proof_attest = b.addExecutable(.{
        .name = "proof-attest",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/proof_attest.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    if (install_proof_attest) b.installArtifact(proof_attest);

    const run_command = b.addRunArtifact(exe);
    if (z3_enabled) run_command.addPathDir(b.pathFromRoot(z3_bin));
    run_command.step.dependOn(b.getInstallStep());
    if (b.args) |args| run_command.addArgs(args);
    const run_step = b.step("run", "Run the semantic lifter CLI");
    run_step.dependOn(&run_command.step);

    const absolute_conformance = addZigFixtureConformance(b, exe, z3_enabled, z3_bin, "absolute");
    const function_reference_conformance = addZigFixtureConformance(b, exe, z3_enabled, z3_bin, "function-reference-identity");
    const dynamic_truthiness_conformance = addZigFixtureConformance(b, exe, z3_enabled, z3_bin, "dynamic-truthiness");
    const immutable_closure_conformance = addZigFixtureConformance(b, exe, z3_enabled, z3_bin, "immutable-closure");
    const shared_place_conformance = addZigFixtureConformance(b, exe, z3_enabled, z3_bin, "shared-place-closure");
    const luau_control_conformance = addLuauFixtureConformance(b, exe, z3_enabled, z3_bin, "luau/conformance.luau", "choose-max");
    const luau_loop_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/loop_conformance.luau",
        "loop-control-topologies",
        if (z3_enabled) "z3" else "internal",
    );
    const loop_reresolve = b.addRunArtifact(exe);
    if (z3_enabled) loop_reresolve.addPathDir(b.pathFromRoot(z3_bin));
    loop_reresolve.addArg("resolve-ir");
    loop_reresolve.addFileArg(luau_loop_conformance.resolved_ir);
    const loop_reresolved_ir = loop_reresolve.addOutputFileArg("loop-control-topologies.reresolved.lifter-ir.json");
    loop_reresolve.addArg(if (z3_enabled) "z3" else "internal");
    const loop_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    loop_audit.addFileArg(b.path("luau/loop_conformance.luau"));
    loop_audit.addFileInput(b.path("luau/lifter_ir.luau"));
    loop_audit.addFileInput(b.path("luau/json_codec.luau"));
    loop_audit.addArg("audit");
    loop_audit.addFileArg(luau_loop_conformance.resolved_ir);
    loop_audit.addFileArg(loop_reresolved_ir);
    loop_audit.addArg(if (z3_enabled) "z3" else "internal");
    const luau_numeric_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/numeric_conformance.luau",
        "u32-numerics",
        if (z3_enabled) "z3" else "internal",
    );
    const luau_promotion_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/promotion_conformance.luau",
        "automatic-promotion",
        if (z3_enabled) "z3" else "internal",
    );
    const luau_guarded_promotion_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/guarded_promotion_conformance.luau",
        "guarded-promotion",
        if (z3_enabled) "z3" else "internal",
    );
    const guarded_promotion_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    guarded_promotion_audit.addFileArg(b.path("luau/guarded_promotion_conformance.luau"));
    guarded_promotion_audit.addFileInput(b.path("luau/lifter_ir.luau"));
    guarded_promotion_audit.addFileInput(b.path("luau/json_codec.luau"));
    guarded_promotion_audit.addArg("audit");
    guarded_promotion_audit.addFileArg(luau_guarded_promotion_conformance.resolved_ir);
    guarded_promotion_audit.addFileArg(luau_guarded_promotion_conformance.generated_luau);
    guarded_promotion_audit.addArg(if (z3_enabled) "z3" else "internal_facts");
    const luau_query_promotion_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/query_promotion_conformance.luau",
        "query-promotion",
        if (z3_enabled) "z3" else "internal",
    );
    const query_promotion_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    query_promotion_audit.addFileArg(b.path("luau/query_promotion_conformance.luau"));
    query_promotion_audit.addFileInput(b.path("luau/lifter_ir.luau"));
    query_promotion_audit.addFileInput(b.path("luau/json_codec.luau"));
    query_promotion_audit.addArg("audit");
    query_promotion_audit.addFileArg(luau_query_promotion_conformance.input_ir);
    query_promotion_audit.addFileArg(luau_query_promotion_conformance.resolved_ir);
    const query_promotion_reresolve = b.addRunArtifact(exe);
    if (z3_enabled) query_promotion_reresolve.addPathDir(b.pathFromRoot(z3_bin));
    query_promotion_reresolve.addArg("resolve-ir");
    query_promotion_reresolve.addFileArg(luau_query_promotion_conformance.resolved_ir);
    const query_promotion_reresolved_ir = query_promotion_reresolve.addOutputFileArg("query-promotion.reresolved.lifter-ir.json");
    query_promotion_reresolve.addArg(if (z3_enabled) "z3" else "internal");
    query_promotion_audit.addFileArg(query_promotion_reresolved_ir);
    query_promotion_audit.addFileArg(luau_query_promotion_conformance.generated_luau);
    query_promotion_audit.addArg(if (z3_enabled) "z3" else "internal_facts");
    const luau_closure_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/closure_conformance.luau",
        "luau-shared-place-closure",
        if (z3_enabled) "z3" else "internal",
    );
    const luau_lexical_transfer_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/lexical_transfer_conformance.luau",
        "loop-local-lexical-transfer",
    );
    const luau_entry_parameter_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/entry_parameter_conformance.luau",
        "fixed-entry-parameters",
    );
    const luau_expression_depth_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/expression_depth_conformance.luau",
        "bounded-expression-depth",
    );
    const luau_structured_depth_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/structured_depth_conformance.luau",
        "structured-parser-depth",
    );
    const luau_mixed_entry_vararg_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/mixed_entry_vararg_conformance.luau",
        "mixed-entry-varargs",
    );
    const luau_pack_materialization_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/pack_materialization_conformance.luau",
        "pack-materialized-adjustment",
    );
    const luau_pack_multi_latch_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/pack_multi_latch_conformance.luau",
        "pack-multi-latch",
    );
    const luau_pack_return_storage_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/pack_return_storage_conformance.luau",
        "pack-return-storage",
    );
    const luau_iteration_exit_transfer_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/iteration_exit_transfer_conformance.luau",
        "iteration-exit-transfer",
    );
    const luau_iteration_break_exit_transfer_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/iteration_break_exit_transfer_conformance.luau",
        "iteration-break-exit-transfer",
    );
    const luau_iteration_escape_join_exit_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/iteration_escape_join_exit_conformance.luau",
        "iteration-escape-join-exit",
    );
    const luau_iteration_dominating_break_exit_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/iteration_dominating_break_exit_conformance.luau",
        "iteration-dominating-break-exit",
    );
    const iteration_break_exit_transfer_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "iteration-break-exit-transfer",
        luau_iteration_break_exit_transfer_conformance.resolved_ir,
    );
    const iteration_escape_join_exit_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "iteration-escape-join-exit",
        luau_iteration_escape_join_exit_conformance.resolved_ir,
    );
    const iteration_dominating_break_exit_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "iteration-dominating-break-exit",
        luau_iteration_dominating_break_exit_conformance.resolved_ir,
    );
    const luau_iteration_header_entry_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/iteration_header_entry_conformance.luau",
        "iteration-header-entry",
    );
    const luau_iteration_continue_completion_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/iteration_continue_completion_conformance.luau",
        "iteration-continue-completion",
    );
    const luau_iteration_boundary_body_continue_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/iteration_boundary_body_continue_conformance.luau",
        "iteration-boundary-body-continue",
    );
    const iteration_header_entry_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "iteration-header-entry",
        luau_iteration_header_entry_conformance.resolved_ir,
    );
    const iteration_continue_completion_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "iteration-continue-completion",
        luau_iteration_continue_completion_conformance.resolved_ir,
    );
    const iteration_boundary_body_continue_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "iteration-boundary-body-continue",
        luau_iteration_boundary_body_continue_conformance.resolved_ir,
    );
    const source_frontend_wrapped_local_continue_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/wrapped_local_continue_source.luau",
        "source-frontend-wrapped-local-continue",
    );
    const wrapped_local_continue_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-wrapped-local-continue",
        source_frontend_wrapped_local_continue_conformance.resolved_ir,
    );
    const luau_wrapped_continue_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/wrapped_continue_conformance.luau",
        "wrapped-continue",
    );
    const wrapped_continue_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "wrapped-continue",
        luau_wrapped_continue_conformance.resolved_ir,
    );
    const wrapped_local_continue_layout = b.addSystemCommand(&.{ luneExe(b), "run" });
    wrapped_local_continue_layout.addFileArg(b.path("luau/structured_layout_oracle.luau"));
    wrapped_local_continue_layout.addArg("source-frontend-wrapped-local-continue");
    wrapped_local_continue_layout.addFileArg(source_frontend_wrapped_local_continue_conformance.generated_luau);
    const wrapped_continue_layout = b.addSystemCommand(&.{ luneExe(b), "run" });
    wrapped_continue_layout.addFileArg(b.path("luau/structured_layout_oracle.luau"));
    wrapped_continue_layout.addArg("wrapped-continue");
    wrapped_continue_layout.addFileArg(luau_wrapped_continue_conformance.generated_luau);
    const luau_loop_owned_exit_flag_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/loop_owned_exit_flag_conformance.luau",
        "loop-owned-exit-flag",
    );
    const loop_owned_exit_flag_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "loop-owned-exit-flag",
        luau_loop_owned_exit_flag_conformance.resolved_ir,
    );
    const source_frontend_loop_exit_flag_reentry_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/loop_exit_flag_reentry_source.luau",
        "source-frontend-loop-exit-flag-reentry",
    );
    const source_frontend_loop_exit_flag_reentry_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/loop_exit_flag_reentry_source.luau",
        "source-frontend-loop-exit-flag-reentry-direct-locals",
        "direct-locals-luau",
    );
    const loop_exit_flag_reentry_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-loop-exit-flag-reentry",
        source_frontend_loop_exit_flag_reentry_conformance.resolved_ir,
    );
    const source_frontend_loop_exit_flag_reentry_mid_pass_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/loop_exit_flag_reentry_mid_pass_source.luau",
        "source-frontend-loop-exit-flag-reentry-mid-pass",
    );
    const source_frontend_loop_exit_flag_reentry_mid_pass_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/loop_exit_flag_reentry_mid_pass_source.luau",
        "source-frontend-loop-exit-flag-reentry-mid-pass-direct-locals",
        "direct-locals-luau",
    );
    const loop_exit_flag_reentry_mid_pass_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-loop-exit-flag-reentry-mid-pass",
        source_frontend_loop_exit_flag_reentry_mid_pass_conformance.resolved_ir,
    );
    const loop_exit_flag_reentry_layout = b.addSystemCommand(&.{ luneExe(b), "run" });
    loop_exit_flag_reentry_layout.addFileArg(b.path("luau/structured_layout_oracle.luau"));
    loop_exit_flag_reentry_layout.addArg("source-frontend-loop-exit-flag-reentry");
    loop_exit_flag_reentry_layout.addFileArg(source_frontend_loop_exit_flag_reentry_conformance.generated_luau);
    const loop_exit_flag_reentry_mid_pass_layout = b.addSystemCommand(&.{ luneExe(b), "run" });
    loop_exit_flag_reentry_mid_pass_layout.addFileArg(b.path("luau/structured_layout_oracle.luau"));
    loop_exit_flag_reentry_mid_pass_layout.addArg("source-frontend-loop-exit-flag-reentry-mid-pass");
    loop_exit_flag_reentry_mid_pass_layout.addFileArg(source_frontend_loop_exit_flag_reentry_mid_pass_conformance.generated_luau);
    const source_frontend_nested_continue_side_exit_generic_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/nested_continue_side_exit_generic_source.luau",
        "source-frontend-nested-continue-side-exit-generic",
    );
    const nested_continue_side_exit_generic_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-nested-continue-side-exit-generic",
        source_frontend_nested_continue_side_exit_generic_conformance.resolved_ir,
    );
    const source_frontend_nested_continue_side_exit_while_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/nested_continue_side_exit_while_source.luau",
        "source-frontend-nested-continue-side-exit-while",
    );
    const nested_continue_side_exit_while_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-nested-continue-side-exit-while",
        source_frontend_nested_continue_side_exit_while_conformance.resolved_ir,
    );
    const source_frontend_nested_continue_side_exit_numeric_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/nested_continue_side_exit_numeric_source.luau",
        "source-frontend-nested-continue-side-exit-numeric",
    );
    const nested_continue_side_exit_numeric_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-nested-continue-side-exit-numeric",
        source_frontend_nested_continue_side_exit_numeric_conformance.resolved_ir,
    );
    const source_frontend_nested_continue_side_exit_elseif_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/nested_continue_side_exit_elseif_source.luau",
        "source-frontend-nested-continue-side-exit-elseif",
    );
    const nested_continue_side_exit_elseif_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-nested-continue-side-exit-elseif",
        source_frontend_nested_continue_side_exit_elseif_conformance.resolved_ir,
    );
    const source_frontend_nested_continue_side_exit_nested_break_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/nested_continue_side_exit_nested_break_source.luau",
        "source-frontend-nested-continue-side-exit-nested-break",
    );
    const nested_continue_side_exit_nested_break_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-nested-continue-side-exit-nested-break",
        source_frontend_nested_continue_side_exit_nested_break_conformance.resolved_ir,
    );
    const nested_continue_side_exit_generic_layout = b.addSystemCommand(&.{ luneExe(b), "run" });
    nested_continue_side_exit_generic_layout.addFileArg(b.path("luau/structured_layout_oracle.luau"));
    nested_continue_side_exit_generic_layout.addArg("source-frontend-nested-continue-side-exit-generic");
    nested_continue_side_exit_generic_layout.addFileArg(source_frontend_nested_continue_side_exit_generic_conformance.generated_luau);
    const nested_continue_side_exit_while_layout = b.addSystemCommand(&.{ luneExe(b), "run" });
    nested_continue_side_exit_while_layout.addFileArg(b.path("luau/structured_layout_oracle.luau"));
    nested_continue_side_exit_while_layout.addArg("source-frontend-nested-continue-side-exit-while");
    nested_continue_side_exit_while_layout.addFileArg(source_frontend_nested_continue_side_exit_while_conformance.generated_luau);
    const nested_continue_side_exit_numeric_layout = b.addSystemCommand(&.{ luneExe(b), "run" });
    nested_continue_side_exit_numeric_layout.addFileArg(b.path("luau/structured_layout_oracle.luau"));
    nested_continue_side_exit_numeric_layout.addArg("source-frontend-nested-continue-side-exit-numeric");
    nested_continue_side_exit_numeric_layout.addFileArg(source_frontend_nested_continue_side_exit_numeric_conformance.generated_luau);
    const nested_continue_side_exit_elseif_layout = b.addSystemCommand(&.{ luneExe(b), "run" });
    nested_continue_side_exit_elseif_layout.addFileArg(b.path("luau/structured_layout_oracle.luau"));
    nested_continue_side_exit_elseif_layout.addArg("source-frontend-nested-continue-side-exit-elseif");
    nested_continue_side_exit_elseif_layout.addFileArg(source_frontend_nested_continue_side_exit_elseif_conformance.generated_luau);
    const nested_continue_side_exit_nested_break_layout = b.addSystemCommand(&.{ luneExe(b), "run" });
    nested_continue_side_exit_nested_break_layout.addFileArg(b.path("luau/structured_layout_oracle.luau"));
    nested_continue_side_exit_nested_break_layout.addArg("source-frontend-nested-continue-side-exit-nested-break");
    nested_continue_side_exit_nested_break_layout.addFileArg(source_frontend_nested_continue_side_exit_nested_break_conformance.generated_luau);
    const luau_iteration_header_forwarder_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/iteration_header_forwarder_conformance.luau",
        "iteration-header-forwarder",
    );
    const iteration_header_forwarder_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "iteration-header-forwarder",
        luau_iteration_header_forwarder_conformance.resolved_ir,
    );
    const luau_open_pack_projection_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/open_pack_projection_conformance.luau",
        "open-pack-projection",
    );
    const luau_closed_pack_discard_conformance = addLuauFixtureConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/closed_pack_discard_conformance.luau",
        "closed-pack-discard",
    );
    const luau_table_conformance = addLuauFixtureConformance(b, exe, z3_enabled, z3_bin, "luau/table_conformance.luau", "table-access-modes");
    const luau_boundary_conformance = addLuauFixtureConformance(b, exe, z3_enabled, z3_bin, "luau/control_boundary_conformance.luau", "control-boundaries");
    const luau_path_control_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/path_control_conformance.luau",
        "edge-scoped-control",
        if (z3_enabled) "z3" else "internal",
    );
    const path_control_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    path_control_audit.addFileArg(b.path("luau/path_control_conformance.luau"));
    path_control_audit.addFileInput(b.path("luau/lifter_ir.luau"));
    path_control_audit.addFileInput(b.path("luau/json_codec.luau"));
    path_control_audit.addArg("audit");
    path_control_audit.addFileArg(luau_path_control_conformance.resolved_ir);
    const path_control_reresolve = b.addRunArtifact(exe);
    if (z3_enabled) path_control_reresolve.addPathDir(b.pathFromRoot(z3_bin));
    path_control_reresolve.addArg("resolve-ir");
    path_control_reresolve.addFileArg(luau_path_control_conformance.resolved_ir);
    const path_control_reresolved_ir = path_control_reresolve.addOutputFileArg("edge-scoped-control.reresolved.lifter-ir.json");
    path_control_reresolve.addArg(if (z3_enabled) "z3" else "internal");
    path_control_audit.addFileArg(path_control_reresolved_ir);
    path_control_audit.addArg(if (z3_enabled) "z3" else "internal");
    const luau_relational_path_control_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/relational_path_control_conformance.luau",
        "relational-edge-control",
        if (z3_enabled) "z3" else "internal",
    );
    const relational_path_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    relational_path_audit.addFileArg(b.path("luau/relational_path_control_conformance.luau"));
    relational_path_audit.addFileInput(b.path("luau/lifter_ir.luau"));
    relational_path_audit.addFileInput(b.path("luau/json_codec.luau"));
    relational_path_audit.addArg("audit");
    relational_path_audit.addFileArg(luau_relational_path_control_conformance.resolved_ir);
    relational_path_audit.addArg(if (z3_enabled) "z3" else "internal");
    const luau_chained_path_control_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/chained_path_control_conformance.luau",
        "chained-edge-control",
        if (z3_enabled) "z3" else "internal",
    );
    const chained_path_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    chained_path_audit.addFileArg(b.path("luau/chained_path_control_conformance.luau"));
    chained_path_audit.addFileInput(b.path("luau/lifter_ir.luau"));
    chained_path_audit.addFileInput(b.path("luau/json_codec.luau"));
    chained_path_audit.addArg("audit");
    chained_path_audit.addFileArg(luau_chained_path_control_conformance.resolved_ir);
    const chained_path_reresolve = b.addRunArtifact(exe);
    if (z3_enabled) chained_path_reresolve.addPathDir(b.pathFromRoot(z3_bin));
    chained_path_reresolve.addArg("resolve-ir");
    chained_path_reresolve.addFileArg(luau_chained_path_control_conformance.resolved_ir);
    const chained_path_reresolved_ir = chained_path_reresolve.addOutputFileArg("chained-edge-control.reresolved.lifter-ir.json");
    chained_path_reresolve.addArg(if (z3_enabled) "z3" else "internal");
    chained_path_audit.addFileArg(chained_path_reresolved_ir);
    const luau_irreducible_control_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/irreducible_control_conformance.luau",
        "finite-irreducible-control",
        if (z3_enabled) "z3" else "internal",
    );
    const irreducible_control_structure_ast = addStructureAstAudit(
        b,
        "finite-irreducible-control",
        luau_irreducible_control_conformance.generated_luau,
    );
    const irreducible_control_reresolve = b.addRunArtifact(exe);
    if (z3_enabled) irreducible_control_reresolve.addPathDir(b.pathFromRoot(z3_bin));
    irreducible_control_reresolve.addArg("resolve-ir");
    irreducible_control_reresolve.addFileArg(luau_irreducible_control_conformance.resolved_ir);
    const irreducible_control_reresolved_ir = irreducible_control_reresolve.addOutputFileArg("finite-irreducible-control.reresolved.lifter-ir.json");
    irreducible_control_reresolve.addArg(if (z3_enabled) "z3" else "internal");
    const irreducible_control_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    irreducible_control_audit.addFileArg(b.path("luau/irreducible_control_conformance.luau"));
    irreducible_control_audit.addFileInput(b.path("luau/irreducible_control_audit.luau"));
    irreducible_control_audit.addFileInput(b.path("luau/lifter_ir.luau"));
    irreducible_control_audit.addFileInput(b.path("luau/json_codec.luau"));
    irreducible_control_audit.addArg("audit");
    irreducible_control_audit.addFileArg(luau_irreducible_control_conformance.input_ir);
    irreducible_control_audit.addFileArg(luau_irreducible_control_conformance.resolved_ir);
    irreducible_control_audit.addFileArg(irreducible_control_reresolved_ir);
    irreducible_control_audit.addFileArg(luau_irreducible_control_conformance.generated_luau);
    const luau_irreducible_coroutine_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/irreducible_coroutine_conformance.luau",
        "irreducible-coroutine-control",
        if (z3_enabled) "z3" else "internal",
    );
    const irreducible_coroutine_structure_ast = addStructureAstAudit(
        b,
        "irreducible-coroutine-control",
        luau_irreducible_coroutine_conformance.generated_luau,
    );
    const irreducible_coroutine_reresolve = b.addRunArtifact(exe);
    if (z3_enabled) irreducible_coroutine_reresolve.addPathDir(b.pathFromRoot(z3_bin));
    irreducible_coroutine_reresolve.addArg("resolve-ir");
    irreducible_coroutine_reresolve.addFileArg(luau_irreducible_coroutine_conformance.resolved_ir);
    const irreducible_coroutine_reresolved_ir = irreducible_coroutine_reresolve.addOutputFileArg("irreducible-coroutine-control.reresolved.lifter-ir.json");
    irreducible_coroutine_reresolve.addArg(if (z3_enabled) "z3" else "internal");
    const irreducible_coroutine_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    irreducible_coroutine_audit.addFileArg(b.path("luau/irreducible_coroutine_conformance.luau"));
    irreducible_coroutine_audit.addFileInput(b.path("luau/irreducible_coroutine_audit.luau"));
    irreducible_coroutine_audit.addFileInput(b.path("luau/lifter_ir.luau"));
    irreducible_coroutine_audit.addFileInput(b.path("luau/json_codec.luau"));
    irreducible_coroutine_audit.addArg("audit");
    irreducible_coroutine_audit.addFileArg(luau_irreducible_coroutine_conformance.input_ir);
    irreducible_coroutine_audit.addFileArg(luau_irreducible_coroutine_conformance.resolved_ir);
    irreducible_coroutine_audit.addFileArg(irreducible_coroutine_reresolved_ir);
    irreducible_coroutine_audit.addFileArg(luau_irreducible_coroutine_conformance.generated_luau);
    const luau_irreducible_table_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/irreducible_table_conformance.luau",
        "irreducible-table-construction",
        if (z3_enabled) "z3" else "internal",
    );
    const irreducible_table_structure_ast = addStructureAstAudit(
        b,
        "irreducible-table-construction",
        luau_irreducible_table_conformance.generated_luau,
    );
    const irreducible_table_reresolve = b.addRunArtifact(exe);
    if (z3_enabled) irreducible_table_reresolve.addPathDir(b.pathFromRoot(z3_bin));
    irreducible_table_reresolve.addArg("resolve-ir");
    irreducible_table_reresolve.addFileArg(luau_irreducible_table_conformance.resolved_ir);
    const irreducible_table_reresolved_ir = irreducible_table_reresolve.addOutputFileArg("irreducible-table-construction.reresolved.lifter-ir.json");
    irreducible_table_reresolve.addArg(if (z3_enabled) "z3" else "internal");
    const irreducible_table_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    irreducible_table_audit.addFileArg(b.path("luau/irreducible_table_conformance.luau"));
    irreducible_table_audit.addFileInput(b.path("luau/irreducible_table_audit.luau"));
    irreducible_table_audit.addFileInput(b.path("luau/lifter_ir.luau"));
    irreducible_table_audit.addFileInput(b.path("luau/json_codec.luau"));
    irreducible_table_audit.addArg("audit");
    irreducible_table_audit.addFileArg(luau_irreducible_table_conformance.input_ir);
    irreducible_table_audit.addFileArg(luau_irreducible_table_conformance.resolved_ir);
    irreducible_table_audit.addFileArg(irreducible_table_reresolved_ir);
    irreducible_table_audit.addFileArg(luau_irreducible_table_conformance.generated_luau);
    const luau_irreducible_interpolation_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/irreducible_interpolation_conformance.luau",
        "irreducible-string-interpolation",
        if (z3_enabled) "z3" else "internal",
    );
    const irreducible_interpolation_structure_ast = addStructureAstAudit(
        b,
        "irreducible-string-interpolation",
        luau_irreducible_interpolation_conformance.generated_luau,
    );
    const irreducible_interpolation_reresolve = b.addRunArtifact(exe);
    if (z3_enabled) irreducible_interpolation_reresolve.addPathDir(b.pathFromRoot(z3_bin));
    irreducible_interpolation_reresolve.addArg("resolve-ir");
    irreducible_interpolation_reresolve.addFileArg(luau_irreducible_interpolation_conformance.resolved_ir);
    const irreducible_interpolation_reresolved_ir = irreducible_interpolation_reresolve.addOutputFileArg("irreducible-string-interpolation.reresolved.lifter-ir.json");
    irreducible_interpolation_reresolve.addArg(if (z3_enabled) "z3" else "internal");
    const irreducible_interpolation_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    irreducible_interpolation_audit.addFileArg(b.path("luau/irreducible_interpolation_conformance.luau"));
    irreducible_interpolation_audit.addFileInput(b.path("luau/irreducible_interpolation_audit.luau"));
    irreducible_interpolation_audit.addFileInput(b.path("luau/lifter_ir.luau"));
    irreducible_interpolation_audit.addFileInput(b.path("luau/json_codec.luau"));
    irreducible_interpolation_audit.addArg("audit");
    irreducible_interpolation_audit.addFileArg(luau_irreducible_interpolation_conformance.input_ir);
    irreducible_interpolation_audit.addFileArg(luau_irreducible_interpolation_conformance.resolved_ir);
    irreducible_interpolation_audit.addFileArg(irreducible_interpolation_reresolved_ir);
    irreducible_interpolation_audit.addFileArg(luau_irreducible_interpolation_conformance.generated_luau);
    const luau_irreducible_closure_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/irreducible_closure_conformance.luau",
        "irreducible-closure-captures",
        if (z3_enabled) "z3" else "internal",
    );
    const irreducible_closure_structure_ast = addStructureAstAudit(
        b,
        "irreducible-closure-captures",
        luau_irreducible_closure_conformance.generated_luau,
    );
    const irreducible_closure_reresolve = b.addRunArtifact(exe);
    if (z3_enabled) irreducible_closure_reresolve.addPathDir(b.pathFromRoot(z3_bin));
    irreducible_closure_reresolve.addArg("resolve-ir");
    irreducible_closure_reresolve.addFileArg(luau_irreducible_closure_conformance.resolved_ir);
    const irreducible_closure_reresolved_ir = irreducible_closure_reresolve.addOutputFileArg("irreducible-closure-captures.reresolved.lifter-ir.json");
    irreducible_closure_reresolve.addArg(if (z3_enabled) "z3" else "internal");
    const irreducible_closure_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    irreducible_closure_audit.addFileArg(b.path("luau/irreducible_closure_conformance.luau"));
    irreducible_closure_audit.addFileInput(b.path("luau/irreducible_closure_audit.luau"));
    irreducible_closure_audit.addFileInput(b.path("luau/lifter_ir.luau"));
    irreducible_closure_audit.addFileInput(b.path("luau/json_codec.luau"));
    irreducible_closure_audit.addArg("audit");
    irreducible_closure_audit.addFileArg(luau_irreducible_closure_conformance.input_ir);
    irreducible_closure_audit.addFileArg(luau_irreducible_closure_conformance.resolved_ir);
    irreducible_closure_audit.addFileArg(irreducible_closure_reresolved_ir);
    irreducible_closure_audit.addFileArg(luau_irreducible_closure_conformance.generated_luau);
    const luau_irreducible_iteration_conformance = addLuauFixtureConformanceWithEngine(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/irreducible_iteration_conformance.luau",
        "irreducible-iteration-convergence",
        if (z3_enabled) "z3" else "internal",
    );
    const irreducible_iteration_structure_ast = addStructureAstAudit(
        b,
        "irreducible-iteration-convergence",
        luau_irreducible_iteration_conformance.generated_luau,
    );
    const irreducible_iteration_reresolve = b.addRunArtifact(exe);
    if (z3_enabled) irreducible_iteration_reresolve.addPathDir(b.pathFromRoot(z3_bin));
    irreducible_iteration_reresolve.addArg("resolve-ir");
    irreducible_iteration_reresolve.addFileArg(luau_irreducible_iteration_conformance.resolved_ir);
    const irreducible_iteration_reresolved_ir = irreducible_iteration_reresolve.addOutputFileArg("irreducible-iteration-convergence.reresolved.lifter-ir.json");
    irreducible_iteration_reresolve.addArg(if (z3_enabled) "z3" else "internal");
    const irreducible_iteration_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    irreducible_iteration_audit.addFileArg(b.path("luau/irreducible_iteration_conformance.luau"));
    irreducible_iteration_audit.addFileInput(b.path("luau/irreducible_iteration_audit.luau"));
    irreducible_iteration_audit.addFileInput(b.path("luau/lifter_ir.luau"));
    irreducible_iteration_audit.addFileInput(b.path("luau/json_codec.luau"));
    irreducible_iteration_audit.addArg("audit");
    irreducible_iteration_audit.addFileArg(luau_irreducible_iteration_conformance.input_ir);
    irreducible_iteration_audit.addFileArg(luau_irreducible_iteration_conformance.resolved_ir);
    irreducible_iteration_audit.addFileArg(irreducible_iteration_reresolved_ir);
    irreducible_iteration_audit.addFileArg(luau_irreducible_iteration_conformance.generated_luau);
    const irreducible_iteration_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "irreducible-iteration-convergence",
        luau_irreducible_iteration_conformance.resolved_ir,
    );
    const source_frontend_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/straight_line_source.luau",
        "source-frontend-straight-line",
    );
    const source_frontend_effectful_assignment_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/effectful_assignment_source.luau",
        "source-frontend-effectful-assignment",
    );
    const source_frontend_if_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/structured_if_source.luau",
        "source-frontend-structured-if",
    );
    const source_frontend_capture_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/captured_mutation_source.luau",
        "source-frontend-captured-mutation",
    );
    const source_frontend_variadic_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/variadic_forward_source.luau",
        "source-frontend-variadic-forward",
    );
    const source_frontend_chunk_varargs_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/chunk_varargs_source.luau",
        "source-frontend-chunk-varargs",
    );
    const source_frontend_table_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/table_access_source.luau",
        "source-frontend-table-access",
    );
    const source_frontend_while_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/while_loop_source.luau",
        "source-frontend-while-loop",
    );
    const source_frontend_loop_control_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/loop_control_source.luau",
        "source-frontend-loop-control",
    );
    const source_frontend_short_circuit_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/short_circuit_source.luau",
        "source-frontend-short-circuit",
    );
    const source_frontend_multi_assignment_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/multi_assignment_source.luau",
        "source-frontend-multi-assignment",
    );
    const source_frontend_method_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/method_call_source.luau",
        "source-frontend-method-call",
    );
    const source_frontend_recursive_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/recursive_local_source.luau",
        "source-frontend-recursive-local",
    );
    const source_frontend_repeat_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/repeat_loop_source.luau",
        "source-frontend-repeat-loop",
    );
    const source_frontend_compound_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/compound_assignment_source.luau",
        "source-frontend-compound-assignment",
    );
    const source_frontend_if_expression_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/if_expression_source.luau",
        "source-frontend-if-expression",
    );
    const source_frontend_iteration_capture_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/per_iteration_capture_source.luau",
        "source-frontend-per-iteration-capture",
    );
    const per_iteration_capture_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-per-iteration-capture",
        source_frontend_iteration_capture_conformance.resolved_ir,
    );
    const repeat_loop_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-repeat-loop",
        source_frontend_repeat_conformance.resolved_ir,
    );
    const source_frontend_cell_branch_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/per_iteration_capture_branch_source.luau",
        "source-frontend-per-iteration-capture-branch",
    );
    const per_execution_cell_dispatcher_refusal = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-per-iteration-capture-branch",
        source_frontend_cell_branch_conformance.resolved_ir,
    );
    const per_execution_cell_inherited_flat_refusal = addAutomaticRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "per-execution-cell-inherited-flat",
        b.path("luau/fixtures/per_execution_cell_inherited_flat.lifter-ir.json"),
    );
    const per_execution_cell_layout_automatic_emit = b.addRunArtifact(exe);
    if (z3_enabled) per_execution_cell_layout_automatic_emit.addPathDir(b.pathFromRoot(z3_bin));
    per_execution_cell_layout_automatic_emit.addArg("emit-readable-luau-strategy");
    per_execution_cell_layout_automatic_emit.addFileArg(b.path("luau/fixtures/per_execution_cell_inherited_flat.lifter-ir.json"));
    const per_execution_cell_layout_automatic_luau = per_execution_cell_layout_automatic_emit.addOutputFileArg("per-execution-cell-inherited-flat-layout.automatic.luau");
    per_execution_cell_layout_automatic_emit.addArgs(&.{ "standard-luau", "automatic" });
    per_execution_cell_layout_automatic_emit.expectExitCode(0);
    const per_execution_cell_layout_automatic_audit = addStructureAstAudit(b, "per-execution-cell-inherited-flat", per_execution_cell_layout_automatic_luau);
    per_execution_cell_layout_automatic_audit.expectExitCode(0);
    per_execution_cell_layout_automatic_audit.expectStdOutMatch(" pc_declarations=1 dispatcher_loops=1 ");
    const per_execution_cell_layout_dispatcher_emit = b.addRunArtifact(exe);
    if (z3_enabled) per_execution_cell_layout_dispatcher_emit.addPathDir(b.pathFromRoot(z3_bin));
    per_execution_cell_layout_dispatcher_emit.addArg("emit-readable-luau-strategy");
    per_execution_cell_layout_dispatcher_emit.addFileArg(b.path("luau/fixtures/per_execution_cell_inherited_flat.lifter-ir.json"));
    const per_execution_cell_layout_dispatcher_luau = per_execution_cell_layout_dispatcher_emit.addOutputFileArg("per-execution-cell-inherited-flat-layout.dispatcher.luau");
    per_execution_cell_layout_dispatcher_emit.addArgs(&.{ "standard-luau", "dispatcher" });
    per_execution_cell_layout_dispatcher_emit.expectExitCode(0);
    const per_execution_cell_layout_dispatcher_audit = addStructureAstAudit(b, "per-execution-cell-inherited-flat", per_execution_cell_layout_dispatcher_luau);
    per_execution_cell_layout_dispatcher_audit.expectExitCode(0);
    per_execution_cell_layout_dispatcher_audit.expectStdOutMatch(" pc_declarations=3 dispatcher_loops=2 ");
    const per_execution_cell_structured_child_runtime = addAutomaticRuntimeCaseConformance(b, exe, z3_enabled, z3_bin, "per-execution-cell-flat-root-structured-child", "per-execution-cell-inherited-flat", b.path("luau/fixtures/per_execution_cell_flat_root_structured_child.lifter-ir.json"));
    const per_execution_cell_structured_grandchild_runtime = addAutomaticRuntimeCaseConformance(b, exe, z3_enabled, z3_bin, "per-execution-cell-flat-root-structured-grandchild", "per-execution-cell-inherited-flat", b.path("luau/fixtures/per_execution_cell_flat_root_structured_grandchild.lifter-ir.json"));
    const numeric_operand_flat_grouping = addNumericOperandGroupingConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/numeric_operand_flat_concat.lifter-ir.json",
        "numeric-operand-flat-concat.automatic.luau",
        "automatic",
        "luau-numeric",
    );
    const numeric_operand_semantic_grouping = addNumericOperandGroupingConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/numeric_operand_semantic_concat.lifter-ir.json",
        "numeric-operand-semantic-concat.automatic.luau",
        "automatic",
        "semantic-normalized",
    );
    // A `repeat` whose header block's own branch leaves the loop: six functions in one module (a store then a break,
    // a bare break, a break in an `if` arm before a statement and as the arm's last statement, a header arm that
    // returns, and a store then a break in an `if` arm of a `while` before a return), the same `repeat` nested in a
    // `while`, and two whose `repeat` ends a `while` body or an `if` arm in one. Their cases pin no dispatcher form
    // and the source's results.
    const source_frontend_repeat_header_exit_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/repeat_header_exit_source.luau",
        "source-frontend-repeat-header-exit",
    );
    const source_frontend_repeat_header_exit_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/repeat_header_exit_source.luau",
        "source-frontend-repeat-header-exit-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_repeat_header_exit_nested_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/repeat_header_exit_nested_source.luau",
        "source-frontend-repeat-header-exit-nested",
    );
    const source_frontend_repeat_header_exit_nested_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/repeat_header_exit_nested_source.luau",
        "source-frontend-repeat-header-exit-nested-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_repeat_header_exit_while_tail_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/repeat_header_exit_while_tail_source.luau",
        "source-frontend-repeat-header-exit-while-tail",
    );
    const source_frontend_repeat_header_exit_while_tail_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/repeat_header_exit_while_tail_source.luau",
        "source-frontend-repeat-header-exit-while-tail-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_typed_block_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/typed_block_source.luau",
        "source-frontend-typed-block",
    );
    const source_frontend_numeric_for_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/numeric_for_source.luau",
        "source-frontend-numeric-for",
    );
    const source_frontend_generic_for_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/generic_for_source.luau",
        "source-frontend-generic-for",
    );
    const source_frontend_always_return_iteration_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/always_return_iteration_source.luau",
        "source-frontend-always-return-iteration",
    );
    const source_frontend_always_return_iteration_in_loop_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/always_return_iteration_in_loop_source.luau",
        "source-frontend-always-return-iteration-in-loop",
    );
    const source_frontend_always_break_iteration_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/always_break_iteration_source.luau",
        "source-frontend-always-break-iteration",
    );
    const source_frontend_always_break_transfer_iteration_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/always_break_transfer_iteration_source.luau",
        "source-frontend-always-break-transfer-iteration",
    );
    const source_frontend_generic_initializer_scope_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/generic_initializer_scope_source.luau",
        "source-frontend-generic-initializer-scope",
    );
    const source_frontend_generic_initializer_scope_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/generic_initializer_scope_source.luau",
        "source-frontend-generic-initializer-scope-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_generic_initializer_scope_storage_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/generic_initializer_scope_storage_source.luau",
        "source-frontend-generic-initializer-scope-storage",
    );
    const source_frontend_generic_initializer_scope_storage_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/generic_initializer_scope_storage_source.luau",
        "source-frontend-generic-initializer-scope-storage-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_generic_initializer_order_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/generic_initializer_order_source.luau",
        "source-frontend-generic-initializer-order",
    );
    const source_frontend_generic_initializer_order_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/generic_initializer_order_source.luau",
        "source-frontend-generic-initializer-order-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_binary_operand_read_order_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/binary_operand_read_order_source.luau",
        "source-frontend-binary-operand-read-order",
    );
    const source_frontend_binary_operand_read_order_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/binary_operand_read_order_source.luau",
        "source-frontend-binary-operand-read-order-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_proved_branch_unreachable_consumer_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/proved_branch_unreachable_consumer_source.luau",
        "source-frontend-proved-branch-unreachable-consumer",
    );
    const source_frontend_proved_branch_unreachable_consumer_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/proved_branch_unreachable_consumer_source.luau",
        "source-frontend-proved-branch-unreachable-consumer-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_generic_initializer_read_after_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/generic_initializer_read_after_source.luau",
        "source-frontend-generic-initializer-read-after",
    );
    const source_frontend_generic_initializer_read_after_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/generic_initializer_read_after_source.luau",
        "source-frontend-generic-initializer-read-after-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_index_base_read_order_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/index_base_read_order_source.luau",
        "source-frontend-index-base-read-order",
    );
    const source_frontend_index_base_read_order_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/index_base_read_order_source.luau",
        "source-frontend-index-base-read-order-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_assignment_target_read_order_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/assignment_target_read_order_source.luau",
        "source-frontend-assignment-target-read-order",
    );
    const source_frontend_assignment_target_read_order_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/assignment_target_read_order_source.luau",
        "source-frontend-assignment-target-read-order-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_compound_table_target_read_order_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/compound_table_target_read_order_source.luau",
        "source-frontend-compound-table-target-read-order",
    );
    const source_frontend_compound_table_target_read_order_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/compound_table_target_read_order_source.luau",
        "source-frontend-compound-table-target-read-order-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_multiple_assignment_value_read_order_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/multiple_assignment_value_read_order_source.luau",
        "source-frontend-multiple-assignment-value-read-order",
    );
    const source_frontend_multiple_assignment_value_read_order_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/multiple_assignment_value_read_order_source.luau",
        "source-frontend-multiple-assignment-value-read-order-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_multiple_assignment_store_order_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/multiple_assignment_store_order_source.luau",
        "source-frontend-multiple-assignment-store-order",
    );
    const source_frontend_multiple_assignment_store_order_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/multiple_assignment_store_order_source.luau",
        "source-frontend-multiple-assignment-store-order-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_table_constructor_key_read_order_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/table_constructor_key_read_order_source.luau",
        "source-frontend-table-constructor-key-read-order",
    );
    const source_frontend_table_constructor_key_read_order_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/table_constructor_key_read_order_source.luau",
        "source-frontend-table-constructor-key-read-order-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_method_receiver_read_order_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/method_receiver_read_order_source.luau",
        "source-frontend-method-receiver-read-order",
    );
    const source_frontend_method_receiver_read_order_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/method_receiver_read_order_source.luau",
        "source-frontend-method-receiver-read-order-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_builtin_fastcall_read_order_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/builtin_fastcall_argument_read_order_source.luau",
        "source-frontend-builtin-fastcall-read-order",
    );
    const source_frontend_builtin_fastcall_read_order_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/builtin_fastcall_argument_read_order_source.luau",
        "source-frontend-builtin-fastcall-read-order-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_builtin_fastcall_optimize0_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/builtin_fastcall_optimize0_source.luau",
        "source-frontend-builtin-fastcall-optimize0",
    );
    const source_frontend_builtin_fastcall_optimize0_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/builtin_fastcall_optimize0_source.luau",
        "source-frontend-builtin-fastcall-optimize0-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_builtin_fastcall_optimize2_refusal = b.addSystemCommand(&.{ luneExe(b), "run" });
    source_frontend_builtin_fastcall_optimize2_refusal.addFileArg(b.path("luau/lift_source.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_frontend.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_local_binding.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_local_identity.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_lexical_scope.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_runtime_context.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_expression_slots.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_expression_scalar.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_statement_slots.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_admission.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_target_recovery.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_frontend_outcome.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_frontend_expressions.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_frontend_tables.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_frontend_operator_domains.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_frontend_place_domains.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_frontend_control.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/ast_frontend_iteration.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/intrinsic_bindings.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/recovery_admission.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/lifter_ir.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/json_codec.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/recovery_manifest.luau"));
    addTemporalIdentityInputs(b, source_frontend_builtin_fastcall_optimize2_refusal);
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/target_recovery.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/target_result_contracts.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileInput(b.path("luau/target_proof_bundle.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addFileArg(.{ .cwd_relative = luauAstExe(b) });
    source_frontend_builtin_fastcall_optimize2_refusal.addFileArg(.{ .cwd_relative = luauCompileExe(b) });
    source_frontend_builtin_fastcall_optimize2_refusal.addFileArg(b.path("luau/fixtures/builtin_fastcall_optimize2_source.luau"));
    source_frontend_builtin_fastcall_optimize2_refusal.addArg("source-frontend-builtin-fastcall-optimize2");
    _ = source_frontend_builtin_fastcall_optimize2_refusal.addOutputFileArg("source-frontend-builtin-fastcall-optimize2.lifter-ir.json");
    source_frontend_builtin_fastcall_optimize2_refusal.addArg("source-frontend-builtin-fastcall-optimize2");
    source_frontend_builtin_fastcall_optimize2_refusal.expectExitCode(1);
    source_frontend_builtin_fastcall_optimize2_refusal.expectStdErrMatch("unsupported_optimization_level at ");
    source_frontend_builtin_fastcall_optimize2_refusal.expectStdErrMatch("asks for optimisation level 2");
    const source_frontend_integer_literal_refusal = b.addSystemCommand(&.{ luneExe(b), "run" });
    source_frontend_integer_literal_refusal.addFileArg(b.path("luau/lift_source.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_frontend.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_local_binding.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_local_identity.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_lexical_scope.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_runtime_context.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_expression_slots.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_expression_scalar.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_statement_slots.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_admission.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_target_recovery.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_frontend_outcome.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_frontend_expressions.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_frontend_tables.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_frontend_operator_domains.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_frontend_place_domains.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_frontend_control.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/ast_frontend_iteration.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/intrinsic_bindings.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/recovery_admission.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/lifter_ir.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/json_codec.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/recovery_manifest.luau"));
    addTemporalIdentityInputs(b, source_frontend_integer_literal_refusal);
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/target_recovery.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/target_result_contracts.luau"));
    source_frontend_integer_literal_refusal.addFileInput(b.path("luau/target_proof_bundle.luau"));
    source_frontend_integer_literal_refusal.addFileArg(.{ .cwd_relative = luauAstExe(b) });
    source_frontend_integer_literal_refusal.addFileArg(.{ .cwd_relative = luauCompileExe(b) });
    source_frontend_integer_literal_refusal.addFileArg(b.path("luau/fixtures/integer_literal_source.luau"));
    source_frontend_integer_literal_refusal.addArg("source-frontend-integer-literal");
    _ = source_frontend_integer_literal_refusal.addOutputFileArg("source-frontend-integer-literal.lifter-ir.json");
    source_frontend_integer_literal_refusal.addArg("source-frontend-integer-literal");
    source_frontend_integer_literal_refusal.expectExitCode(1);
    source_frontend_integer_literal_refusal.expectStdErrMatch("unsupported_integer_literal at 3,15: ");
    source_frontend_integer_literal_refusal.expectStdErrMatch("i-suffixed integer literal");
    const source_frontend_table_pack_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/table_pack_source.luau",
        "source-frontend-table-pack",
    );
    const source_frontend_function_statement_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/function_statement_source.luau",
        "source-frontend-function-statement",
    );
    const source_frontend_closure_store_environment_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/closure_store_environment_source.luau",
        "source-frontend-closure-store-environment",
    );
    const source_frontend_closure_store_environment_direct_locals_conformance = addLuauSourceConformanceForTarget(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/closure_store_environment_source.luau",
        "source-frontend-closure-store-environment-direct-locals",
        "direct-locals-luau",
    );
    const source_frontend_closure_store_parenthesized_target_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/closure_store_parenthesized_target_source.luau",
        "source-frontend-closure-store-parenthesized-target",
    );
    const closure_store_parenthesized_target_dispatcher = addDispatcherRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-closure-store-parenthesized-target",
        source_frontend_closure_store_parenthesized_target_conformance.resolved_ir,
    );
    const closure_store_parenthesized_target_automatic = addAutomaticRuntimeConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "source-frontend-closure-store-parenthesized-target",
        source_frontend_closure_store_parenthesized_target_conformance.resolved_ir,
    );
    const source_frontend_interpolation_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/interpolation_source.luau",
        "source-frontend-interpolation",
    );
    const source_frontend_intrinsic_invocation_conformance = addLuauSourceManifestConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/intrinsic_invocation_source.luau",
        "luau/fixtures/intrinsic_invocation_manifest.json",
        "source-frontend-intrinsic-invocation",
    );
    const source_frontend_coroutine_wrap_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/coroutine_wrap_source.luau",
        "source-frontend-coroutine-wrap",
    );
    const source_frontend_double_rounding_comparison_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/double_rounding_comparison_source.luau",
        "source-frontend-double-rounding-comparison",
    );
    const source_frontend_double_rounding_comparison_in_range_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/double_rounding_comparison_in_range_source.luau",
        "source-frontend-double-rounding-comparison-in-range",
    );
    const source_frontend_wide_integral_number_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/wide_integral_number_source.luau",
        "source-frontend-wide-integral-number",
    );
    const source_frontend_exact_number_literal_conformance = addLuauSourceConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/exact_number_literal_source.luau",
        "source-frontend-exact-number-literal",
    );
    // Constructors with many array items, each in the standard target and in direct locals: luau-compile stores array
    // items in batches of 16 above the table register, so 253, 254, 300 and 1000 items take the same registers.
    const many_item_sources = [_][2][]const u8{
        .{ "luau/fixtures/many_array_items_253_source.luau", "source-frontend-many-array-items-253" },
        .{ "luau/fixtures/many_array_items_254_source.luau", "source-frontend-many-array-items-254" },
        .{ "luau/fixtures/many_array_items_300_source.luau", "source-frontend-many-array-items-300" },
        .{ "luau/fixtures/many_array_items_1000_source.luau", "source-frontend-many-array-items-1000" },
        .{ "luau/fixtures/many_number_items_300_source.luau", "source-frontend-many-number-items-300" },
        .{ "luau/fixtures/many_array_items_in_function_300_source.luau", "source-frontend-many-array-items-in-function-300" },
        .{ "luau/fixtures/many_computed_items_300_source.luau", "source-frontend-many-computed-items-300" },
    };
    var many_item_conformance: [2 * many_item_sources.len]FixtureConformance = undefined;
    for (many_item_sources, 0..) |many_item_source, many_item_index| {
        many_item_conformance[2 * many_item_index] = addLuauSourceConformance(b, exe, z3_enabled, z3_bin, many_item_source[0], many_item_source[1]);
        many_item_conformance[2 * many_item_index + 1] = addLuauSourceConformanceForTarget(
            b,
            exe,
            z3_enabled,
            z3_bin,
            many_item_source[0],
            b.fmt("{s}-direct-locals", .{many_item_source[1]}),
            "direct-locals-luau",
        );
    }
    const nested_constructor_last_item_conformance = addNestedConstructorLastItemConformance(b, exe, z3_enabled, z3_bin);
    const source_frontend_target_resolution_conformance = addLuauSourceManifestProofConformance(
        b,
        exe,
        proof_attest,
        z3_enabled,
        z3_bin,
        "luau/fixtures/target_resolution_source.luau",
        "luau/fixtures/target_resolution_manifest.json",
        "luau/fixtures/target_resolution_proof_bundle.json",
        "03a107bff3ce10be1d70dd18e74bc09967e4d6309ba50d5f1ddc8664125531b8",
        "source-frontend-target-resolution",
    );
    const source_frontend_opaque_result_target_conformance = addLuauSourceManifestConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/opaque_result_target_source.luau",
        "luau/fixtures/opaque_result_target_manifest.json",
        "source-frontend-opaque-result-target",
    );
    const source_frontend_nonintrinsic_target_origin_conformance = addLuauSourceManifestConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/nonintrinsic_target_origin_source.luau",
        "luau/fixtures/nonintrinsic_target_origin_manifest.json",
        "source-frontend-nonintrinsic-target-origin",
    );
    const source_frontend_access_path_target_origin_conformance = addLuauSourceManifestConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/access_path_target_origin_source.luau",
        "luau/fixtures/access_path_target_origin_manifest.json",
        "source-frontend-access-path-target-origin",
    );
    const source_frontend_dynamic_key_target_origin_conformance = addLuauSourceManifestConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/dynamic_key_target_origin_source.luau",
        "luau/fixtures/dynamic_key_target_origin_manifest.json",
        "source-frontend-dynamic-key-target-origin",
    );
    const source_frontend_namecall_target_origin_conformance = addLuauSourceManifestConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/namecall_target_origin_source.luau",
        "luau/fixtures/namecall_target_origin_manifest.json",
        "source-frontend-namecall-target-origin",
    );
    const source_frontend_compositional_access_path_conformance = addLuauSourceManifestConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/compositional_access_path_source.luau",
        "luau/fixtures/compositional_access_path_manifest.json",
        "source-frontend-compositional-access-path",
    );
    const source_frontend_temporal_target_identity_conformance = addLuauSourceManifestConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/fixtures/temporal_target_identity_source.luau",
        "luau/fixtures/temporal_target_identity_manifest.json",
        "source-frontend-temporal-target-identity",
    );
    const ast_admission_compile_conformance = addLuauSourceCompileConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/ast_admission.luau",
        "strict-module-ast-admission",
        if (z3_enabled) "z3" else "internal",
    );
    const loop_module_compile_conformance = addLuauSourceCompileConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/loop_conformance.luau",
        "strict-module-loop-conformance",
        if (z3_enabled) "z3" else "internal",
    );
    const register_budget_module_compile_conformance = addLuauSourceCompileConformance(
        b,
        exe,
        z3_enabled,
        z3_bin,
        "luau/register_budget_oracle.luau",
        "strict-module-register-budget-oracle",
        if (z3_enabled) "z3" else "internal",
    );

    const register_budget_oracle = addRegisterBudgetOracle(b);
    const dispatcher_local_budget_conformance = addDispatcherLocalBudgetConformance(b, exe, z3_enabled, z3_bin);
    const dispatcher_generic_budget_conformance = addDispatcherGenericBudgetConformance(b, exe, z3_enabled, z3_bin);
    const native_loop_register_conformance = addNativeLoopRegisterConformance(b, exe, z3_enabled, z3_bin);
    const compile_check_positive = b.addRunArtifact(exe);
    if (z3_enabled) compile_check_positive.addPathDir(b.pathFromRoot(z3_bin));
    compile_check_positive.addArg("emit-luau");
    compile_check_positive.addFileArg(absolute_conformance.input_ir);
    _ = compile_check_positive.addOutputFileArg("compile-check-positive.generated.luau");
    compile_check_positive.addArg("standard-luau");
    compile_check_positive.addFileArg(.{ .cwd_relative = luauCompileExe(b) });
    compile_check_positive.expectExitCode(0);
    if (!trace_normalize_phases) compile_check_positive.expectStdErrEqual("");
    const rejection_output_files = b.addWriteFiles();
    const rejection_output = rejection_output_files.add(
        "compile-check-preserved-invalid.luau",
        "local =\n",
    );
    const compile_check_rejection = b.addRunArtifact(exe);
    if (z3_enabled) compile_check_rejection.addPathDir(b.pathFromRoot(z3_bin));
    compile_check_rejection.addArg("emit-luau-solved-checked");
    compile_check_rejection.addFileArg(absolute_conformance.resolved_ir);
    compile_check_rejection.addFileArg(rejection_output);
    compile_check_rejection.addArg(if (z3_enabled) "z3" else "internal");
    compile_check_rejection.addArg("standard-luau");
    compile_check_rejection.addArtifactArg(exe);
    compile_check_rejection.expectExitCode(1);
    compile_check_rejection.expectStdErrMatch("diagnostic=luau_compile_check_failed entity=null");
    compile_check_rejection.expectStdErrMatch("reason=compiler_rejected");
    compile_check_rejection.expectStdErrMatch("termination=exited code=1");
    compile_check_rejection.expectStdErrMatch("stdout_bytes=0 stdout=\"\"");
    compile_check_rejection.expectStdErrMatch("stderr_bytes=");
    const compile_check_preserved_output = b.addSystemCommand(&.{ luauCompileExe(b), "--null" });
    compile_check_preserved_output.addFileArg(rejection_output);
    compile_check_preserved_output.step.dependOn(&compile_check_rejection.step);
    compile_check_preserved_output.expectExitCode(1);
    const legacy_unchecked_output_files = b.addWriteFiles();
    const legacy_unchecked_output = legacy_unchecked_output_files.add(
        "legacy-unchecked-preserved-invalid.luau",
        "local =\n",
    );
    const legacy_unchecked_rejection = b.addRunArtifact(exe);
    if (z3_enabled) legacy_unchecked_rejection.addPathDir(b.pathFromRoot(z3_bin));
    legacy_unchecked_rejection.addArg("emit-luau");
    legacy_unchecked_rejection.addFileArg(absolute_conformance.input_ir);
    legacy_unchecked_rejection.addFileArg(legacy_unchecked_output);
    legacy_unchecked_rejection.addArg("standard-luau");
    legacy_unchecked_rejection.expectExitCode(1);
    const legacy_unchecked_preserved_output = std.Build.Step.CheckFile.create(b, legacy_unchecked_output, .{
        .expected_exact = "local =\n",
    });
    legacy_unchecked_preserved_output.step.dependOn(&legacy_unchecked_rejection.step);
    const resolve_refusal_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    if (z3_enabled) resolve_refusal_audit.addPathDir(b.pathFromRoot(z3_bin));
    resolve_refusal_audit.addFileArg(b.path("luau/resolve_refusal_audit.luau"));
    resolve_refusal_audit.addArtifactArg(exe);
    resolve_refusal_audit.addFileArg(b.path("luau/fixtures/resolve_refusal_b3.lifter-ir.json"));
    _ = resolve_refusal_audit.addOutputDirectoryArg("resolve-refusal");
    // Re-resolution fixed-point conformance over the recorded nested graph.
    // resolve-ir iterates to a fixed point (src/proof_orchestrator.zig), so re-resolving the resolved
    // IR is byte-idempotent and the resolved IR is already a normalizer fixed point.
    const nested_reresolve_resolve = b.addRunArtifact(exe);
    if (z3_enabled) nested_reresolve_resolve.addPathDir(b.pathFromRoot(z3_bin));
    nested_reresolve_resolve.addArg("resolve-ir");
    nested_reresolve_resolve.addFileArg(b.path("luau/fixtures/nested_inner_cycle_w1.lifter-ir.json"));
    const nested_reresolve_resolved_ir = nested_reresolve_resolve.addOutputFileArg("nested-inner-cycle-w1.resolved.lifter-ir.json");
    nested_reresolve_resolve.addArg("internal");
    const nested_reresolve_reresolve = b.addRunArtifact(exe);
    if (z3_enabled) nested_reresolve_reresolve.addPathDir(b.pathFromRoot(z3_bin));
    nested_reresolve_reresolve.addArg("resolve-ir");
    nested_reresolve_reresolve.addFileArg(nested_reresolve_resolved_ir);
    const nested_reresolve_reresolved_ir = nested_reresolve_reresolve.addOutputFileArg("nested-inner-cycle-w1.reresolved.lifter-ir.json");
    nested_reresolve_reresolve.addArg("internal");
    const nested_reresolve_third = b.addRunArtifact(exe);
    if (z3_enabled) nested_reresolve_third.addPathDir(b.pathFromRoot(z3_bin));
    nested_reresolve_third.addArg("resolve-ir");
    nested_reresolve_third.addFileArg(nested_reresolve_reresolved_ir);
    const nested_reresolve_third_ir = nested_reresolve_third.addOutputFileArg("nested-inner-cycle-w1.third.lifter-ir.json");
    nested_reresolve_third.addArg("internal");
    const nested_reresolve_renormalize = b.addRunArtifact(exe);
    if (z3_enabled) nested_reresolve_renormalize.addPathDir(b.pathFromRoot(z3_bin));
    nested_reresolve_renormalize.addArg("normalize-ir");
    nested_reresolve_renormalize.addFileArg(nested_reresolve_resolved_ir);
    const nested_reresolve_renormalized_ir = nested_reresolve_renormalize.addOutputFileArg("nested-inner-cycle-w1.renormalized.lifter-ir.json");
    const nested_reresolve_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    nested_reresolve_audit.addFileArg(b.path("luau/irreducible_nested_reresolve_audit.luau"));
    nested_reresolve_audit.addFileArg(nested_reresolve_resolved_ir);
    nested_reresolve_audit.addFileArg(nested_reresolve_reresolved_ir);
    nested_reresolve_audit.addFileArg(nested_reresolve_third_ir);
    nested_reresolve_audit.addFileArg(nested_reresolve_renormalized_ir);
    const conformance_step = b.step("conformance", "Validate, emit, and compile Zig- and Luau-built generic fixtures");
    // Author-written programs whose latch carries
    // values of its own loop (a header instruction or parameter, a mid block, the edge source), and their controls.
    // specializeForwardingJump forwards the authenticated latch through the dominator-path rule, so emit-luau writes
    // each forwarded function structured on both targets; the controls keep their structure class, the two refusals
    // keep their lines, the Phase-0 runs pin the post-split collapse's self-target guard, and the resolved mid twin
    // pins the published forwarding record.
    const latch_forward_fixtures = [_]struct { path: []const u8, name: []const u8, audit: []const u8 }{
        .{ .path = "luau/fixtures/latch_forward_t2y_place.lifter-ir.json", .name = "latch-forward-t2y-place", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2x.lifter-ir.json", .name = "latch-forward-t2x", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2.lifter-ir.json", .name = "latch-forward-t2", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_wp.lifter-ir.json", .name = "latch-forward-wp", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_wl.lifter-ir.json", .name = "latch-forward-wl", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2x_body1.lifter-ir.json", .name = "latch-forward-t2x-body1", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2x_body4.lifter-ir.json", .name = "latch-forward-t2x-body4", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2x_hang4x2.lifter-ir.json", .name = "latch-forward-t2x-hang4x2", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2x_hang6x2.lifter-ir.json", .name = "latch-forward-t2x-hang6x2", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2x_pre2.lifter-ir.json", .name = "latch-forward-t2x-pre2", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2x_pre8.lifter-ir.json", .name = "latch-forward-t2x-pre8", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2x_three.lifter-ir.json", .name = "latch-forward-t2x-three", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2y_body1.lifter-ir.json", .name = "latch-forward-t2y-body1", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2y_body4.lifter-ir.json", .name = "latch-forward-t2y-body4", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2y_hang4x2.lifter-ir.json", .name = "latch-forward-t2y-hang4x2", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2y_hang6x2.lifter-ir.json", .name = "latch-forward-t2y-hang6x2", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2y_pre2.lifter-ir.json", .name = "latch-forward-t2y-pre2", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2y_pre8.lifter-ir.json", .name = "latch-forward-t2y-pre8", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2y_three.lifter-ir.json", .name = "latch-forward-t2y-three", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2y_place_mid.lifter-ir.json", .name = "latch-forward-t2y-place-mid", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2x_mid.lifter-ir.json", .name = "latch-forward-t2x-mid", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_wp_mid.lifter-ir.json", .name = "latch-forward-wp-mid", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_wl_mid.lifter-ir.json", .name = "latch-forward-wl-mid", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2y_place_bodyarg.lifter-ir.json", .name = "latch-forward-t2y-place-bodyarg", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_t2x_bodyarg.lifter-ir.json", .name = "latch-forward-t2x-bodyarg", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_control_noparam.lifter-ir.json", .name = "latch-forward-control-noparam", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_control_wok.lifter-ir.json", .name = "latch-forward-control-wok", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_control_wok_mid.lifter-ir.json", .name = "latch-forward-control-wok-mid", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_control_cycle2_param.lifter-ir.json", .name = "latch-forward-control-cycle2-param", .audit = "class=structured-no-dispatcher" },
        .{ .path = "luau/fixtures/latch_forward_control_presolved.lifter-ir.json", .name = "latch-forward-control-presolved", .audit = "class=dispatcher-present" },
        .{ .path = "luau/fixtures/latch_forward_control_presolved_place.lifter-ir.json", .name = "latch-forward-control-presolved-place", .audit = "class=dispatcher-present" },
    };
    for (latch_forward_fixtures) |fixture| {
        addLatchForwardConformance(b, exe, z3_enabled, z3_bin, trace_normalize_phases, conformance_step, fixture.path, fixture.name, "standard-luau", fixture.audit);
        addLatchForwardConformance(b, exe, z3_enabled, z3_bin, trace_normalize_phases, conformance_step, fixture.path, b.fmt("{s}-direct-locals", .{fixture.name}), "direct-locals-luau", fixture.audit);
    }
    addLatchForwardConformance(b, exe, z3_enabled, z3_bin, trace_normalize_phases, conformance_step, "luau/fixtures/latch_forward_control_t2x_pre.lifter-ir.json", "latch-forward-control-t2x-pre", "standard-luau", "class=dispatcher-present");
    const latch_forward_pre_refusal = b.addRunArtifact(exe);
    if (z3_enabled) latch_forward_pre_refusal.addPathDir(b.pathFromRoot(z3_bin));
    latch_forward_pre_refusal.addArg("emit-luau");
    latch_forward_pre_refusal.addFileArg(b.path("luau/fixtures/latch_forward_control_t2y_place_pre.lifter-ir.json"));
    _ = latch_forward_pre_refusal.addOutputFileArg("latch-forward-control-t2y-place-pre.generated.luau");
    latch_forward_pre_refusal.addArg("standard-luau");
    latch_forward_pre_refusal.addFileArg(.{ .cwd_relative = luauCompileExe(b) });
    latch_forward_pre_refusal.expectStdErrMatch("normalize failure phase=clone-availability function=0 blocks=10 rewrites=2");
    latch_forward_pre_refusal.expectExitCode(1);
    conformance_step.dependOn(&latch_forward_pre_refusal.step);
    const latch_forward_plain_refusal = b.addRunArtifact(exe);
    if (z3_enabled) latch_forward_plain_refusal.addPathDir(b.pathFromRoot(z3_bin));
    latch_forward_plain_refusal.addArg("normalize-ir");
    latch_forward_plain_refusal.addFileArg(b.path("luau/fixtures/latch_forward_control_presolved_place.lifter-ir.json"));
    _ = latch_forward_plain_refusal.addOutputFileArg("latch-forward-control-presolved-place.normalized.lifter-ir.json");
    latch_forward_plain_refusal.expectStdErrMatch("normalize failure phase=feedback-unsplittable-collision iteration=0 blocks=8 structural_clones=0 rewrites=0 arms=0");
    latch_forward_plain_refusal.expectExitCode(1);
    conformance_step.dependOn(&latch_forward_plain_refusal.step);
    const latch_forward_phase0 = [_]struct { path: []const u8, name: []const u8 }{
        .{ .path = "luau/fixtures/latch_forward_control_cycle2_param.lifter-ir.json", .name = "latch-forward-control-cycle2-param" },
        .{ .path = "luau/fixtures/latch_forward_guard_cycle2_fparam.lifter-ir.json", .name = "latch-forward-guard-cycle2-fparam" },
    };
    for (latch_forward_phase0) |fixture| {
        const phase0 = b.addRunArtifact(exe);
        if (z3_enabled) phase0.addPathDir(b.pathFromRoot(z3_bin));
        phase0.addArg("normalize-ir-budget");
        phase0.addFileArg(b.path(fixture.path));
        _ = phase0.addOutputFileArg(b.fmt("{s}.phase0.lifter-ir.json", .{fixture.name}));
        phase0.addArgs(&.{ "1", "0" });
        if (!trace_normalize_phases) phase0.expectStdErrEqual("");
        phase0.expectExitCode(0);
        conformance_step.dependOn(&phase0.step);
    }
    const latch_forward_pin_resolve = b.addRunArtifact(exe);
    if (z3_enabled) latch_forward_pin_resolve.addPathDir(b.pathFromRoot(z3_bin));
    latch_forward_pin_resolve.addArg("resolve-ir");
    latch_forward_pin_resolve.addFileArg(b.path("luau/fixtures/latch_forward_t2y_place_mid.lifter-ir.json"));
    const latch_forward_pin_ir = latch_forward_pin_resolve.addOutputFileArg("latch-forward-t2y-place-mid.resolved.lifter-ir.json");
    latch_forward_pin_resolve.addArg(if (z3_enabled) "z3" else "internal");
    latch_forward_pin_resolve.expectExitCode(0);
    const latch_forward_pin = b.addRunArtifact(exe);
    latch_forward_pin.addArg("inspect-edge-rewrite");
    latch_forward_pin.addFileArg(latch_forward_pin_ir);
    latch_forward_pin.addArg("0");
    latch_forward_pin.expectStdErrMatch("rewrite=0 source=5 kind=branch_then from=3 to=1 rule=forwarding_jump group=null");
    latch_forward_pin.expectExitCode(0);
    conformance_step.dependOn(&latch_forward_pin.step);
    // The post-split collapse's self-target guard on source-lifted
    // programs. The frontend lowers the body of an empty-body `while` loop to a forwarder whose source is its own
    // header, so the collapse of a targeted normalization writes a self-forward today, split or not: Phase 0 runs on
    // the lifted IR of the two-hang `while` fixture and of a terminating `while step() do end`, and on the resolved IR
    // of a `while k > 100 do end`, whose edge into the body carries a path constraint the self-forward would orphan.
    const latch_forward_source_phase0 = [_]struct { path: []const u8, name: []const u8 }{
        .{ .path = "luau/fixtures/exitless_two_hang_while_source.luau", .name = "latch-forward-guard-two-hang-while" },
        .{ .path = "luau/fixtures/latch_forward_guard_empty_while_source.luau", .name = "latch-forward-guard-empty-while" },
    };
    for (latch_forward_source_phase0) |fixture| {
        const source_phase0 = b.addRunArtifact(exe);
        if (z3_enabled) source_phase0.addPathDir(b.pathFromRoot(z3_bin));
        source_phase0.addArg("normalize-ir-budget");
        source_phase0.addFileArg(addLuauSourceIr(b, fixture.path, null, fixture.name));
        _ = source_phase0.addOutputFileArg(b.fmt("{s}.phase0.lifter-ir.json", .{fixture.name}));
        source_phase0.addArgs(&.{ "1", "0" });
        if (!trace_normalize_phases) source_phase0.expectStdErrEqual("");
        source_phase0.expectExitCode(0);
        conformance_step.dependOn(&source_phase0.step);
    }
    const latch_forward_constraint_resolve = b.addRunArtifact(exe);
    if (z3_enabled) latch_forward_constraint_resolve.addPathDir(b.pathFromRoot(z3_bin));
    latch_forward_constraint_resolve.addArg("resolve-ir");
    latch_forward_constraint_resolve.addFileArg(addLuauSourceIr(b, "luau/fixtures/latch_forward_guard_while_constraint_source.luau", null, "latch-forward-guard-while-constraint"));
    const latch_forward_constraint_ir = latch_forward_constraint_resolve.addOutputFileArg("latch-forward-guard-while-constraint.resolved.lifter-ir.json");
    latch_forward_constraint_resolve.addArg(if (z3_enabled) "z3" else "internal");
    latch_forward_constraint_resolve.expectExitCode(0);
    const latch_forward_constraint_phase0 = b.addRunArtifact(exe);
    if (z3_enabled) latch_forward_constraint_phase0.addPathDir(b.pathFromRoot(z3_bin));
    latch_forward_constraint_phase0.addArg("normalize-ir-budget");
    latch_forward_constraint_phase0.addFileArg(latch_forward_constraint_ir);
    _ = latch_forward_constraint_phase0.addOutputFileArg("latch-forward-guard-while-constraint.phase0.lifter-ir.json");
    latch_forward_constraint_phase0.addArgs(&.{ "1", "0" });
    if (!trace_normalize_phases) latch_forward_constraint_phase0.expectStdErrEqual("");
    latch_forward_constraint_phase0.expectExitCode(0);
    conformance_step.dependOn(&latch_forward_constraint_phase0.step);
    // The same guard on an exact-prepass checkpoint. Resolving the exact branch facts of a source's
    // `while true do end` turns its header into a jump to the empty body, which jumps back, so Phase 0 of a targeted
    // normalization would forward the header's edge into the body onto the header itself.
    const latch_forward_exact_resolve = b.addRunArtifact(exe);
    if (z3_enabled) latch_forward_exact_resolve.addPathDir(b.pathFromRoot(z3_bin));
    latch_forward_exact_resolve.addArg("resolve-exact-control-ir");
    latch_forward_exact_resolve.addFileArg(addLuauSourceIr(b, "luau/fixtures/feedback_decline_iteration_join_min_source.luau", null, "latch-forward-guard-while-true-latch"));
    const latch_forward_exact_ir = latch_forward_exact_resolve.addOutputFileArg("latch-forward-guard-while-true-latch.exact.lifter-ir.json");
    latch_forward_exact_resolve.addArg(if (z3_enabled) "z3" else "internal");
    latch_forward_exact_resolve.expectExitCode(0);
    const latch_forward_exact_phase0 = b.addRunArtifact(exe);
    if (z3_enabled) latch_forward_exact_phase0.addPathDir(b.pathFromRoot(z3_bin));
    latch_forward_exact_phase0.addArg("normalize-ir-budget");
    latch_forward_exact_phase0.addFileArg(latch_forward_exact_ir);
    _ = latch_forward_exact_phase0.addOutputFileArg("latch-forward-guard-while-true-latch.phase0.lifter-ir.json");
    latch_forward_exact_phase0.addArgs(&.{ "1", "0" });
    if (!trace_normalize_phases) latch_forward_exact_phase0.expectStdErrEqual("");
    latch_forward_exact_phase0.expectExitCode(0);
    conformance_step.dependOn(&latch_forward_exact_phase0.step);
    // Author-written IR fixtures in which the structure feedback
    // cannot make function 0 plannable. emit-luau declines that function, writes it flat and emits on both targets;
    // the control, whose functions all plan, keeps an empty stderr. resolve-ir and the decline audit pin the
    // per-function scope on the published IR.
    const feedback_decline_fixtures = [_]struct { path: []const u8, name: []const u8, stderr_match: ?[]const u8 }{
        .{ .path = "luau/fixtures/feedback_decline_or_arm_place.lifter-ir.json", .name = "feedback-decline-or-arm-place", .stderr_match = "normalize decline phase=feedback-unsplittable-collision function=0 " },
        .{ .path = "luau/fixtures/feedback_decline_exitless_place.lifter-ir.json", .name = "feedback-decline-exitless-place", .stderr_match = "normalize decline phase=feedback-unsplittable-collision function=0 " },
        .{ .path = "luau/fixtures/feedback_decline_exitless_local.lifter-ir.json", .name = "feedback-decline-exitless-local", .stderr_match = "normalize decline phase=feedback-clone-limit function=0 " },
        .{ .path = "luau/fixtures/feedback_decline_worker_place.lifter-ir.json", .name = "feedback-decline-worker-place", .stderr_match = "normalize decline phase=feedback-unsplittable-collision function=0 " },
        .{ .path = "luau/fixtures/feedback_decline_worker_local.lifter-ir.json", .name = "feedback-decline-worker-local", .stderr_match = "normalize decline phase=feedback-clone-limit function=0 " },
        .{ .path = "luau/fixtures/feedback_decline_worker_ok.lifter-ir.json", .name = "feedback-decline-worker-ok", .stderr_match = null },
    };
    for (feedback_decline_fixtures) |fixture| {
        addFeedbackDeclineConformance(b, exe, z3_enabled, z3_bin, trace_normalize_phases, conformance_step, b.path(fixture.path), fixture.name, "standard-luau", fixture.stderr_match);
        addFeedbackDeclineConformance(b, exe, z3_enabled, z3_bin, trace_normalize_phases, conformance_step, b.path(fixture.path), b.fmt("{s}-direct-locals", .{fixture.name}), "direct-locals-luau", fixture.stderr_match);
    }
    const feedback_decline_control_ir = addFeedbackDeclineResolve(b, exe, z3_enabled, z3_bin, "luau/fixtures/feedback_decline_worker_ok.lifter-ir.json", "feedback-decline-worker-ok");
    const feedback_decline_audited = [_]struct { path: []const u8, name: []const u8 }{
        .{ .path = "luau/fixtures/feedback_decline_worker_place.lifter-ir.json", .name = "feedback-decline-worker-place" },
        .{ .path = "luau/fixtures/feedback_decline_worker_local.lifter-ir.json", .name = "feedback-decline-worker-local" },
        .{ .path = "luau/fixtures/feedback_decline_worker_ok.lifter-ir.json", .name = "feedback-decline-worker-ok" },
    };
    for (feedback_decline_audited) |fixture| {
        const resolved_ir = if (std.mem.eql(u8, fixture.name, "feedback-decline-worker-ok"))
            feedback_decline_control_ir
        else
            addFeedbackDeclineResolve(b, exe, z3_enabled, z3_bin, fixture.path, fixture.name);
        const decline_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
        decline_audit.addFileArg(b.path("luau/feedback_decline_audit.luau"));
        decline_audit.addArg(fixture.name);
        decline_audit.addFileArg(b.path(fixture.path));
        decline_audit.addFileArg(resolved_ir);
        decline_audit.addFileArg(feedback_decline_control_ir);
        conformance_step.dependOn(&decline_audit.step);
    }
    // Author-written source programs: a numeric for loop whose if leaves the loop into two never-ending branches, one
    // of them holding its own inner for loop. The structure feedback finds no alternative split for the loop's
    // function, so emit-luau declines it and writes it flat. Each program lifts, resolves, validates, emits and runs on
    // both targets (the runtime oracle calls only inputs that return), and emit-luau on the lifted IR prints the
    // decline line.
    const feedback_decline_sources = [_]struct { path: []const u8, name: []const u8 }{
        .{ .path = "luau/fixtures/feedback_decline_iteration_join_source.luau", .name = "feedback-decline-iteration-join" },
        .{ .path = "luau/fixtures/feedback_decline_iteration_join_min_source.luau", .name = "feedback-decline-iteration-join-min" },
    };
    for (feedback_decline_sources) |fixture| {
        const standard = addLuauSourceConformanceForTarget(b, exe, z3_enabled, z3_bin, fixture.path, b.fmt("source-frontend-{s}", .{fixture.name}), "standard-luau");
        standard.addTo(conformance_step);
        addFeedbackDeclineConformance(b, exe, z3_enabled, z3_bin, trace_normalize_phases, conformance_step, standard.input_ir, fixture.name, "standard-luau", "normalize decline phase=feedback-no-alternative function=1 ");
        const direct = addLuauSourceConformanceForTarget(b, exe, z3_enabled, z3_bin, fixture.path, b.fmt("source-frontend-{s}-direct-locals", .{fixture.name}), "direct-locals-luau");
        direct.addTo(conformance_step);
        addFeedbackDeclineConformance(b, exe, z3_enabled, z3_bin, trace_normalize_phases, conformance_step, direct.input_ir, b.fmt("{s}-direct-locals", .{fixture.name}), "direct-locals-luau", "normalize decline phase=feedback-no-alternative function=1 ");
    }
    conformance_step.dependOn(&register_budget_oracle.step);
    dispatcher_local_budget_conformance.addTo(conformance_step);
    dispatcher_generic_budget_conformance.addTo(conformance_step);
    native_loop_register_conformance.addTo(conformance_step);
    conformance_step.dependOn(&compile_check_positive.step);
    conformance_step.dependOn(&compile_check_rejection.step);
    conformance_step.dependOn(&compile_check_preserved_output.step);
    conformance_step.dependOn(&legacy_unchecked_rejection.step);
    conformance_step.dependOn(&legacy_unchecked_preserved_output.step);
    conformance_step.dependOn(&resolve_refusal_audit.step);
    conformance_step.dependOn(&nested_reresolve_audit.step);
    absolute_conformance.addTo(conformance_step);
    function_reference_conformance.addTo(conformance_step);
    dynamic_truthiness_conformance.addTo(conformance_step);
    immutable_closure_conformance.addTo(conformance_step);
    shared_place_conformance.addTo(conformance_step);
    luau_control_conformance.addTo(conformance_step);
    luau_loop_conformance.addTo(conformance_step);
    conformance_step.dependOn(&loop_audit.step);
    luau_numeric_conformance.addTo(conformance_step);
    luau_promotion_conformance.addTo(conformance_step);
    luau_guarded_promotion_conformance.addTo(conformance_step);
    conformance_step.dependOn(&guarded_promotion_audit.step);
    luau_query_promotion_conformance.addTo(conformance_step);
    conformance_step.dependOn(&query_promotion_audit.step);
    luau_closure_conformance.addTo(conformance_step);
    luau_lexical_transfer_conformance.addTo(conformance_step);
    luau_entry_parameter_conformance.addTo(conformance_step);
    luau_expression_depth_conformance.addTo(conformance_step);
    luau_structured_depth_conformance.addTo(conformance_step);
    luau_mixed_entry_vararg_conformance.addTo(conformance_step);
    luau_pack_materialization_conformance.addTo(conformance_step);
    luau_pack_multi_latch_conformance.addTo(conformance_step);
    luau_pack_return_storage_conformance.addTo(conformance_step);
    luau_iteration_exit_transfer_conformance.addTo(conformance_step);
    luau_iteration_break_exit_transfer_conformance.addTo(conformance_step);
    conformance_step.dependOn(iteration_break_exit_transfer_dispatcher);
    luau_iteration_escape_join_exit_conformance.addTo(conformance_step);
    conformance_step.dependOn(iteration_escape_join_exit_dispatcher);
    luau_iteration_dominating_break_exit_conformance.addTo(conformance_step);
    conformance_step.dependOn(iteration_dominating_break_exit_dispatcher);
    luau_iteration_header_entry_conformance.addTo(conformance_step);
    conformance_step.dependOn(iteration_header_entry_dispatcher);
    luau_iteration_continue_completion_conformance.addTo(conformance_step);
    conformance_step.dependOn(iteration_continue_completion_dispatcher);
    luau_iteration_boundary_body_continue_conformance.addTo(conformance_step);
    conformance_step.dependOn(iteration_boundary_body_continue_dispatcher);
    source_frontend_wrapped_local_continue_conformance.addTo(conformance_step);
    conformance_step.dependOn(wrapped_local_continue_dispatcher);
    luau_wrapped_continue_conformance.addTo(conformance_step);
    conformance_step.dependOn(wrapped_continue_dispatcher);
    conformance_step.dependOn(&wrapped_local_continue_layout.step);
    conformance_step.dependOn(&wrapped_continue_layout.step);
    // The structured texts of the arms whose regions are wrapped for a free target: no transfer wrapper only forwards
    // escape flags to the propagation after it, and no wrapper declares a stop flag that nothing sets or reads.
    const transfer_wrapper_audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    transfer_wrapper_audit.addFileArg(b.path("luau/transfer_wrapper_audit.luau"));
    transfer_wrapper_audit.addFileArg(luau_iteration_escape_join_exit_conformance.generated_luau);
    transfer_wrapper_audit.addFileArg(luau_iteration_header_entry_conformance.generated_luau);
    transfer_wrapper_audit.addFileArg(luau_iteration_continue_completion_conformance.generated_luau);
    transfer_wrapper_audit.addFileArg(luau_iteration_boundary_body_continue_conformance.generated_luau);
    transfer_wrapper_audit.addFileArg(source_frontend_wrapped_local_continue_conformance.generated_luau);
    transfer_wrapper_audit.addFileArg(luau_wrapped_continue_conformance.generated_luau);
    transfer_wrapper_audit.addFileArg(luau_loop_owned_exit_flag_conformance.generated_luau);
    transfer_wrapper_audit.addFileArg(luau_iteration_header_forwarder_conformance.generated_luau);
    transfer_wrapper_audit.addFileArg(source_frontend_always_break_transfer_iteration_conformance.generated_luau);
    conformance_step.dependOn(&transfer_wrapper_audit.step);
    luau_loop_owned_exit_flag_conformance.addTo(conformance_step);
    conformance_step.dependOn(loop_owned_exit_flag_dispatcher);
    source_frontend_loop_exit_flag_reentry_conformance.addTo(conformance_step);
    source_frontend_loop_exit_flag_reentry_direct_locals_conformance.addTo(conformance_step);
    conformance_step.dependOn(loop_exit_flag_reentry_dispatcher);
    conformance_step.dependOn(&loop_exit_flag_reentry_layout.step);
    source_frontend_loop_exit_flag_reentry_mid_pass_conformance.addTo(conformance_step);
    source_frontend_loop_exit_flag_reentry_mid_pass_direct_locals_conformance.addTo(conformance_step);
    conformance_step.dependOn(loop_exit_flag_reentry_mid_pass_dispatcher);
    conformance_step.dependOn(&loop_exit_flag_reentry_mid_pass_layout.step);
    source_frontend_nested_continue_side_exit_generic_conformance.addTo(conformance_step);
    conformance_step.dependOn(nested_continue_side_exit_generic_dispatcher);
    conformance_step.dependOn(&nested_continue_side_exit_generic_layout.step);
    source_frontend_nested_continue_side_exit_while_conformance.addTo(conformance_step);
    conformance_step.dependOn(nested_continue_side_exit_while_dispatcher);
    conformance_step.dependOn(&nested_continue_side_exit_while_layout.step);
    source_frontend_nested_continue_side_exit_numeric_conformance.addTo(conformance_step);
    conformance_step.dependOn(nested_continue_side_exit_numeric_dispatcher);
    conformance_step.dependOn(&nested_continue_side_exit_numeric_layout.step);
    source_frontend_nested_continue_side_exit_elseif_conformance.addTo(conformance_step);
    conformance_step.dependOn(nested_continue_side_exit_elseif_dispatcher);
    conformance_step.dependOn(&nested_continue_side_exit_elseif_layout.step);
    source_frontend_nested_continue_side_exit_nested_break_conformance.addTo(conformance_step);
    conformance_step.dependOn(nested_continue_side_exit_nested_break_dispatcher);
    conformance_step.dependOn(&nested_continue_side_exit_nested_break_layout.step);
    luau_iteration_header_forwarder_conformance.addTo(conformance_step);
    conformance_step.dependOn(iteration_header_forwarder_dispatcher);
    luau_open_pack_projection_conformance.addTo(conformance_step);
    luau_closed_pack_discard_conformance.addTo(conformance_step);
    luau_table_conformance.addTo(conformance_step);
    luau_boundary_conformance.addTo(conformance_step);
    luau_path_control_conformance.addTo(conformance_step);
    conformance_step.dependOn(&path_control_audit.step);
    luau_relational_path_control_conformance.addTo(conformance_step);
    conformance_step.dependOn(&relational_path_audit.step);
    luau_chained_path_control_conformance.addTo(conformance_step);
    conformance_step.dependOn(&chained_path_audit.step);
    luau_irreducible_control_conformance.addTo(conformance_step);
    conformance_step.dependOn(&irreducible_control_audit.step);
    conformance_step.dependOn(&irreducible_control_structure_ast.step);
    luau_irreducible_coroutine_conformance.addTo(conformance_step);
    conformance_step.dependOn(&irreducible_coroutine_audit.step);
    conformance_step.dependOn(&irreducible_coroutine_structure_ast.step);
    luau_irreducible_table_conformance.addTo(conformance_step);
    conformance_step.dependOn(&irreducible_table_audit.step);
    conformance_step.dependOn(&irreducible_table_structure_ast.step);
    luau_irreducible_interpolation_conformance.addTo(conformance_step);
    conformance_step.dependOn(&irreducible_interpolation_audit.step);
    conformance_step.dependOn(&irreducible_interpolation_structure_ast.step);
    luau_irreducible_closure_conformance.addTo(conformance_step);
    conformance_step.dependOn(&irreducible_closure_audit.step);
    conformance_step.dependOn(&irreducible_closure_structure_ast.step);
    luau_irreducible_iteration_conformance.addTo(conformance_step);
    conformance_step.dependOn(&irreducible_iteration_audit.step);
    conformance_step.dependOn(&irreducible_iteration_structure_ast.step);
    conformance_step.dependOn(irreducible_iteration_dispatcher);
    source_frontend_conformance.addTo(conformance_step);
    source_frontend_effectful_assignment_conformance.addTo(conformance_step);
    source_frontend_if_conformance.addTo(conformance_step);
    source_frontend_capture_conformance.addTo(conformance_step);
    source_frontend_variadic_conformance.addTo(conformance_step);
    source_frontend_chunk_varargs_conformance.addTo(conformance_step);
    source_frontend_table_conformance.addTo(conformance_step);
    source_frontend_while_conformance.addTo(conformance_step);
    source_frontend_loop_control_conformance.addTo(conformance_step);
    source_frontend_short_circuit_conformance.addTo(conformance_step);
    source_frontend_multi_assignment_conformance.addTo(conformance_step);
    source_frontend_method_conformance.addTo(conformance_step);
    source_frontend_recursive_conformance.addTo(conformance_step);
    source_frontend_repeat_conformance.addTo(conformance_step);
    conformance_step.dependOn(repeat_loop_dispatcher);
    source_frontend_compound_conformance.addTo(conformance_step);
    source_frontend_if_expression_conformance.addTo(conformance_step);
    source_frontend_iteration_capture_conformance.addTo(conformance_step);
    conformance_step.dependOn(per_iteration_capture_dispatcher);
    source_frontend_cell_branch_conformance.addTo(conformance_step);
    conformance_step.dependOn(per_execution_cell_dispatcher_refusal);
    conformance_step.dependOn(per_execution_cell_inherited_flat_refusal);
    conformance_step.dependOn(&per_execution_cell_layout_automatic_audit.step);
    conformance_step.dependOn(&per_execution_cell_layout_dispatcher_audit.step);
    conformance_step.dependOn(per_execution_cell_structured_child_runtime);
    conformance_step.dependOn(per_execution_cell_structured_grandchild_runtime);
    conformance_step.dependOn(numeric_operand_flat_grouping);
    conformance_step.dependOn(numeric_operand_semantic_grouping);
    source_frontend_repeat_header_exit_conformance.addTo(conformance_step);
    source_frontend_repeat_header_exit_direct_locals_conformance.addTo(conformance_step);
    source_frontend_repeat_header_exit_nested_conformance.addTo(conformance_step);
    source_frontend_repeat_header_exit_nested_direct_locals_conformance.addTo(conformance_step);
    source_frontend_repeat_header_exit_while_tail_conformance.addTo(conformance_step);
    source_frontend_repeat_header_exit_while_tail_direct_locals_conformance.addTo(conformance_step);
    source_frontend_typed_block_conformance.addTo(conformance_step);
    source_frontend_numeric_for_conformance.addTo(conformance_step);
    source_frontend_generic_for_conformance.addTo(conformance_step);
    source_frontend_always_return_iteration_conformance.addTo(conformance_step);
    source_frontend_always_return_iteration_in_loop_conformance.addTo(conformance_step);
    source_frontend_always_break_iteration_conformance.addTo(conformance_step);
    source_frontend_always_break_transfer_iteration_conformance.addTo(conformance_step);
    source_frontend_generic_initializer_scope_conformance.addTo(conformance_step);
    source_frontend_generic_initializer_scope_direct_locals_conformance.addTo(conformance_step);
    source_frontend_generic_initializer_scope_storage_conformance.addTo(conformance_step);
    source_frontend_generic_initializer_scope_storage_direct_locals_conformance.addTo(conformance_step);
    source_frontend_generic_initializer_order_conformance.addTo(conformance_step);
    source_frontend_generic_initializer_order_direct_locals_conformance.addTo(conformance_step);
    source_frontend_binary_operand_read_order_conformance.addTo(conformance_step);
    source_frontend_binary_operand_read_order_direct_locals_conformance.addTo(conformance_step);
    source_frontend_proved_branch_unreachable_consumer_conformance.addTo(conformance_step);
    source_frontend_proved_branch_unreachable_consumer_direct_locals_conformance.addTo(conformance_step);
    source_frontend_generic_initializer_read_after_conformance.addTo(conformance_step);
    source_frontend_generic_initializer_read_after_direct_locals_conformance.addTo(conformance_step);
    source_frontend_index_base_read_order_conformance.addTo(conformance_step);
    source_frontend_index_base_read_order_direct_locals_conformance.addTo(conformance_step);
    source_frontend_assignment_target_read_order_conformance.addTo(conformance_step);
    source_frontend_assignment_target_read_order_direct_locals_conformance.addTo(conformance_step);
    source_frontend_compound_table_target_read_order_conformance.addTo(conformance_step);
    source_frontend_compound_table_target_read_order_direct_locals_conformance.addTo(conformance_step);
    source_frontend_multiple_assignment_value_read_order_conformance.addTo(conformance_step);
    source_frontend_multiple_assignment_value_read_order_direct_locals_conformance.addTo(conformance_step);
    source_frontend_multiple_assignment_store_order_conformance.addTo(conformance_step);
    source_frontend_multiple_assignment_store_order_direct_locals_conformance.addTo(conformance_step);
    source_frontend_table_constructor_key_read_order_conformance.addTo(conformance_step);
    source_frontend_table_constructor_key_read_order_direct_locals_conformance.addTo(conformance_step);
    source_frontend_method_receiver_read_order_conformance.addTo(conformance_step);
    source_frontend_method_receiver_read_order_direct_locals_conformance.addTo(conformance_step);
    source_frontend_builtin_fastcall_read_order_conformance.addTo(conformance_step);
    source_frontend_builtin_fastcall_read_order_direct_locals_conformance.addTo(conformance_step);
    source_frontend_builtin_fastcall_optimize0_conformance.addTo(conformance_step);
    source_frontend_builtin_fastcall_optimize0_direct_locals_conformance.addTo(conformance_step);
    conformance_step.dependOn(&source_frontend_builtin_fastcall_optimize2_refusal.step);
    conformance_step.dependOn(&source_frontend_integer_literal_refusal.step);
    source_frontend_table_pack_conformance.addTo(conformance_step);
    source_frontend_function_statement_conformance.addTo(conformance_step);
    source_frontend_closure_store_environment_conformance.addTo(conformance_step);
    source_frontend_closure_store_environment_direct_locals_conformance.addTo(conformance_step);
    source_frontend_closure_store_parenthesized_target_conformance.addTo(conformance_step);
    conformance_step.dependOn(closure_store_parenthesized_target_dispatcher);
    conformance_step.dependOn(closure_store_parenthesized_target_automatic);
    source_frontend_interpolation_conformance.addTo(conformance_step);
    source_frontend_intrinsic_invocation_conformance.addTo(conformance_step);
    source_frontend_coroutine_wrap_conformance.addTo(conformance_step);
    source_frontend_double_rounding_comparison_conformance.addTo(conformance_step);
    source_frontend_double_rounding_comparison_in_range_conformance.addTo(conformance_step);
    source_frontend_wide_integral_number_conformance.addTo(conformance_step);
    source_frontend_exact_number_literal_conformance.addTo(conformance_step);
    for (many_item_conformance) |many_item| many_item.addTo(conformance_step);
    for (nested_constructor_last_item_conformance) |checked| conformance_step.dependOn(checked);
    source_frontend_target_resolution_conformance.addTo(conformance_step);
    source_frontend_opaque_result_target_conformance.addTo(conformance_step);
    source_frontend_nonintrinsic_target_origin_conformance.addTo(conformance_step);
    source_frontend_access_path_target_origin_conformance.addTo(conformance_step);
    source_frontend_dynamic_key_target_origin_conformance.addTo(conformance_step);
    source_frontend_namecall_target_origin_conformance.addTo(conformance_step);
    source_frontend_compositional_access_path_conformance.addTo(conformance_step);
    source_frontend_temporal_target_identity_conformance.addTo(conformance_step);
    ast_admission_compile_conformance.addTo(conformance_step);
    loop_module_compile_conformance.addTo(conformance_step);
    register_budget_module_compile_conformance.addTo(conformance_step);

    const module_tests = b.addTest(.{
        .root_module = module,
    });
    module_tests.stack_size = main_thread_stack_size;
    const run_module_tests = b.addRunArtifact(module_tests);
    if (z3_enabled) run_module_tests.addPathDir(b.pathFromRoot(z3_bin));
    const structure_projection_tests = b.addTest(.{
        .root_module = module,
        .filters = &.{
            "builder consumes arbitrary",
            "raw parameterized numeric join",
            "branching internal SCC boundary clones only its authenticated block",
            "jumping internal SCC boundary clones only its authenticated block",
            "dead pure forwarding boundary clones its one-block projection",
            "authenticated zero-parameter group SCC boundary requires complete replay ownership",
            "complete internal SCC availability roots at the cloned target",
            "effectful terminal continuation replay requires complete authenticated witness",
            "internal loop collision clones a bounded effectful suffix",
            "continuation extension retains a shared effectful jump suffix before iteration handoff",
            "external-use projection rescans definitions added by the first pass",
            "contextual boundary rejects an unprojected shared predecessor",
            "authenticated group carrier path projects a shared predecessor",
            "authenticated group carrier path rejects an unowned ingress before nested clones",
            "authenticated carrier path keeps an alternate edge",
            "authenticated carrier path retains an alternate predecessor",
            "effectful parameterized jump SCC boundary authenticates its tuple",
            "node-split replay restores a consumed branch before reversing clone history",
        },
    });
    const run_structure_projection_tests = b.addRunArtifact(structure_projection_tests);
    if (z3_enabled) run_structure_projection_tests.addPathDir(b.pathFromRoot(z3_bin));
    const structure_projection_test_step = b.step(
        "test-structure-projection",
        "Run the arbitrary-arity continuation projection witness",
    );
    structure_projection_test_step.dependOn(&run_structure_projection_tests.step);

    const parameterized_replay_tests = b.addTest(.{
        .root_module = module,
        .filters = &.{"effectful parameterized replay rebinds distinct"},
    });
    const run_parameterized_replay_tests = b.addRunArtifact(parameterized_replay_tests);
    if (z3_enabled) run_parameterized_replay_tests.addPathDir(b.pathFromRoot(z3_bin));
    const parameterized_replay_test_step = b.step(
        "test-parameterized-replay",
        "Run the distinct-tuple effectful replay witness",
    );
    parameterized_replay_test_step.dependOn(&run_parameterized_replay_tests.step);

    const transparent_forwarding_tests = b.addTest(.{
        .root_module = module,
        .filters = &.{
            "authenticated transparent forwarding preserves parameterized successor tuple",
            "empty zero-parameter forwarder accepts canonical successor tuple",
            "post-apply transparent collapse preserves canonical successor tuple",
            "transparent collapse refuses a non-local successor tuple",
            "failed clone application rolls back graph and rewrite state",
            "transparent empty continuation reuses a different stop",
            "clone fold dominance preflight rolls back an unsafe redirect",
            "clone-fold resume arm reservation is idempotent",
            "clone-fold reservation does not consume a distinct predecessor",
        },
    });
    const run_transparent_forwarding_tests = b.addRunArtifact(transparent_forwarding_tests);
    if (z3_enabled) run_transparent_forwarding_tests.addPathDir(b.pathFromRoot(z3_bin));
    const transparent_forwarding_test_step = b.step(
        "test-transparent-forwarding",
        "Run the parameterized transparent forwarding witness",
    );
    transparent_forwarding_test_step.dependOn(&run_transparent_forwarding_tests.step);

    const cli_tests = b.addTest(.{
        .root_module = exe.root_module,
    });
    const run_cli_tests = b.addRunArtifact(cli_tests);
    if (z3_enabled) run_cli_tests.addPathDir(b.pathFromRoot(z3_bin));

    const proof_attest_tests = b.addTest(.{
        .root_module = proof_attest.root_module,
    });
    const run_proof_attest_tests = b.addRunArtifact(proof_attest_tests);

    const run_validator_tests = addStandaloneTests(b, module, target, optimize, z3_enabled, z3_bin, "src/validate_test.zig");
    const run_emitter_tests = addStandaloneTests(b, module, target, optimize, z3_enabled, z3_bin, "src/emit_luau_test.zig");
    const emitter_test_step = b.step("test-emitter", "Run Luau emitter tests");
    emitter_test_step.dependOn(&run_emitter_tests.step);
    const run_semantics_tests = addStandaloneTests(b, module, target, optimize, z3_enabled, z3_bin, "src/validate_semantics_test.zig");
    const run_structure_tests = addStandaloneTests(b, module, target, optimize, z3_enabled, z3_bin, "src/structure_test.zig");
    const structure_internal_module = b.createModule(.{
        .root_source_file = b.path("src/structure.zig"),
        .target = target,
        .optimize = optimize,
    });
    structure_internal_module.addOptions("build_options", build_options);
    const structure_internal_tests = b.addTest(.{
        .root_module = structure_internal_module,
        .filters = &.{
            "independent zero-parameter loop reentry requires one authenticated entry",
            "effectful zero-parameter prefix replay requires an authenticated SCC",
            "parameterized stop replay rejects non-carried continuation values",
            "same-entry parameterized prefix replay requires a semantic handoff",
            "same-entry numeric reentry accepts contextual state without a node split",
            "same-SCC numeric reentry requires an authenticated loop-carried tuple",
            "nonempty prefix reuses an authenticated same-SCC parameterized branch",
        },
    });
    const run_structure_internal_tests = b.addRunArtifact(structure_internal_tests);
    if (z3_enabled) run_structure_internal_tests.addPathDir(b.pathFromRoot(z3_bin));
    const structure_internal_test_step = b.step(
        "test-structure-internal",
        "Run internal structural replay witnesses",
    );
    structure_internal_test_step.dependOn(&run_structure_internal_tests.step);
    const one_parameter_continuation_tests = b.addTest(.{
        .root_module = module,
        .filters = &.{"one-parameter continuation witness"},
    });
    const run_one_parameter_continuation_tests = b.addRunArtifact(one_parameter_continuation_tests);
    if (z3_enabled) run_one_parameter_continuation_tests.addPathDir(b.pathFromRoot(z3_bin));
    const run_terminal_loop_structure_tests = addStandaloneTests(b, module, target, optimize, z3_enabled, z3_bin, "src/terminal_loop_structure_test.zig");
    const structure_test_step = b.step("test-structure", "Run focused structural reconstruction tests");
    structure_test_step.dependOn(&run_structure_tests.step);
    structure_test_step.dependOn(&run_structure_internal_tests.step);
    structure_test_step.dependOn(&run_one_parameter_continuation_tests.step);
    const run_generated_lexical_oracle_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_generated_lexical_oracle_tests.addFileArg(b.path("luau/generated_lexical_oracle.luau"));
    run_generated_lexical_oracle_tests.addArg("self-test");
    run_generated_lexical_oracle_tests.addFileArg(.{ .cwd_relative = luauAnalyzeExe(b) });
    _ = run_generated_lexical_oracle_tests.addOutputFileArg("generated-lexical-oracle-source.luau");
    _ = run_generated_lexical_oracle_tests.addOutputFileArg("generated-lexical-oracle-negative.luau");
    const run_luau_ir_typecheck = b.addSystemCommand(&.{luauAnalyzeExe(b)});
    run_luau_ir_typecheck.addFileArg(b.path("luau/lifter_ir.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_frontend_outcome.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_local_binding.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_local_identity.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_lexical_scope.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_runtime_context.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_expression_slots.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_expression_scalar.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_expression_scalar_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_statement_slots.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_admission.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/json_exact.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_admission_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_local_identity_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_frontend_control.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_frontend_iteration.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_frontend_expressions.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_frontend_tables.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_frontend_operator_domains.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_frontend_place_domains.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/source_domain_fixed_point_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/intrinsic_bindings.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/invocation_frame.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/target_origin_expression_matcher.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/target_origin_return_selector.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/target_origin_matcher.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/structured_definition_sets.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_alias_graph.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_callee_resolver.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_invocation_flow.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_source_index.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_target_identity.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_test_support.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_invocation_test_support.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/direct_closure_return_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/local_function_return_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/conditional_factory_return_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/fixed_vararg_return_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/local_factory_return_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/local_factory_alias_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/statement_factory_return_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/parameter_factory_call_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_target_identity_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_future_write_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_assignment_commit_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_for_header_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_guard_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_immediate_invocation_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_invocation_chain_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_invocation_capture_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_invocation_set_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_invocation_fanout_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_nested_invocation_set_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_invocation_kill_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_invocation_definition_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_loop_fixed_point_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_loop_phase_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/temporal_loop_transfer_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/target_recovery.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/target_result_contracts.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/target_result_contract_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/target_proof_bundle.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/target_proof_bundle_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/closure_target_recovery_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/recovery_admission.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/recovery_admission_test.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/recovery_manifest.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_target_recovery.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/ast_frontend.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/iteration_exit_transfer_runtime_oracle.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/iteration_break_exit_transfer_runtime_oracle.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/iteration_header_entry_runtime_oracle.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/wrapped_continue_runtime_oracle.luau"));
    run_luau_ir_typecheck.addFileArg(b.path("luau/loop_owned_exit_flag_runtime_oracle.luau"));
    run_luau_ir_typecheck.addFileInput(b.path("luau/json_codec.luau"));
    const run_frontend_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_frontend_tests.addFileArg(b.path("luau/frontend_contract_test.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_local_binding.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_local_identity.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_lexical_scope.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_runtime_context.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_expression_slots.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_expression_scalar.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_statement_slots.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_admission.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_target_recovery.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_frontend.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_frontend_outcome.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_frontend_expressions.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_frontend_tables.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_frontend_operator_domains.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_frontend_place_domains.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_frontend_control.luau"));
    run_frontend_tests.addFileInput(b.path("luau/ast_frontend_iteration.luau"));
    run_frontend_tests.addFileInput(b.path("luau/source_domain_fixed_point_test.luau"));
    run_frontend_tests.addFileInput(b.path("luau/intrinsic_bindings.luau"));
    run_frontend_tests.addFileInput(b.path("luau/recovery_admission.luau"));
    addTemporalIdentityInputs(b, run_frontend_tests);
    run_frontend_tests.addFileInput(b.path("luau/target_recovery.luau"));
    run_frontend_tests.addFileInput(b.path("luau/target_result_contracts.luau"));
    run_frontend_tests.addFileInput(b.path("luau/target_proof_bundle.luau"));
    run_frontend_tests.addFileInput(b.path("luau/lifter_ir.luau"));
    run_frontend_tests.addFileInput(b.path("luau/json_codec.luau"));
    const run_recovery_manifest_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_recovery_manifest_tests.addFileArg(b.path("luau/recovery_manifest_test.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/recovery_admission_test.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/target_origin_contract_test.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/closure_target_recovery_test.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_local_binding.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_local_identity.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_lexical_scope.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_runtime_context.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_expression_slots.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_expression_scalar.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_statement_slots.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_admission.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_target_recovery.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/namecall_target_recovery_test.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/access_path_target_recovery_test.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/recovery_manifest.luau"));
    addTemporalIdentityInputs(b, run_recovery_manifest_tests);
    run_recovery_manifest_tests.addFileInput(b.path("luau/target_recovery.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/target_result_contracts.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/target_result_contract_test.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/temporal_test_support.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/target_proof_bundle.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_frontend.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_frontend_outcome.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_frontend_expressions.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_frontend_tables.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_frontend_operator_domains.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_frontend_place_domains.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_frontend_control.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/ast_frontend_iteration.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/intrinsic_bindings.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/recovery_admission.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/lifter_ir.luau"));
    run_recovery_manifest_tests.addFileInput(b.path("luau/json_codec.luau"));
    const run_target_proof_bundle_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_target_proof_bundle_tests.addFileArg(b.path("luau/target_proof_bundle_test.luau"));
    run_target_proof_bundle_tests.addFileInput(b.path("luau/target_proof_bundle.luau"));
    run_target_proof_bundle_tests.addFileInput(b.path("luau/target_recovery.luau"));
    run_target_proof_bundle_tests.addFileInput(b.path("luau/target_result_contracts.luau"));
    run_target_proof_bundle_tests.addFileInput(b.path("luau/recovery_manifest.luau"));
    run_target_proof_bundle_tests.addFileInput(b.path("luau/lifter_ir.luau"));
    run_target_proof_bundle_tests.addFileInput(b.path("luau/intrinsic_bindings.luau"));
    run_target_proof_bundle_tests.addFileInput(b.path("luau/recovery_admission.luau"));
    addTemporalIdentityInputs(b, run_target_proof_bundle_tests);
    const run_ast_admission_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_ast_admission_tests.addFileArg(b.path("luau/ast_admission_test.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_local_binding.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_local_identity.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_lexical_scope.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_runtime_context.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_expression_slots.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_expression_scalar.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_expression_scalar_test.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_statement_slots.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_local_identity_test.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_admission.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_target_recovery.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_frontend.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_frontend_outcome.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_frontend_expressions.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_frontend_tables.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_frontend_operator_domains.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_frontend_place_domains.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_frontend_control.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/ast_frontend_iteration.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/intrinsic_bindings.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/recovery_admission.luau"));
    addTemporalIdentityInputs(b, run_ast_admission_tests);
    run_ast_admission_tests.addFileInput(b.path("luau/target_recovery.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/target_result_contracts.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/target_proof_bundle.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/lifter_ir.luau"));
    run_ast_admission_tests.addFileInput(b.path("luau/json_codec.luau"));
    const run_parser_number_transport_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_parser_number_transport_tests.addFileArg(b.path("luau/parser_number_transport_test.luau"));
    run_parser_number_transport_tests.addFileInput(b.path("luau/ast_admission.luau"));
    run_parser_number_transport_tests.addFileInput(b.path("luau/ast_expression_scalar.luau"));
    run_parser_number_transport_tests.addFileInput(b.path("luau/ast_expression_slots.luau"));
    run_parser_number_transport_tests.addFileInput(b.path("luau/ast_lexical_scope.luau"));
    run_parser_number_transport_tests.addFileInput(b.path("luau/ast_local_binding.luau"));
    run_parser_number_transport_tests.addFileInput(b.path("luau/ast_local_identity.luau"));
    run_parser_number_transport_tests.addFileInput(b.path("luau/ast_runtime_context.luau"));
    run_parser_number_transport_tests.addFileInput(b.path("luau/ast_statement_slots.luau"));
    run_parser_number_transport_tests.addFileInput(b.path("luau/invocation_frame.luau"));
    run_parser_number_transport_tests.addFileInput(b.path("luau/target_origin_expression_matcher.luau"));
    const run_json_exact_transport_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_json_exact_transport_tests.addFileArg(b.path("luau/json_exact_transport_test.luau"));
    run_json_exact_transport_tests.addFileInput(b.path("luau/json_exact.luau"));
    const run_exact_number_handoff_lift = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_exact_number_handoff_lift.addFileArg(b.path("frontends/disassembly/lift_compiler_disassembly.luau"));
    run_exact_number_handoff_lift.addFileArg(b.path("luau/fixtures/exact_number_handoff.json"));
    const exact_number_handoff_ir = run_exact_number_handoff_lift.addOutputFileArg("exact-number-handoff.lifter-ir.json");
    run_exact_number_handoff_lift.addArg("exact-number-handoff");
    run_exact_number_handoff_lift.addFileInput(b.path("luau/lifter_ir.luau"));
    run_exact_number_handoff_lift.addFileInput(b.path("luau/json_codec.luau"));
    run_exact_number_handoff_lift.addFileInput(b.path("luau/json_exact.luau"));
    const run_handoff_number_transport_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_handoff_number_transport_tests.addFileArg(b.path("luau/handoff_number_transport_test.luau"));
    run_handoff_number_transport_tests.addFileArg(b.path("luau/fixtures/exact_number_handoff.json"));
    run_handoff_number_transport_tests.addFileArg(exact_number_handoff_ir);
    const run_temporal_target_identity_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_target_identity_tests.addFileArg(b.path("luau/temporal_target_identity_test.luau"));
    addTemporalTestInputs(b, run_temporal_target_identity_tests);
    const run_direct_closure_return_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_direct_closure_return_tests.addFileArg(b.path("luau/direct_closure_return_test.luau"));
    run_direct_closure_return_tests.addFileInput(b.path("luau/local_function_return_test.luau"));
    run_direct_closure_return_tests.addFileInput(b.path("luau/conditional_factory_return_test.luau"));
    addTemporalTestInputs(b, run_direct_closure_return_tests);
    const run_fixed_vararg_return_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_fixed_vararg_return_tests.addFileArg(b.path("luau/fixed_vararg_return_test.luau"));
    addTemporalTestInputs(b, run_fixed_vararg_return_tests);
    const run_local_factory_return_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_local_factory_return_tests.addFileArg(b.path("luau/local_factory_return_test.luau"));
    addTemporalTestInputs(b, run_local_factory_return_tests);
    const run_local_factory_alias_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_local_factory_alias_tests.addFileArg(b.path("luau/local_factory_alias_test.luau"));
    addTemporalTestInputs(b, run_local_factory_alias_tests);
    const run_statement_factory_return_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_statement_factory_return_tests.addFileArg(b.path("luau/statement_factory_return_test.luau"));
    addTemporalTestInputs(b, run_statement_factory_return_tests);
    const run_parameter_factory_call_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_parameter_factory_call_tests.addFileArg(b.path("luau/parameter_factory_call_test.luau"));
    addTemporalTestInputs(b, run_parameter_factory_call_tests);
    const run_temporal_future_write_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_future_write_tests.addFileArg(b.path("luau/temporal_future_write_test.luau"));
    addTemporalTestInputs(b, run_temporal_future_write_tests);
    const run_temporal_assignment_commit_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_assignment_commit_tests.addFileArg(b.path("luau/temporal_assignment_commit_test.luau"));
    addTemporalTestInputs(b, run_temporal_assignment_commit_tests);
    const run_temporal_for_header_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_for_header_tests.addFileArg(b.path("luau/temporal_for_header_test.luau"));
    addTemporalTestInputs(b, run_temporal_for_header_tests);
    const run_temporal_guard_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_guard_tests.addFileArg(b.path("luau/temporal_guard_test.luau"));
    addTemporalTestInputs(b, run_temporal_guard_tests);
    const run_temporal_immediate_invocation_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_immediate_invocation_tests.addFileArg(b.path("luau/temporal_immediate_invocation_test.luau"));
    addTemporalTestInputs(b, run_temporal_immediate_invocation_tests);
    run_temporal_immediate_invocation_tests.addFileInput(b.path("luau/target_recovery.luau"));
    run_temporal_immediate_invocation_tests.addFileInput(b.path("luau/target_result_contracts.luau"));
    run_temporal_immediate_invocation_tests.addFileInput(b.path("luau/recovery_admission.luau"));
    run_temporal_immediate_invocation_tests.addFileInput(b.path("luau/target_proof_bundle.luau"));
    const run_temporal_invocation_chain_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_invocation_chain_tests.addFileArg(b.path("luau/temporal_invocation_chain_test.luau"));
    addTemporalTestInputs(b, run_temporal_invocation_chain_tests);
    const run_temporal_invocation_capture_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_invocation_capture_tests.addFileArg(b.path("luau/temporal_invocation_capture_test.luau"));
    addTemporalTestInputs(b, run_temporal_invocation_capture_tests);
    const run_temporal_invocation_set_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_invocation_set_tests.addFileArg(b.path("luau/temporal_invocation_set_test.luau"));
    addTemporalTestInputs(b, run_temporal_invocation_set_tests);
    const run_temporal_invocation_fanout_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_invocation_fanout_tests.addFileArg(b.path("luau/temporal_invocation_fanout_test.luau"));
    addTemporalTestInputs(b, run_temporal_invocation_fanout_tests);
    const run_temporal_nested_invocation_set_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_nested_invocation_set_tests.addFileArg(b.path("luau/temporal_nested_invocation_set_test.luau"));
    addTemporalTestInputs(b, run_temporal_nested_invocation_set_tests);
    const run_temporal_invocation_kill_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_invocation_kill_tests.addFileArg(b.path("luau/temporal_invocation_kill_test.luau"));
    addTemporalTestInputs(b, run_temporal_invocation_kill_tests);
    const run_temporal_invocation_definition_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_invocation_definition_tests.addFileArg(b.path("luau/temporal_invocation_definition_test.luau"));
    addTemporalTestInputs(b, run_temporal_invocation_definition_tests);
    const run_temporal_loop_fixed_point_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_loop_fixed_point_tests.addFileArg(b.path("luau/temporal_loop_fixed_point_test.luau"));
    addTemporalTestInputs(b, run_temporal_loop_fixed_point_tests);
    const run_temporal_loop_phase_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_loop_phase_tests.addFileArg(b.path("luau/temporal_loop_phase_test.luau"));
    addTemporalTestInputs(b, run_temporal_loop_phase_tests);
    const run_temporal_loop_transfer_tests = b.addSystemCommand(&.{ luneExe(b), "run" });
    run_temporal_loop_transfer_tests.addFileArg(b.path("luau/temporal_loop_transfer_test.luau"));
    addTemporalTestInputs(b, run_temporal_loop_transfer_tests);

    const run_disassembly_adapter_tests = b.addSystemCommand(&.{ nodeExe(b), "--test" });
    run_disassembly_adapter_tests.addFileArg(b.path("frontends/disassembly/compiler_disassembly_adapter.test.mjs"));
    run_disassembly_adapter_tests.addFileInput(b.path("frontends/disassembly/compiler_disassembly_adapter.mjs"));
    const disassembly_test_step = b.step("test-disassembly", "Run the compiler-disassembly adapter tests under Node");
    disassembly_test_step.dependOn(&run_disassembly_adapter_tests.step);

    const test_step = b.step("test", "Run semantic lifter tests");
    test_step.dependOn(&run_module_tests.step);
    test_step.dependOn(&run_cli_tests.step);
    test_step.dependOn(&run_proof_attest_tests.step);
    test_step.dependOn(&run_validator_tests.step);
    test_step.dependOn(&run_emitter_tests.step);
    test_step.dependOn(&run_semantics_tests.step);
    test_step.dependOn(&run_structure_tests.step);
    test_step.dependOn(&run_terminal_loop_structure_tests.step);
    test_step.dependOn(&run_generated_lexical_oracle_tests.step);
    test_step.dependOn(&run_luau_ir_typecheck.step);
    test_step.dependOn(&run_frontend_tests.step);
    test_step.dependOn(&run_disassembly_adapter_tests.step);
    test_step.dependOn(&run_recovery_manifest_tests.step);
    test_step.dependOn(&run_target_proof_bundle_tests.step);
    test_step.dependOn(&run_ast_admission_tests.step);
    test_step.dependOn(&run_parser_number_transport_tests.step);
    test_step.dependOn(&run_json_exact_transport_tests.step);
    test_step.dependOn(&run_handoff_number_transport_tests.step);
    test_step.dependOn(&run_temporal_target_identity_tests.step);
    test_step.dependOn(&run_direct_closure_return_tests.step);
    test_step.dependOn(&run_fixed_vararg_return_tests.step);
    test_step.dependOn(&run_local_factory_return_tests.step);
    test_step.dependOn(&run_local_factory_alias_tests.step);
    test_step.dependOn(&run_statement_factory_return_tests.step);
    test_step.dependOn(&run_parameter_factory_call_tests.step);
    test_step.dependOn(&run_temporal_future_write_tests.step);
    test_step.dependOn(&run_temporal_assignment_commit_tests.step);
    test_step.dependOn(&run_temporal_for_header_tests.step);
    test_step.dependOn(&run_temporal_guard_tests.step);
    test_step.dependOn(&run_temporal_immediate_invocation_tests.step);
    test_step.dependOn(&run_temporal_invocation_chain_tests.step);
    test_step.dependOn(&run_temporal_invocation_capture_tests.step);
    test_step.dependOn(&run_temporal_invocation_set_tests.step);
    test_step.dependOn(&run_temporal_invocation_fanout_tests.step);
    test_step.dependOn(&run_temporal_nested_invocation_set_tests.step);
    test_step.dependOn(&run_temporal_invocation_kill_tests.step);
    test_step.dependOn(&run_temporal_invocation_definition_tests.step);
    test_step.dependOn(&run_temporal_loop_fixed_point_tests.step);
    test_step.dependOn(&run_temporal_loop_phase_tests.step);
    test_step.dependOn(&run_temporal_loop_transfer_tests.step);
    if (z3_enabled) {
        const run_z3_tests = addStandaloneTests(b, module, target, optimize, true, z3_bin, "src/z3_backend_test.zig");
        test_step.dependOn(&run_z3_tests.step);
    }
}

fn addRegisterBudgetOracle(b: *std.Build) *std.Build.Step.Run {
    const command = b.addSystemCommand(&.{ luneExe(b), "run" });
    command.addFileArg(b.path("luau/register_budget_oracle.luau"));
    command.addFileArg(.{ .cwd_relative = luauCompileExe(b) });
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
    runtime_command.addFileInput(b.path("luau/iteration_break_exit_transfer_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/iteration_header_entry_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/wrapped_continue_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/loop_owned_exit_flag_runtime_oracle.luau"));
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
    command.addFileArg(.{ .cwd_relative = luauAnalyzeExe(b) });
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

const DispatcherLocalBudgetConformance = struct {
    automatic_compile: *std.Build.Step,
    dispatcher_refusal: *std.Build.Step,
    boundary_compile: *std.Build.Step,

    fn addTo(self: DispatcherLocalBudgetConformance, step: *std.Build.Step) void {
        step.dependOn(self.automatic_compile);
        step.dependOn(self.dispatcher_refusal);
        step.dependOn(self.boundary_compile);
    }
};

// The forced-dispatcher layout is budgeted at emission admission.
// The 192-local fixture emits under `automatic` (structured, O0-compilable) but
// is refused under `dispatcher` (flat layout = 201 locals > 200); the 191-local
// sibling pins the boundary (200 locals, dispatcher accepted and O0-compilable).
fn addDispatcherLocalBudgetConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
) DispatcherLocalBudgetConformance {
    const engine = if (z3_enabled) "z3" else "internal";

    const json_192 = addLuauSourceIr(b, "luau/fixtures/dispatcher_local_budget_source.luau", null, "dispatcher-local-budget");
    const resolve_192 = b.addRunArtifact(exe);
    if (z3_enabled) resolve_192.addPathDir(b.pathFromRoot(z3_bin));
    resolve_192.addArg("resolve-ir");
    resolve_192.addFileArg(json_192);
    const resolved_192 = resolve_192.addOutputFileArg("dispatcher-local-budget.resolved.lifter-ir.json");
    resolve_192.addArg(engine);

    const emit_192_automatic = b.addRunArtifact(exe);
    if (z3_enabled) emit_192_automatic.addPathDir(b.pathFromRoot(z3_bin));
    emit_192_automatic.addArg("emit-readable-luau-strategy");
    emit_192_automatic.addFileArg(resolved_192);
    const luau_192_automatic = emit_192_automatic.addOutputFileArg("dispatcher-local-budget.automatic.luau");
    emit_192_automatic.addArgs(&.{ "standard-luau", "automatic" });
    emit_192_automatic.expectExitCode(0);

    const compile_192_automatic = b.addSystemCommand(&.{ luauCompileExe(b), "--null", "-O0" });
    compile_192_automatic.addFileArg(luau_192_automatic);
    compile_192_automatic.expectExitCode(0);

    const emit_192_dispatcher = b.addRunArtifact(exe);
    if (z3_enabled) emit_192_dispatcher.addPathDir(b.pathFromRoot(z3_bin));
    emit_192_dispatcher.addArg("emit-readable-luau-strategy");
    emit_192_dispatcher.addFileArg(resolved_192);
    const dispatcher_192_seed_files = b.addWriteFiles();
    const dispatcher_192_seed = dispatcher_192_seed_files.add("dispatcher-local-budget.dispatcher.luau", "");
    emit_192_dispatcher.addFileArg(dispatcher_192_seed);
    emit_192_dispatcher.addArgs(&.{ "standard-luau", "dispatcher" });
    emit_192_dispatcher.expectExitCode(1);
    emit_192_dispatcher.expectStdErrMatch("diagnostic=unsupported_readable_register_pressure entity=1\n");

    const json_191 = addLuauSourceIr(b, "luau/fixtures/dispatcher_local_budget_191_source.luau", null, "dispatcher-local-budget-191");
    const resolve_191 = b.addRunArtifact(exe);
    if (z3_enabled) resolve_191.addPathDir(b.pathFromRoot(z3_bin));
    resolve_191.addArg("resolve-ir");
    resolve_191.addFileArg(json_191);
    const resolved_191 = resolve_191.addOutputFileArg("dispatcher-local-budget-191.resolved.lifter-ir.json");
    resolve_191.addArg(engine);

    const emit_191_dispatcher = b.addRunArtifact(exe);
    if (z3_enabled) emit_191_dispatcher.addPathDir(b.pathFromRoot(z3_bin));
    emit_191_dispatcher.addArg("emit-readable-luau-strategy");
    emit_191_dispatcher.addFileArg(resolved_191);
    const luau_191_dispatcher = emit_191_dispatcher.addOutputFileArg("dispatcher-local-budget-191.dispatcher.luau");
    emit_191_dispatcher.addArgs(&.{ "standard-luau", "dispatcher" });
    emit_191_dispatcher.expectExitCode(0);

    const compile_191_dispatcher = b.addSystemCommand(&.{ luauCompileExe(b), "--null", "-O0" });
    compile_191_dispatcher.addFileArg(luau_191_dispatcher);
    compile_191_dispatcher.expectExitCode(0);

    return .{
        .automatic_compile = &compile_192_automatic.step,
        .dispatcher_refusal = &emit_192_dispatcher.step,
        .boundary_compile = &compile_191_dispatcher.step,
    };
}

const DispatcherGenericBudgetConformance = struct {
    local_automatic_compile: *std.Build.Step,
    local_dispatcher_refusal: *std.Build.Step,
    local_boundary_compile: *std.Build.Step,
    register_dispatcher_refusal: *std.Build.Step,
    register_boundary_compile: *std.Build.Step,

    fn addTo(self: DispatcherGenericBudgetConformance, step: *std.Build.Step) void {
        step.dependOn(self.local_automatic_compile);
        step.dependOn(self.local_dispatcher_refusal);
        step.dependOn(self.local_boundary_compile);
        step.dependOn(self.register_dispatcher_refusal);
        step.dependOn(self.register_boundary_compile);
    }
};

// A flat function holding a generic
// transition is budgeted for the transition's five private locals and its iterator call frame.
// The 200-root-local fixture is refused under `dispatcher` (205 locals > 200) and emitted under
// `automatic`; its 195-local sibling pins the local boundary (200 locals, dispatcher accepted and
// O0-compilable). The 82-target fixture is refused (90 + 3 + 2 x 82 = 257 registers > 255); its
// 81-target sibling pins the register boundary (254 registers, accepted and O0-compilable).
fn addDispatcherGenericBudgetConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
) DispatcherGenericBudgetConformance {
    const local_resolved = addGenericBudgetResolvedIr(b, exe, z3_enabled, z3_bin, "luau/fixtures/dispatcher_generic_local_budget_source.luau", "dispatcher-generic-local-budget");
    const local_automatic = b.addRunArtifact(exe);
    if (z3_enabled) local_automatic.addPathDir(b.pathFromRoot(z3_bin));
    local_automatic.addArg("emit-readable-luau-strategy");
    local_automatic.addFileArg(local_resolved);
    const local_automatic_luau = local_automatic.addOutputFileArg("dispatcher-generic-local-budget.automatic.luau");
    local_automatic.addArgs(&.{ "standard-luau", "automatic" });
    local_automatic.expectExitCode(0);
    const local_automatic_compile = b.addSystemCommand(&.{ luauCompileExe(b), "--null", "-O0" });
    local_automatic_compile.addFileArg(local_automatic_luau);
    local_automatic_compile.expectExitCode(0);
    const local_refusal = addGenericBudgetRefusal(b, exe, z3_enabled, z3_bin, local_resolved, "dispatcher-generic-local-budget.dispatcher.luau", "diagnostic=unsupported_readable_register_pressure entity=1\n");

    const local_boundary_resolved = addGenericBudgetResolvedIr(b, exe, z3_enabled, z3_bin, "luau/fixtures/dispatcher_generic_local_budget_170_source.luau", "dispatcher-generic-local-budget-170");
    const local_boundary_compile = addGenericBudgetBoundary(b, exe, z3_enabled, z3_bin, local_boundary_resolved, "dispatcher-generic-local-budget-170.dispatcher.luau");

    const register_resolved = addGenericBudgetResolvedIr(b, exe, z3_enabled, z3_bin, "luau/fixtures/dispatcher_generic_register_budget_source.luau", "dispatcher-generic-register-budget");
    const register_refusal = addGenericBudgetRefusal(b, exe, z3_enabled, z3_bin, register_resolved, "dispatcher-generic-register-budget.dispatcher.luau", "diagnostic=unsupported_readable_temporary_register_pressure entity=1\n");

    const register_boundary_resolved = addGenericBudgetResolvedIr(b, exe, z3_enabled, z3_bin, "luau/fixtures/dispatcher_generic_register_budget_81_source.luau", "dispatcher-generic-register-budget-81");
    const register_boundary_compile = addGenericBudgetBoundary(b, exe, z3_enabled, z3_bin, register_boundary_resolved, "dispatcher-generic-register-budget-81.dispatcher.luau");

    return .{
        .local_automatic_compile = &local_automatic_compile.step,
        .local_dispatcher_refusal = local_refusal,
        .local_boundary_compile = local_boundary_compile,
        .register_dispatcher_refusal = register_refusal,
        .register_boundary_compile = register_boundary_compile,
    };
}

fn addGenericBudgetResolvedIr(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    source_path: []const u8,
    fixture_name: []const u8,
) std.Build.LazyPath {
    const json = addLuauSourceIr(b, source_path, null, fixture_name);
    const resolve = b.addRunArtifact(exe);
    if (z3_enabled) resolve.addPathDir(b.pathFromRoot(z3_bin));
    resolve.addArg("resolve-ir");
    resolve.addFileArg(json);
    const resolved = resolve.addOutputFileArg(b.fmt("{s}.resolved.lifter-ir.json", .{fixture_name}));
    resolve.addArg(if (z3_enabled) "z3" else "internal");
    return resolved;
}

fn addGenericBudgetRefusal(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    resolved: std.Build.LazyPath,
    seed_name: []const u8,
    stderr_match: []const u8,
) *std.Build.Step {
    const emit = b.addRunArtifact(exe);
    if (z3_enabled) emit.addPathDir(b.pathFromRoot(z3_bin));
    emit.addArg("emit-readable-luau-strategy");
    emit.addFileArg(resolved);
    const seed_files = b.addWriteFiles();
    emit.addFileArg(seed_files.add(seed_name, ""));
    emit.addArgs(&.{ "standard-luau", "dispatcher" });
    emit.expectExitCode(1);
    emit.expectStdErrMatch(stderr_match);
    return &emit.step;
}

fn addGenericBudgetBoundary(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    resolved: std.Build.LazyPath,
    output_name: []const u8,
) *std.Build.Step {
    const emit = b.addRunArtifact(exe);
    if (z3_enabled) emit.addPathDir(b.pathFromRoot(z3_bin));
    emit.addArg("emit-readable-luau-strategy");
    emit.addFileArg(resolved);
    const emitted = emit.addOutputFileArg(output_name);
    emit.addArgs(&.{ "standard-luau", "dispatcher" });
    emit.expectExitCode(0);
    const compile = b.addSystemCommand(&.{ luauCompileExe(b), "--null", "-O0" });
    compile.addFileArg(emitted);
    compile.expectExitCode(0);
    return &compile.step;
}

// Author-written chains at the edge of the readable certificates (luau/native_loop_register_conformance.luau):
// nested native loops and nested one-shot native loops whose `for` frames and completion locals fill the
// 255-register frame, and an escape chain whose transfer wrappers fill the syntax budget. At the refused depth the
// readable admission reports the diagnostic; one level shallower (200 arms for the escape chain) the chain is
// admitted, emitted and compiled at the pinned compiler's default options, the options of the checked emission.
// The two one-shot chains are also emitted in direct locals, without value storage, where their header parameters
// are still aliases that no local counts: at the refused depth that emission is refused with the diagnostic (the
// emitter writes no output, so the output argument is an empty seed file); one level shallower it is compiled.
const NativeLoopRegisterConformance = struct {
    steps: [16]*std.Build.Step,

    fn addTo(self: NativeLoopRegisterConformance, step: *std.Build.Step) void {
        for (self.steps) |checked| step.dependOn(checked);
    }
};

fn addNativeLoopRegisterConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
) NativeLoopRegisterConformance {
    const Arm = struct { shape: []const u8, refused: []const u8, admitted: []const u8, diagnostic: []const u8, direct_locals: bool = false };
    const arms = [_]Arm{
        .{ .shape = "frame_chain", .refused = "83", .admitted = "82", .diagnostic = "unsupported_readable_temporary_register_pressure" },
        .{ .shape = "generic_chain", .refused = "50", .admitted = "49", .diagnostic = "unsupported_readable_temporary_register_pressure" },
        .{ .shape = "completion_chain", .refused = "62", .admitted = "61", .diagnostic = "unsupported_readable_temporary_register_pressure" },
        .{ .shape = "acyclic_chain", .refused = "83", .admitted = "82", .diagnostic = "unsupported_readable_temporary_register_pressure", .direct_locals = true },
        .{ .shape = "acyclic_generic_chain", .refused = "50", .admitted = "49", .diagnostic = "unsupported_readable_temporary_register_pressure", .direct_locals = true },
        .{ .shape = "escape_chain", .refused = "300", .admitted = "200", .diagnostic = "unsupported_readable_syntax_depth" },
    };
    var result: NativeLoopRegisterConformance = undefined;
    var next: usize = 0;
    for (arms) |arm| {
        const refused_ir = addNativeLoopRegisterResolvedIr(b, exe, z3_enabled, z3_bin, arm.shape, arm.refused);
        const admitted_ir = addNativeLoopRegisterResolvedIr(b, exe, z3_enabled, z3_bin, arm.shape, arm.admitted);

        const refusal = b.addRunArtifact(exe);
        if (z3_enabled) refusal.addPathDir(b.pathFromRoot(z3_bin));
        refusal.addArg("expect-diagnostic");
        refusal.addFileArg(refused_ir);
        refusal.addArgs(&.{ "readable-luau", arm.diagnostic });
        refusal.expectExitCode(0);
        result.steps[next] = &refusal.step;

        const emit = b.addRunArtifact(exe);
        if (z3_enabled) emit.addPathDir(b.pathFromRoot(z3_bin));
        emit.addArg("emit-readable-luau-strategy");
        emit.addFileArg(admitted_ir);
        const emitted = emit.addOutputFileArg(b.fmt("native-loop-register-{s}-{s}.automatic.luau", .{ arm.shape, arm.admitted }));
        emit.addArgs(&.{ "standard-luau", "automatic" });
        emit.expectExitCode(0);
        const compile = b.addSystemCommand(&.{ luauCompileExe(b), "--null" });
        compile.addFileArg(emitted);
        compile.expectExitCode(0);
        result.steps[next + 1] = &compile.step;
        next += 2;
        if (!arm.direct_locals) continue;

        const direct_refusal = b.addRunArtifact(exe);
        if (z3_enabled) direct_refusal.addPathDir(b.pathFromRoot(z3_bin));
        direct_refusal.addArg("emit-readable-luau-strategy");
        direct_refusal.addFileArg(refused_ir);
        const seed_files = b.addWriteFiles();
        direct_refusal.addFileArg(seed_files.add(b.fmt("native-loop-register-{s}-{s}.direct-locals.luau", .{ arm.shape, arm.refused }), ""));
        direct_refusal.addArgs(&.{ "direct-locals-luau", "automatic" });
        direct_refusal.expectExitCode(1);
        direct_refusal.expectStdErrMatch(b.fmt("diagnostic={s} entity=1\n", .{arm.diagnostic}));
        result.steps[next] = &direct_refusal.step;

        const direct_emit = b.addRunArtifact(exe);
        if (z3_enabled) direct_emit.addPathDir(b.pathFromRoot(z3_bin));
        direct_emit.addArg("emit-readable-luau-strategy");
        direct_emit.addFileArg(admitted_ir);
        const direct_emitted = direct_emit.addOutputFileArg(b.fmt("native-loop-register-{s}-{s}.direct-locals.luau", .{ arm.shape, arm.admitted }));
        direct_emit.addArgs(&.{ "direct-locals-luau", "automatic" });
        direct_emit.expectExitCode(0);
        const direct_compile = b.addSystemCommand(&.{ luauCompileExe(b), "--null" });
        direct_compile.addFileArg(direct_emitted);
        direct_compile.expectExitCode(0);
        result.steps[next + 1] = &direct_compile.step;
        next += 2;
    }
    std.debug.assert(next == result.steps.len);
    return result;
}

fn addNativeLoopRegisterResolvedIr(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    shape: []const u8,
    depth: []const u8,
) std.Build.LazyPath {
    const name = b.fmt("native-loop-register-{s}-{s}", .{ shape, depth });
    const fixture_command = b.addSystemCommand(&.{ luneExe(b), "run" });
    fixture_command.addFileArg(b.path("luau/native_loop_register_conformance.luau"));
    fixture_command.addFileInput(b.path("luau/lifter_ir.luau"));
    fixture_command.addFileInput(b.path("luau/json_codec.luau"));
    const fixture_json = fixture_command.addOutputFileArg(b.fmt("{s}.lifter-ir.json", .{name}));
    fixture_command.addArgs(&.{ shape, depth });
    const resolve = b.addRunArtifact(exe);
    if (z3_enabled) resolve.addPathDir(b.pathFromRoot(z3_bin));
    resolve.addArg("resolve-ir");
    resolve.addFileArg(fixture_json);
    const resolved = resolve.addOutputFileArg(b.fmt("{s}.resolved.lifter-ir.json", .{name}));
    resolve.addArg(if (z3_enabled) "z3" else "internal");
    return resolved;
}

// A fixture's resolved IR emitted under the forced dispatcher (flat layout),
// compiled at -O0, and executed by the runtime oracle case of the same name, the case
// that already holds the fixture's structured output (and, for a source fixture, the
// original program) to its behaviour.
fn addDispatcherRuntimeConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    fixture_name: []const u8,
    resolved_ir: std.Build.LazyPath,
) *std.Build.Step {
    const emit_dispatcher = b.addRunArtifact(exe);
    if (z3_enabled) emit_dispatcher.addPathDir(b.pathFromRoot(z3_bin));
    emit_dispatcher.addArg("emit-readable-luau-strategy");
    emit_dispatcher.addFileArg(resolved_ir);
    const dispatcher_luau = emit_dispatcher.addOutputFileArg(b.fmt("{s}.dispatcher.luau", .{fixture_name}));
    emit_dispatcher.addArgs(&.{ "standard-luau", "dispatcher" });
    emit_dispatcher.expectExitCode(0);

    const compile_dispatcher = b.addSystemCommand(&.{ luauCompileExe(b), "--null", "-O0" });
    compile_dispatcher.addFileArg(dispatcher_luau);
    compile_dispatcher.expectExitCode(0);

    const runtime_dispatcher = b.addSystemCommand(&.{ luneExe(b), "run" });
    runtime_dispatcher.addFileArg(b.path("luau/runtime_oracle.luau"));
    runtime_dispatcher.addFileInput(b.path("luau/source_runtime_oracle.luau"));
    runtime_dispatcher.addFileInput(b.path("luau/pack_multi_latch_runtime_oracle.luau"));
    runtime_dispatcher.addFileInput(b.path("luau/pack_return_storage_runtime_oracle.luau"));
    runtime_dispatcher.addFileInput(b.path("luau/iteration_exit_transfer_runtime_oracle.luau"));
    runtime_dispatcher.addFileInput(b.path("luau/iteration_break_exit_transfer_runtime_oracle.luau"));
    runtime_dispatcher.addFileInput(b.path("luau/iteration_header_entry_runtime_oracle.luau"));
    runtime_dispatcher.addFileInput(b.path("luau/wrapped_continue_runtime_oracle.luau"));
    runtime_dispatcher.addFileInput(b.path("luau/loop_owned_exit_flag_runtime_oracle.luau"));
    runtime_dispatcher.addArg(fixture_name);
    runtime_dispatcher.addFileArg(dispatcher_luau);
    runtime_dispatcher.expectExitCode(0);
    runtime_dispatcher.step.dependOn(&compile_dispatcher.step);
    return &runtime_dispatcher.step;
}

// The inherited-flat automatic arm — a fixture's resolved IR emitted under the automatic
// strategy (which inherits force_dispatcher and renders flat), compiled at -O0 and executed by the runtime
// oracle case of the same name. A sibling of addDispatcherRuntimeConformance that passes `automatic`.
fn addAutomaticRuntimeConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    fixture_name: []const u8,
    resolved_ir: std.Build.LazyPath,
) *std.Build.Step {
    const emit_automatic = b.addRunArtifact(exe);
    if (z3_enabled) emit_automatic.addPathDir(b.pathFromRoot(z3_bin));
    emit_automatic.addArg("emit-readable-luau-strategy");
    emit_automatic.addFileArg(resolved_ir);
    const automatic_luau = emit_automatic.addOutputFileArg(b.fmt("{s}.automatic.luau", .{fixture_name}));
    emit_automatic.addArgs(&.{ "standard-luau", "automatic" });
    emit_automatic.expectExitCode(0);

    const compile_automatic = b.addSystemCommand(&.{ luauCompileExe(b), "--null", "-O0" });
    compile_automatic.addFileArg(automatic_luau);
    compile_automatic.expectExitCode(0);

    const runtime_automatic = b.addSystemCommand(&.{ luneExe(b), "run" });
    runtime_automatic.addFileArg(b.path("luau/runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/source_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/pack_multi_latch_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/pack_return_storage_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/iteration_exit_transfer_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/iteration_break_exit_transfer_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/iteration_header_entry_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/wrapped_continue_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/loop_owned_exit_flag_runtime_oracle.luau"));
    runtime_automatic.addArg(fixture_name);
    runtime_automatic.addFileArg(automatic_luau);
    runtime_automatic.expectExitCode(0);
    runtime_automatic.step.dependOn(&compile_automatic.step);
    return &runtime_automatic.step;
}

// A constructor whose last array item, a nested chain of constructors, sits below the last slot of its batch:
// luau-compile builds the chain above the whole batch, 255 registers from the table register up. Written in direct
// locals the text keeps the source's registers and compiles; in the standard target the value storage table is one
// more local under the table, and the readable admission refuses it for temporary register pressure.
fn addNestedConstructorLastItemConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
) [2]*std.Build.Step {
    const name = "source-frontend-nested-constructor-last-item";
    const fixture_json = addLuauSourceIr(b, "luau/fixtures/nested_constructor_last_item_source.luau", null, name);
    const resolve = b.addRunArtifact(exe);
    if (z3_enabled) resolve.addPathDir(b.pathFromRoot(z3_bin));
    resolve.addArg("resolve-ir");
    resolve.addFileArg(fixture_json);
    const resolved = resolve.addOutputFileArg(name ++ ".resolved.lifter-ir.json");
    resolve.addArg(if (z3_enabled) "z3" else "internal");

    const refusal = b.addRunArtifact(exe);
    if (z3_enabled) refusal.addPathDir(b.pathFromRoot(z3_bin));
    refusal.addArg("expect-diagnostic");
    refusal.addFileArg(resolved);
    refusal.addArgs(&.{ "readable-luau", "unsupported_readable_temporary_register_pressure" });
    refusal.expectExitCode(0);

    const emit = b.addRunArtifact(exe);
    if (z3_enabled) emit.addPathDir(b.pathFromRoot(z3_bin));
    emit.addArg("emit-readable-luau-strategy");
    emit.addFileArg(resolved);
    const emitted = emit.addOutputFileArg(name ++ ".direct-locals.luau");
    emit.addArgs(&.{ "direct-locals-luau", "automatic" });
    emit.expectExitCode(0);
    const compile = b.addSystemCommand(&.{ luauCompileExe(b), "--null" });
    compile.addFileArg(emitted);
    compile.expectExitCode(0);
    return .{ &refusal.step, &compile.step };
}

// The automatic arm for a fixture whose results an existing runtime oracle case already checks: the fixture's
// automatic output is named after the fixture, compiled at -O0 and executed by the oracle under that case's name.
fn addAutomaticRuntimeCaseConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    output_stem: []const u8,
    case_name: []const u8,
    resolved_ir: std.Build.LazyPath,
) *std.Build.Step {
    const emit_automatic = b.addRunArtifact(exe);
    if (z3_enabled) emit_automatic.addPathDir(b.pathFromRoot(z3_bin));
    emit_automatic.addArg("emit-readable-luau-strategy");
    emit_automatic.addFileArg(resolved_ir);
    const automatic_luau = emit_automatic.addOutputFileArg(b.fmt("{s}.automatic.luau", .{output_stem}));
    emit_automatic.addArgs(&.{ "standard-luau", "automatic" });
    emit_automatic.expectExitCode(0);

    const compile_automatic = b.addSystemCommand(&.{ luauCompileExe(b), "--null", "-O0" });
    compile_automatic.addFileArg(automatic_luau);
    compile_automatic.expectExitCode(0);

    const runtime_automatic = b.addSystemCommand(&.{ luneExe(b), "run" });
    runtime_automatic.addFileArg(b.path("luau/runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/source_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/pack_multi_latch_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/pack_return_storage_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/iteration_exit_transfer_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/iteration_break_exit_transfer_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/iteration_header_entry_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/wrapped_continue_runtime_oracle.luau"));
    runtime_automatic.addFileInput(b.path("luau/loop_owned_exit_flag_runtime_oracle.luau"));
    runtime_automatic.addArg(case_name);
    runtime_automatic.addFileArg(automatic_luau);
    runtime_automatic.expectExitCode(0);
    runtime_automatic.step.dependOn(&compile_automatic.step);
    return &runtime_automatic.step;
}

// An emission that must be refused with a typed line, in the dispatcher-budget refusal form
// (`addDispatcherLocalBudgetConformance`): the emitter writes no output, so the output argument is
// an empty seed file, and the step expects exit 1 and the typed line on stderr.
fn addEmitRefusalConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    ir: std.Build.LazyPath,
    seed_name: []const u8,
    strategy: []const u8,
    stderr_match: []const u8,
) *std.Build.Step {
    const emit = b.addRunArtifact(exe);
    if (z3_enabled) emit.addPathDir(b.pathFromRoot(z3_bin));
    emit.addArg("emit-readable-luau-strategy");
    emit.addFileArg(ir);
    const seed_files = b.addWriteFiles();
    emit.addFileArg(seed_files.add(seed_name, ""));
    emit.addArgs(&.{ "standard-luau", strategy });
    emit.expectExitCode(1);
    emit.expectStdErrMatch(stderr_match);
    return &emit.step;
}

// An admitted crafted IR whose numeric transition has an inlined operand, emitted,
// compiled at -O0 and audited for the grouped rendering of every operand an operator follows.
fn addNumericOperandGroupingConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    ir_path: []const u8,
    output_name: []const u8,
    strategy: []const u8,
    audit_mode: []const u8,
) *std.Build.Step {
    const emit = b.addRunArtifact(exe);
    if (z3_enabled) emit.addPathDir(b.pathFromRoot(z3_bin));
    emit.addArg("emit-readable-luau-strategy");
    emit.addFileArg(b.path(ir_path));
    const emitted = emit.addOutputFileArg(output_name);
    emit.addArgs(&.{ "standard-luau", strategy });
    emit.expectExitCode(0);

    const compile = b.addSystemCommand(&.{ luauCompileExe(b), "--null", "-O0" });
    compile.addFileArg(emitted);
    compile.expectExitCode(0);

    const audit = b.addSystemCommand(&.{ luneExe(b), "run" });
    audit.addFileArg(b.path("luau/numeric_operand_grouping_audit.luau"));
    audit.addArg(audit_mode);
    audit.addFileArg(emitted);
    audit.expectExitCode(0);
    audit.step.dependOn(&compile.step);
    return &audit.step;
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
    frontend_command.addFileArg(.{ .cwd_relative = luauAstExe(b) });
    frontend_command.addFileArg(.{ .cwd_relative = luauCompileExe(b) });
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
    emit_command.addFileArg(.{ .cwd_relative = luauCompileExe(b) });

    const runtime_command = b.addSystemCommand(&.{ luneExe(b), "run" });
    runtime_command.addFileArg(b.path("luau/runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/source_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/pack_multi_latch_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/pack_return_storage_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/iteration_exit_transfer_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/iteration_break_exit_transfer_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/iteration_header_entry_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/wrapped_continue_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/loop_owned_exit_flag_runtime_oracle.luau"));
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

// A source conformance arm emitted for a named target. addSerializedConformanceWithEngine emits
// standard-luau only, whose value storage (more than 120 candidate values) hides a scope-plan defect in a large
// function; this sibling runs the same lift, resolve-ir, validate, checked emit, runtime, source compile, lexical and
// source runtime steps for the target it is given (direct-locals-luau).
fn addLuauSourceConformanceForTarget(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    source_path: []const u8,
    fixture_name: []const u8,
    target_name: []const u8,
) FixtureConformance {
    const fixture_json = addLuauSourceIr(b, source_path, null, fixture_name);
    const engine_name = if (z3_enabled) "z3" else "internal";

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
    emit_command.addArg(target_name);
    emit_command.addFileArg(.{ .cwd_relative = luauCompileExe(b) });

    const runtime_command = b.addSystemCommand(&.{ luneExe(b), "run" });
    runtime_command.addFileArg(b.path("luau/runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/source_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/pack_multi_latch_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/pack_return_storage_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/iteration_exit_transfer_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/iteration_break_exit_transfer_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/iteration_header_entry_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/wrapped_continue_runtime_oracle.luau"));
    runtime_command.addFileInput(b.path("luau/loop_owned_exit_flag_runtime_oracle.luau"));
    runtime_command.addArg(fixture_name);
    runtime_command.addFileArg(emitted_luau);

    return .{
        .validate = &validate_command.step,
        .compile = &emit_command.step,
        .runtime = &runtime_command.step,
        .source_compile = addSourceCompileConformance(b, source_path),
        .source_runtime = addSourceRuntimeConformance(b, source_path, fixture_name, emitted_luau),
        .input_ir = fixture_json,
        .resolved_ir = resolved_json,
        .generated_luau = emitted_luau,
    };
}

// emit-luau on an author-written IR, a fixture or a lifted source, for a named target.
// The checked emission compiles the output, so exit 0 means it emits and compiles. A declining fixture prints its
// decline line (once per resolve pass); the control, whose functions all plan, keeps an empty stderr.
fn addFeedbackDeclineConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    trace_normalize_phases: bool,
    conformance_step: *std.Build.Step,
    fixture_ir: std.Build.LazyPath,
    fixture_name: []const u8,
    target_name: []const u8,
    stderr_match: ?[]const u8,
) void {
    const emit_command = b.addRunArtifact(exe);
    if (z3_enabled) emit_command.addPathDir(b.pathFromRoot(z3_bin));
    emit_command.addArg("emit-luau");
    emit_command.addFileArg(fixture_ir);
    _ = emit_command.addOutputFileArg(b.fmt("{s}.generated.luau", .{fixture_name}));
    emit_command.addArg(target_name);
    emit_command.addFileArg(.{ .cwd_relative = luauCompileExe(b) });
    if (stderr_match) |line| {
        emit_command.expectStdErrMatch(line);
    } else if (!trace_normalize_phases) {
        emit_command.expectStdErrEqual("");
    }
    emit_command.expectExitCode(0);
    conformance_step.dependOn(&emit_command.step);
}

// resolve-ir on an author-written IR fixture; the resolved IR is the decline audit's input.
fn addFeedbackDeclineResolve(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    fixture_path: []const u8,
    fixture_name: []const u8,
) std.Build.LazyPath {
    const resolve_command = b.addRunArtifact(exe);
    if (z3_enabled) resolve_command.addPathDir(b.pathFromRoot(z3_bin));
    resolve_command.addArg("resolve-ir");
    resolve_command.addFileArg(b.path(fixture_path));
    const resolved_json = resolve_command.addOutputFileArg(b.fmt("{s}.resolved.lifter-ir.json", .{fixture_name}));
    resolve_command.addArg(if (z3_enabled) "z3" else "internal");
    return resolved_json;
}

// emit-luau on an author-written IR fixture for a
// named target, exit 0 with an empty stderr (the checked emission compiles the output), then the structure audit with
// the expected class: `class=structured-no-dispatcher` for a forwarded latch or a control that plans,
// `class=dispatcher-present` for a control that stays flat.
fn addLatchForwardConformance(
    b: *std.Build,
    exe: *std.Build.Step.Compile,
    z3_enabled: bool,
    z3_bin: []const u8,
    trace_normalize_phases: bool,
    conformance_step: *std.Build.Step,
    fixture_path: []const u8,
    fixture_name: []const u8,
    target_name: []const u8,
    audit_class: []const u8,
) void {
    const emit_command = b.addRunArtifact(exe);
    if (z3_enabled) emit_command.addPathDir(b.pathFromRoot(z3_bin));
    emit_command.addArg("emit-luau");
    emit_command.addFileArg(b.path(fixture_path));
    const generated_luau = emit_command.addOutputFileArg(b.fmt("{s}.generated.luau", .{fixture_name}));
    emit_command.addArg(target_name);
    emit_command.addFileArg(.{ .cwd_relative = luauCompileExe(b) });
    if (!trace_normalize_phases) emit_command.expectStdErrEqual("");
    emit_command.expectExitCode(0);
    conformance_step.dependOn(&emit_command.step);
    const audit = addStructureAstAudit(b, fixture_name, generated_luau);
    audit.expectStdOutMatch(audit_class);
    conformance_step.dependOn(&audit.step);
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
    emit_command.addFileArg(.{ .cwd_relative = luauCompileExe(b) });

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
