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
    conformance_step.dependOn(&register_budget_oracle.step);
    dispatcher_local_budget_conformance.addTo(conformance_step);
    dispatcher_generic_budget_conformance.addTo(conformance_step);
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
    conformance_step.dependOn(numeric_operand_flat_grouping);
    conformance_step.dependOn(numeric_operand_semantic_grouping);
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
    source_frontend_table_pack_conformance.addTo(conformance_step);
    source_frontend_function_statement_conformance.addTo(conformance_step);
    source_frontend_closure_store_environment_conformance.addTo(conformance_step);
    source_frontend_closure_store_environment_direct_locals_conformance.addTo(conformance_step);
    source_frontend_interpolation_conformance.addTo(conformance_step);
    source_frontend_intrinsic_invocation_conformance.addTo(conformance_step);
    source_frontend_coroutine_wrap_conformance.addTo(conformance_step);
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
    runtime_automatic.addArg(fixture_name);
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
