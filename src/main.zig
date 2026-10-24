const std = @import("std");
const Io = std.Io;
const lifter = @import("semantic_lifter");

// Large recovered programs carry repeated provenance/evidence arrays. Keep
// the CLI limit above the size of a composed IR without making reads
// unbounded.
const max_ir_json_bytes: usize = 2 * 1024 * 1024 * 1024;

const usage_text =
    \\usage:
    \\  semantic-lifter fixture-json <arithmetic|absolute|function-reference-identity|dynamic-truthiness|variadic-identity|open-pack|immutable-closure|shared-place-closure> <output.json>
    \\      built-in fixtures; nothing to admit
    \\  semantic-lifter validate <input.json> <core|readable-luau>
    \\  semantic-lifter validate-solved <input.json> <core|readable-luau> <internal|z3>
    \\  semantic-lifter emit-luau <input.json> <output.luau> <standard-luau|direct-locals-luau> <compiler>
    \\  semantic-lifter emit-luau-solved <input.json> <output.luau> <internal|z3> <standard-luau|direct-locals-luau> <compiler>
    \\  semantic-lifter emit-readable-luau <input.json> <output.luau> <standard-luau|direct-locals-luau> <compiler>
    \\  semantic-lifter emit-admitted-readable-luau <input.json> <output.luau> <standard-luau|direct-locals-luau> <compiler>
    \\  semantic-lifter resolve-ir <input.json> <output.json> <internal|z3>
    \\  semantic-lifter resolve-readable-ir <input.json> <output.json> <internal|z3>
    \\  semantic-lifter resolve-admitted-readable-ir <input.json> <output.json>
    \\  semantic-lifter refresh-proof-digests <input.json> <output.json>
    \\  semantic-lifter normalize-control-ir <input.json> <output.json>
    \\  semantic-lifter normalize-ir <input.json> <output.json> [<function-index>]
    \\  semantic-lifter normalize-ir-budget <input.json> <output.json> <function-index> <feedback-iterations> [resume]
    \\  semantic-lifter normalize-ir-resume <input.json> <output.json> <function-index> <feedback-iterations> <resume-token.json>
    \\
    \\test helpers (no output file; exit 0 when the expectation holds):
    \\  semantic-lifter expect-diagnostic <input.json> <core|readable-luau> <diagnostic>
    \\  semantic-lifter expect-blocker-census <input.json> <core|readable-luau> <total> [<kind> <subject> <operation> <producer> <value-type> <place-flow> <count>]...
    \\  semantic-lifter expect-blocker-proof-census <input.json> <core|readable-luau> <total> [<kind> <subject> <operation> <producer> <value-type> <place-flow> <proof-links> <count>]...
    \\
    \\diagnostic-only or unchecked (exit 0 is not a checked publication):
    \\  semantic-lifter emit-admitted-readable-luau-raw <input.json> <output.luau> <standard-luau|direct-locals-luau>
    \\      checks nothing; the caller must already have admitted the input
    \\  semantic-lifter emit-readable-luau-strategy <normalized.json> <output.luau> <standard-luau|direct-locals-luau> <automatic|dispatcher>
    \\      checks readable-luau admission of the input only; no resolution, no compile check;
    \\      an admission refusal prints its diagnostic= lines and writes no output (exit 1)
    \\  semantic-lifter emit-function-probe <input.json> <output.luau> <function-index>
    \\      one function, standard-luau only; checks nothing
    \\  semantic-lifter resolve-exact-control-ir <input.json> <output.json> <internal|z3>
    \\      exact-branch checkpoint; neither its input nor its output is validated
    \\  semantic-lifter inspect-structure <input.json> <function-index>
    \\  semantic-lifter inspect-edge-rewrite <input.json> <rewrite-index>
    \\
    \\exit status: 0 success; 1 refusal (diagnostic= lines on stderr) or an error such as a missing file or a bad argument.
    \\
;

fn usage() void {
    std.debug.print(usage_text, .{});
}

fn inspectIndent(depth: usize) void {
    for (0..depth) |_| std.debug.print("  ", .{});
}

fn inspectCollisionLoops(
    allocator: std.mem.Allocator,
    analysis: *const lifter.cfg.Analysis,
    collision: lifter.structure.Collision,
) !void {
    const collision_index = analysis.blockIndex(collision.block) orelse return;
    for (analysis.function.blocks) |header| {
        var membership = (lifter.natural_loop.collect(allocator, analysis, header) catch |err| switch (err) {
            error.UnsupportedShape => continue,
            error.OutOfMemory => return error.OutOfMemory,
        }) orelse continue;
        defer membership.deinit();
        if (!membership.bits[collision_index]) continue;

        const incoming_source_inside = if (collision.incoming) |incoming| source_inside: {
            const source_index = analysis.blockIndex(incoming.source) orelse break :source_inside false;
            break :source_inside membership.bits[source_index];
        } else false;
        const post_tested = lifter.natural_loop.classifyPostTested(
            analysis,
            header,
            membership.bits,
        ) catch null;
        const exit_shape = try lifter.natural_loop.classifyExit(analysis, membership.bits);
        std.debug.print(
            "structure_collision_loop header={d} members={d} incoming_source_inside={} post_tested={} post_exit={?d} latch_count={d} exit_kind={s} exit={?d}\n",
            .{
                header.index(),
                std.mem.countScalar(bool, membership.bits, true),
                incoming_source_inside,
                post_tested != null,
                if (post_tested) |shape| shape.exit.index() else null,
                if (post_tested) |shape| shape.latch_count else 0,
                @tagName(exit_shape),
                switch (exit_shape) {
                    .unique => |target| target.index(),
                    .closed, .multiple => null,
                },
            },
        );
        for (analysis.function.blocks, 0..) |block, block_index| {
            if (membership.bits[block_index]) {
                std.debug.print("structure_collision_loop_member block={d}\n", .{block.index()});
            }
        }
        for (analysis.function.blocks, 0..) |block, block_index| {
            if (!membership.bits[block_index]) continue;
            for (0..analysis.predecessorCount(block)) |predecessor_index| {
                const predecessor = analysis.predecessorAt(block, predecessor_index) orelse continue;
                const predecessor_local = analysis.blockIndex(predecessor) orelse continue;
                if (!membership.bits[predecessor_local]) {
                    std.debug.print("structure_collision_loop_entry source={d} target={d}\n", .{ predecessor.index(), block.index() });
                }
            }
            for (0..analysis.successorCount(block)) |successor_index| {
                const successor = analysis.successorAt(block, successor_index) orelse continue;
                const successor_local = analysis.blockIndex(successor) orelse continue;
                if (!membership.bits[successor_local]) {
                    std.debug.print("structure_collision_loop_exit source={d} target={d}\n", .{ block.index(), successor.index() });
                }
            }
        }
    }
}

fn inspectStructureRegion(
    allocator: std.mem.Allocator,
    program: *const lifter.ir.Program,
    region: *const lifter.structure.Region,
    depth: usize,
) !void {
    inspectIndent(depth);
    std.debug.print("region nodes={d} stop={?d} loop_exit={?d}\n", .{
        region.nodes.len,
        if (region.stop) |id| id.index() else null,
        if (region.loop_exit) |id| id.index() else null,
    });
    for (region.nodes) |node| switch (node) {
        .block => |id| {
            inspectIndent(depth + 1);
            std.debug.print("block {d}\n", .{id.index()});
        },
        .branch => |branch| {
            const protocol = try lifter.iteration_protocol.matchAcyclicBranch(allocator, program, branch);
            inspectIndent(depth + 1);
            std.debug.print("branch {d} join={?d} iteration={?d}\n", .{
                branch.block.index(),
                if (branch.join) |id| id.index() else null,
                if (protocol) |value| value.protocol.instructionId().index() else null,
            });
            try inspectStructureRegion(allocator, program, branch.then_region, depth + 2);
            try inspectStructureRegion(allocator, program, branch.else_region, depth + 2);
        },
        .loop => |loop| {
            const protocol = try lifter.iteration_protocol.matchLoop(allocator, program, loop);
            inspectIndent(depth + 1);
            std.debug.print("loop {d} body={d} exit={d} iteration={?d}\n", .{
                loop.header.index(),
                loop.body_edge.target.index(),
                loop.exit_edge.target.index(),
                if (protocol) |value| value.instructionId().index() else null,
            });
            try inspectStructureRegion(allocator, program, loop.body_region, depth + 2);
        },
        .latch_loop => |loop| {
            inspectIndent(depth + 1);
            std.debug.print("latch_loop {d} exit={d} latches={d}\n", .{ loop.header.index(), loop.exit.index(), loop.latch_count });
            try inspectStructureRegion(allocator, program, loop.body_region, depth + 2);
        },
        .infinite_loop => |loop| {
            inspectIndent(depth + 1);
            std.debug.print("infinite_loop {d} exit={?d} shared_side={?d}\n", .{
                loop.header.index(),
                if (loop.exit) |id| id.index() else null,
                if (loop.shared_side_exit) |side_exit|
                    if (side_exit.entries.len != 0) side_exit.entries[0].entry.index() else null
                else
                    null,
            });
            try inspectStructureRegion(allocator, program, loop.body_region, depth + 2);
            if (loop.shared_side_exit) |side_exit| {
                for (side_exit.entries) |entry| try inspectStructureRegion(allocator, program, entry.region, depth + 2);
            }
        },
        .loop_control => |control| {
            inspectIndent(depth + 1);
            std.debug.print("loop_control {d}\n", .{control.block.index()});
        },
        .loop_boundary => |control| {
            inspectIndent(depth + 1);
            const boundary_target: ?lifter.ir.BlockId = switch (control.boundary) {
                .exit => |edge| edge.target,
                .escape => |edge| edge.target,
                .terminal => |terminal| terminal.edge.target,
                .side_exit => |side| side.entry_edge.target,
                .side_escape => |side| side.entry_edge.target,
                .shared_exit => |entry| if (entry.value()) |value| value.reference.target else null,
            };
            std.debug.print("loop_boundary {d} body={d} body_stop={?d} body_loop_exit={?d} body_continue={?d} boundary={s} boundary_target={?d}\n", .{
                control.block.index(),
                control.body_edge.target.index(),
                if (control.body_region.stop) |id| id.index() else null,
                if (control.body_region.loop_exit) |id| id.index() else null,
                if (control.body_region.continue_target) |id| id.index() else null,
                @tagName(std.meta.activeTag(control.boundary)),
                if (boundary_target) |id| id.index() else null,
            });
            try inspectStructureRegion(allocator, program, control.body_region, depth + 2);
            switch (control.boundary) {
                .side_exit => |side| {
                    inspectIndent(depth + 2);
                    std.debug.print("side_exit_region entry={d} stop={?d} loop_exit={?d} continue_target={?d}\n", .{
                        side.entry_edge.target.index(),
                        if (side.region.stop) |id| id.index() else null,
                        if (side.region.loop_exit) |id| id.index() else null,
                        if (side.region.continue_target) |id| id.index() else null,
                    });
                    try inspectStructureRegion(allocator, program, side.region, depth + 3);
                },
                .side_escape => |side| {
                    inspectIndent(depth + 2);
                    std.debug.print("side_escape_region entry={d} target={d} stop={?d} loop_exit={?d} continue_target={?d}\n", .{
                        side.entry_edge.target.index(),
                        side.target.index(),
                        if (side.region.stop) |id| id.index() else null,
                        if (side.region.loop_exit) |id| id.index() else null,
                        if (side.region.continue_target) |id| id.index() else null,
                    });
                    try inspectStructureRegion(allocator, program, side.region, depth + 3);
                },
                else => {},
            }
        },
        .loop_terminal => |control| {
            inspectIndent(depth + 1);
            std.debug.print("loop_terminal {d} terminal={d}\n", .{ control.block.index(), control.terminal_block.index() });
        },
    };
}

fn writeFileWithOptions(
    io: Io,
    path: []const u8,
    bytes: []const u8,
    options: Io.Dir.CreateFileOptions,
) !void {
    if (std.fs.path.dirname(path)) |directory| {
        _ = try Io.Dir.cwd().createDirPathStatus(io, directory, .default_dir);
    }
    const file = try Io.Dir.cwd().createFile(io, path, options);
    defer file.close(io);
    var buffer: [8192]u8 = undefined;
    var writer_state = file.writer(io, &buffer);
    const writer = &writer_state.interface;
    try writer.writeAll(bytes);
    try writer.flush();
}

fn writeFile(io: Io, path: []const u8, bytes: []const u8) !void {
    try writeFileWithOptions(io, path, bytes, .{ .truncate = true });
}

/// `program_allocator` owns the storage of `program` (the arena of the command, or the arena that parsing allocated).
/// The refresh stores the proof digests it recomputes in the program, so they are allocated there and released with
/// it; a digest it replaces stays with the owner that allocated it.
fn prepareNormalizedPublication(
    allocator: std.mem.Allocator,
    program_allocator: std.mem.Allocator,
    program: *lifter.ir.Program,
) !void {
    try lifter.proof_orchestrator.refreshSerializedProofDigestsAlloc(program_allocator, program);
    var report = try lifter.validate.validate(allocator, program, .core);
    defer report.deinit();
    printDiagnostics(allocator, &report, program);
    if (!report.isClean()) return error.ValidationFailed;
}

fn parseProfile(text: []const u8) !lifter.ir.AdmissionProfile {
    if (std.mem.eql(u8, text, "core")) return .core;
    if (std.mem.eql(u8, text, "readable-luau")) return .readable_luau;
    return error.UnknownProfile;
}

fn solverBackend(name: []const u8) !lifter.solver_backend.Backend {
    if (std.mem.eql(u8, name, "internal")) return lifter.solver_backend.internalFacts();
    if (std.mem.eql(u8, name, "z3")) {
        if (!lifter.z3_backend.enabled) return error.Z3Disabled;
        return lifter.z3_backend.defaultBackend();
    }
    return error.UnknownSolverBackend;
}

fn emissionTarget(name: []const u8) !lifter.emit_luau.Target {
    if (std.mem.eql(u8, name, "standard-luau")) return .standard_luau;
    if (std.mem.eql(u8, name, "direct-locals-luau")) return .direct_locals_luau;
    return error.UnknownEmissionTarget;
}

const EmissionCommand = enum {
    unsolved,
    solved,
};

fn emissionCommand(name: []const u8) ?EmissionCommand {
    if (std.mem.eql(u8, name, "emit-luau") or std.mem.eql(u8, name, "emit-luau-checked")) return .unsolved;
    if (std.mem.eql(u8, name, "emit-luau-solved") or std.mem.eql(u8, name, "emit-luau-solved-checked")) return .solved;
    return null;
}

fn emissionArgumentCount(command: EmissionCommand) usize {
    return switch (command) {
        .unsolved => 6,
        .solved => 7,
    };
}

fn printCompilerTermination(term: std.process.Child.Term) void {
    switch (term) {
        .exited => |code| std.debug.print("  termination=exited code={d}\n", .{code}),
        .signal => |signal| std.debug.print("  termination=signal code={d}\n", .{@intFromEnum(signal)}),
        .stopped => |signal| std.debug.print("  termination=stopped code={d}\n", .{@intFromEnum(signal)}),
        .unknown => |status| std.debug.print("  termination=unknown code={d}\n", .{status}),
    }
}

fn printCompilerFailure(reason: []const u8, result: lifter.luau_compile_check.Result) void {
    std.debug.print("diagnostic=luau_compile_check_failed entity=null\n", .{});
    std.debug.print("  reason={s}\n", .{reason});
    printCompilerTermination(result.term);
    std.debug.print("  stdout_bytes={d} stdout=\"{f}\"\n", .{ result.stdout.len, std.zig.fmtString(result.stdout) });
    std.debug.print("  stderr_bytes={d} stderr=\"{f}\"\n", .{ result.stderr.len, std.zig.fmtString(result.stderr) });
}

fn requireCheckedPublication(publication: lifter.checked_emission.Outcome) !void {
    switch (publication) {
        .published => return,
        .staging_error => |err| std.debug.print(
            "diagnostic=luau_compile_check_failed entity=null\n  reason=staging_error\n  process_error={s}\n",
            .{@errorName(err)},
        ),
        .compiler_process_error => |err| std.debug.print(
            "diagnostic=luau_compile_check_failed entity=null\n  reason=compiler_process_error\n  process_error={s}\n",
            .{@errorName(err)},
        ),
        .compiler_rejected => |result| printCompilerFailure("compiler_rejected", result),
        .compiler_terminated => |result| printCompilerFailure("compiler_terminated", result),
        .publication_error => |err| std.debug.print(
            "diagnostic=luau_compile_check_failed entity=null\n  reason=publication_error\n  process_error={s}\n",
            .{@errorName(err)},
        ),
    }
    return error.LuauCompileCheckFailed;
}

fn emitLuauChecked(
    io: Io,
    allocator: std.mem.Allocator,
    input_path: []const u8,
    output_path: []const u8,
    backend: lifter.solver_backend.Backend,
    target: lifter.emit_luau.Target,
    compiler_path: []const u8,
    preserve_admitted_readable: bool,
    force_preserve_admitted_readable: bool,
) !void {
    const source = try Io.Dir.cwd().readFileAlloc(io, input_path, allocator, .limited(max_ir_json_bytes));
    defer allocator.free(source);
    var parsed = try lifter.codec.parse(allocator, source);
    defer parsed.deinit();
    var checked = if (preserve_admitted_readable)
        if (force_preserve_admitted_readable)
            try lifter.pipeline.runCheckedDirectAdmittedReadableAlloc(
                allocator,
                io,
                &parsed.value,
                target,
                output_path,
                compiler_path,
            )
        else
            try lifter.pipeline.runCheckedAdmittedReadableAlloc(
                allocator,
                io,
                &parsed.value,
                target,
                output_path,
                compiler_path,
            )
    else
        try lifter.pipeline.runCheckedAlloc(
            allocator,
            io,
            &parsed.value,
            backend,
            target,
            output_path,
            compiler_path,
        );
    defer checked.deinit();
    printDiagnostics(allocator, &checked.pipeline.report, checked.pipeline.program() orelse &parsed.value);
    if (!checked.pipeline.isAdmitted()) return error.ValidationFailed;
    try requireCheckedPublication(checked.publication.?);
}

fn printQueryContext(program: *const lifter.ir.Program, query_id: lifter.ir.QueryId) void {
    if (query_id.index() >= program.queries.len) return;
    const query = program.queries[query_id.index()];
    const goal_operation = if (query.goal.index() < program.solver_terms.len)
        @tagName(program.solver_terms[query.goal.index()].operation)
    else
        "invalid";
    std.debug.print(
        "  query={d} kind={s} goal={d}:{s} assumptions={any} path={any}\n",
        .{ query.id.index(), @tagName(query.kind), query.goal.index(), goal_operation, query.assumptions, query.path_rewrites },
    );
    for (query.assumptions) |constraint_id| {
        if (constraint_id.index() >= program.constraints.len) continue;
        const constraint = program.constraints[constraint_id.index()];
        std.debug.print(
            "    assumption={d} scope={s} predicate={d} path={any}\n",
            .{ constraint_id.index(), @tagName(constraint.scope), constraint.predicate.index(), constraint.path_rewrites },
        );
    }
}

fn printDiagnostics(allocator: std.mem.Allocator, report: *const lifter.validate.Report, program: *const lifter.ir.Program) void {
    if (report.isClean()) return;
    var printed_rewrites = false;
    for (report.diagnostics.items) |diagnostic| {
        std.debug.print("diagnostic={s} entity={?d}\n", .{ @tagName(diagnostic.code), diagnostic.entity_index });
        switch (diagnostic.detail) {
            .solver_unknown => |unknown| {
                std.debug.print(
                    "  engine={s} phase={s} reason={s}\n",
                    .{ @tagName(unknown.engine), @tagName(unknown.phase), @tagName(unknown.reason) },
                );
                continue;
            },
            .none => {},
        }
        if (diagnostic.code == .non_dominating_value_use) {
            const entity_index = diagnostic.entity_index orelse continue;
            if (entity_index < program.instructions.len) {
                const instruction = program.instructions[entity_index];
                std.debug.print(
                    "  candidate_instruction={d} block={d} operation={s}\n",
                    .{ instruction.id.index(), instruction.block.index(), @tagName(instruction.operation) },
                );
            }
            if (entity_index < program.blocks.len) {
                const block = program.blocks[entity_index];
                std.debug.print("  candidate_block={d} terminator={s}\n", .{ block.id.index(), @tagName(block.terminator) });
            }
            if (!printed_rewrites) {
                printed_rewrites = true;
                std.debug.print("  edge_rewrites={d}\n", .{program.edge_rewrites.len});
                for (program.edge_rewrites) |rewrite| {
                    std.debug.print(
                        "    rewrite={d} source={d}:{s} from={d} to={d} rule={s} certificate={?d}\n",
                        .{
                            rewrite.id.index(),
                            rewrite.source.index(),
                            @tagName(rewrite.kind),
                            rewrite.from.target.index(),
                            rewrite.to.target.index(),
                            @tagName(rewrite.rule),
                            if (rewrite.certificate) |certificate| certificate.index() else null,
                        },
                    );
                }
            }
            continue;
        }
        if (diagnostic.code == .contradictory_solver_proof) {
            const certificate_index = diagnostic.entity_index orelse continue;
            if (certificate_index >= program.certificates.len) continue;
            const certificate = program.certificates[certificate_index];
            std.debug.print(
                "  certificate={d} engine={s} resolution={s}\n",
                .{ certificate.id.index(), @tagName(certificate.engine), @tagName(certificate.resolution) },
            );
            printQueryContext(program, certificate.query);
            continue;
        }
        if (diagnostic.code == .contradictory_solver_model) {
            const model_index = diagnostic.entity_index orelse continue;
            if (model_index >= program.solver_models.len) continue;
            const model = program.solver_models[model_index];
            std.debug.print("  model={d} bindings={d}\n", .{ model.id.index(), model.bindings.len });
            printQueryContext(program, model.query);
            for (model.bindings) |binding| {
                std.debug.print("    binding_term={d} value={any}\n", .{ binding.term.index(), binding.value });
            }
            continue;
        }
        if (diagnostic.code == .certificate_digest_mismatch) {
            const certificate_index = diagnostic.entity_index orelse continue;
            if (certificate_index >= program.certificates.len) continue;
            const certificate = program.certificates[certificate_index];
            std.debug.print(
                "  certificate={d} engine={s} resolution={s} model={?d} core={?d}\n",
                .{
                    certificate.id.index(),
                    @tagName(certificate.engine),
                    @tagName(certificate.resolution),
                    if (certificate.model) |model| model.index() else null,
                    if (certificate.unsat_core) |core| core.index() else null,
                },
            );
            printQueryContext(program, certificate.query);
            continue;
        }
        if (diagnostic.code != .open_profile_obligation) continue;
        const obligation_index = diagnostic.entity_index orelse continue;
        if (obligation_index >= program.obligations.len) continue;
        const obligation = program.obligations[obligation_index];
        std.debug.print(
            "  obligation_kind={s} blocks_profile={s} subject={s}:{?d} operation={s} detail={s}\n",
            .{
                @tagName(obligation.kind),
                @tagName(obligation.blocks_profile),
                @tagName(obligation.subject),
                lifter.blocker_report.subjectIndex(obligation.subject),
                lifter.blocker_report.subjectOperation(program, obligation.subject),
                obligation.detail,
            },
        );
        const proof_links = lifter.blocker_report.obligationProofLinks(obligation);
        if (obligation.requirement) |requirement| {
            const predicate_operation = if (requirement.predicate.index() < program.solver_terms.len)
                @tagName(program.solver_terms[requirement.predicate.index()].operation)
            else
                "invalid";
            std.debug.print(
                "  proof_links={s} requirement={s} predicate={d}:{s} query={?d} certificate={?d}\n",
                .{
                    @tagName(proof_links),
                    @tagName(requirement.kind),
                    requirement.predicate.index(),
                    predicate_operation,
                    if (obligation.query) |query| query.index() else null,
                    if (obligation.certificate) |certificate| certificate.index() else null,
                },
            );
        } else {
            std.debug.print(
                "  proof_links={s} requirement=none predicate=null query={?d} certificate={?d}\n",
                .{
                    @tagName(proof_links),
                    if (obligation.query) |query| query.index() else null,
                    if (obligation.certificate) |certificate| certificate.index() else null,
                },
            );
        }
        if (obligation.query) |query| printQueryContext(program, query);
        if (lifter.blocker_report.invocationTarget(program, obligation.subject)) |target| {
            std.debug.print(
                "  target_value={d} value_type={s} producer={s} producer_instruction={?d}\n",
                .{
                    target.value.index(),
                    @tagName(target.value_type),
                    target.producer.label(),
                    if (target.producer_instruction) |instruction| instruction.index() else null,
                },
            );
            if (target.evidence) |evidence_id| {
                std.debug.print("  producer_provenance={s}\n", .{program.evidence[evidence_id.index()].locator});
            }
            const place_read_id = switch (target.producer) {
                .operation => |operation| if (operation == .place_read) target.producer_instruction else null,
                else => null,
            };
            if (place_read_id) |read_id| {
                const maybe_flow = lifter.place_flow.analyzeDirectReachingWrites(allocator, program, read_id) catch null;
                if (maybe_flow) |flow_value| {
                    var flow = flow_value;
                    defer flow.deinit();
                    const place = program.places[flow.place.index()];
                    std.debug.print(
                        "  target_place={d} place_type={s} place_origin={s} direct_entry_reaches_read={} direct_reaching_write_count={d}\n",
                        .{
                            flow.place.index(),
                            @tagName(place.type.kind),
                            lifter.blocker_report.placeOriginLabel(place.origin),
                            flow.reaches_entry,
                            flow.writes.len,
                        },
                    );
                    for (flow.writes) |write_id| {
                        const write_instruction = program.instructions[write_id.index()];
                        const write = switch (write_instruction.operation) {
                            .place_write => |value| value,
                            else => continue,
                        };
                        const value = lifter.blocker_report.valueProducer(program, write.value) orelse continue;
                        std.debug.print(
                            "    direct_reaching_write={d} value={d} value_type={s} producer={s} producer_instruction={?d}\n",
                            .{
                                write_id.index(),
                                value.value.index(),
                                @tagName(value.value_type),
                                value.producer.label(),
                                if (value.producer_instruction) |instruction| instruction.index() else null,
                            },
                        );
                        if (lifter.blocker_report.preferredEvidence(program, write_instruction.evidence)) |evidence_id| {
                            std.debug.print("    direct_reaching_write_provenance={s}\n", .{program.evidence[evidence_id.index()].locator});
                        }
                        if (value.evidence) |evidence_id| {
                            std.debug.print("    direct_reaching_value_provenance={s}\n", .{program.evidence[evidence_id.index()].locator});
                        }
                        if (lifter.blocker_report.packResultProjection(program, value.value)) |projection| {
                            std.debug.print(
                                "    pack_projection_adjustment={d} result_index={d} pack={d} producer={s} producer_instruction={d}\n",
                                .{
                                    projection.adjustment.index(),
                                    projection.result_index,
                                    projection.pack.index(),
                                    @tagName(projection.producer_operation),
                                    projection.producer.index(),
                                },
                            );
                            if (projection.evidence) |evidence_id| {
                                std.debug.print("    pack_producer_provenance={s}\n", .{program.evidence[evidence_id.index()].locator});
                            }
                        }
                    }
                }
            }
        }
        if (lifter.blocker_report.preferredEvidence(program, obligation.evidence)) |evidence_id| {
            std.debug.print("  obligation_provenance={s}\n", .{program.evidence[evidence_id.index()].locator});
        }
    }
}

fn fixtureByName(name: []const u8) !*const lifter.ir.Program {
    if (std.mem.eql(u8, name, "arithmetic")) return &lifter.fixtures.arithmetic_module.program;
    if (std.mem.eql(u8, name, "absolute")) return &lifter.fixtures.absolute_value_module.program;
    if (std.mem.eql(u8, name, "function-reference-identity")) return &lifter.fixtures.function_reference_module.program;
    if (std.mem.eql(u8, name, "dynamic-truthiness")) return &lifter.fixtures.dynamic_truthiness_module.program;
    if (std.mem.eql(u8, name, "variadic-identity")) return &lifter.fixtures.variadic_identity_module.program;
    if (std.mem.eql(u8, name, "immutable-closure")) return &lifter.fixtures.immutable_closure_module.program;
    if (std.mem.eql(u8, name, "shared-place-closure")) return &lifter.fixtures.shared_place_closure_module.program;
    if (std.mem.eql(u8, name, "open-pack")) return &lifter.fixtures.open_pack_adjust_module.program;
    return error.UnknownFixture;
}

pub fn main(init: std.process.Init) !void {
    const io = init.io;
    const arena = init.arena.allocator();
    const allocator = init.gpa;
    const args = try init.minimal.args.toSlice(arena);

    if (args.len < 2) {
        usage();
        return error.MissingCommand;
    }

    const command = args[1];
    if (std.mem.eql(u8, command, "fixture-json")) {
        if (args.len != 4) {
            usage();
            return error.InvalidArguments;
        }
        const encoded = try lifter.codec.encodeAlloc(allocator, try fixtureByName(args[2]));
        defer allocator.free(encoded);
        try writeFile(io, args[3], encoded);
        return;
    }

    if (std.mem.eql(u8, command, "validate")) {
        if (args.len != 4) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        var report = try lifter.validate.validate(allocator, &parsed.value, try parseProfile(args[3]));
        defer report.deinit();
        printDiagnostics(allocator, &report, &parsed.value);
        if (!report.isClean()) return error.ValidationFailed;
        return;
    }

    if (std.mem.eql(u8, command, "inspect-structure")) {
        if (args.len != 4) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        const function_index = try std.fmt.parseInt(usize, args[3], 10);
        if (function_index >= parsed.value.functions.len) return error.InvalidFunctionIndex;
        const function = parsed.value.functions[function_index];
        var analysis = try lifter.cfg.Analysis.init(allocator, &parsed.value, function);
        defer analysis.deinit();
        var collision: ?lifter.structure.Collision = null;
        var structured = lifter.structure.Plan.initWithCollision(allocator, &analysis, &collision) catch |err| {
            if (collision) |*value| {
                defer value.deinit(allocator);
                std.debug.print("structure_collision block={d} previous={?d} incoming_source={?d} incoming_count={d} reason={s}\n", .{
                    value.block.index(),
                    if (value.previous) |previous| previous.index() else null,
                    if (value.incoming) |incoming| incoming.source.index() else null,
                    if (value.incoming_group.len != 0) value.incoming_group.len else @intFromBool(value.incoming != null),
                    @tagName(value.reason),
                });
                if (value.owner_context) |owner| {
                    std.debug.print("structure_collision_owner start={d} stop={?d} loop_exit={?d} continue_target={?d}\n", .{
                        owner.start.index(),
                        if (owner.stop) |block| block.index() else null,
                        if (owner.loop_exit) |block| block.index() else null,
                        if (owner.continue_target) |block| block.index() else null,
                    });
                }
                if (value.incoming_context) |incoming| {
                    std.debug.print("structure_collision_incoming start={d} stop={?d} loop_exit={?d} continue_target={?d}\n", .{
                        incoming.start.index(),
                        if (incoming.stop) |block| block.index() else null,
                        if (incoming.loop_exit) |block| block.index() else null,
                        if (incoming.continue_target) |block| block.index() else null,
                    });
                }
                try inspectCollisionLoops(allocator, &analysis, value.*);
                if (value.incoming) |incoming| {
                    var replay = try lifter.structural_overlap.ReplayProjectionContext.initForFunction(
                        allocator,
                        &parsed.value,
                        function.id,
                    );
                    defer replay.deinit();
                    var split = try lifter.structural_overlap.findCollisionSplitAllocWithAnalysisAndReplayContext(
                        allocator,
                        &parsed.value,
                        &analysis,
                        function_index,
                        value.block,
                        &.{incoming},
                        &replay,
                    );
                    if (split) |*candidate| {
                        defer candidate.deinit();
                        std.debug.print("structure_collision_split entry={} join={} incoming={any} closure={any}\n", .{
                            candidate.entry.index(),
                            candidate.join.index(),
                            candidate.incoming,
                            candidate.closure,
                        });
                    } else {
                        std.debug.print("structure_collision_split unavailable\n", .{});
                    }
                }
            }
            return err;
        };
        defer structured.deinit();
        std.debug.print("function={d} root_nodes={d}\n", .{ function_index, structured.root.nodes.len });
        try inspectStructureRegion(allocator, &parsed.value, structured.root, 0);
        return;
    }

    if (std.mem.eql(u8, command, "expect-diagnostic")) {
        if (args.len != 5) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        var report = try lifter.validate.validate(allocator, &parsed.value, try parseProfile(args[3]));
        defer report.deinit();
        for (report.diagnostics.items) |diagnostic| {
            if (std.mem.eql(u8, @tagName(diagnostic.code), args[4])) return;
        }
        printDiagnostics(allocator, &report, &parsed.value);
        return error.ExpectedDiagnosticMissing;
    }

    if (std.mem.eql(u8, command, "expect-blocker-census") or std.mem.eql(u8, command, "expect-blocker-proof-census")) {
        const include_proof_links = std.mem.eql(u8, command, "expect-blocker-proof-census");
        const row_width: usize = if (include_proof_links) 8 else 7;
        if (args.len < 5 or (args.len - 5) % row_width != 0) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        var report = try lifter.validate.validate(allocator, &parsed.value, try parseProfile(args[3]));
        defer report.deinit();

        const expected_total = try std.fmt.parseInt(usize, args[4], 10);
        var actual_total: usize = 0;
        for (report.diagnostics.items) |diagnostic| {
            if (diagnostic.code == .open_profile_obligation) {
                actual_total += 1;
            } else if (diagnostic.code != .solver_unknown) {
                printDiagnostics(allocator, &report, &parsed.value);
                return error.UnexpectedDiagnostic;
            }
        }
        if (actual_total != expected_total) {
            printDiagnostics(allocator, &report, &parsed.value);
            return error.ExpectedObligationCensusMismatch;
        }

        var expected_sum: usize = 0;
        var row_index: usize = 5;
        while (row_index < args.len) : (row_index += row_width) {
            const expected_kind = args[row_index];
            const expected_subject = args[row_index + 1];
            const expected_operation = args[row_index + 2];
            const expected_producer = args[row_index + 3];
            const expected_value_type = args[row_index + 4];
            const expected_place_flow = args[row_index + 5];
            const expected_proof_links: ?[]const u8 = if (include_proof_links) args[row_index + 6] else null;
            const expected_count = try std.fmt.parseInt(usize, args[row_index + row_width - 1], 10);
            var prior_index: usize = 5;
            while (prior_index < row_index) : (prior_index += row_width) {
                if (std.mem.eql(u8, expected_kind, args[prior_index]) and
                    std.mem.eql(u8, expected_subject, args[prior_index + 1]) and
                    std.mem.eql(u8, expected_operation, args[prior_index + 2]) and
                    std.mem.eql(u8, expected_producer, args[prior_index + 3]) and
                    std.mem.eql(u8, expected_value_type, args[prior_index + 4]) and
                    std.mem.eql(u8, expected_place_flow, args[prior_index + 5]) and
                    (!include_proof_links or std.mem.eql(u8, expected_proof_links.?, args[prior_index + 6])))
                {
                    return error.InvalidArguments;
                }
            }
            var actual_count: usize = 0;
            for (report.diagnostics.items) |diagnostic| {
                if (diagnostic.code != .open_profile_obligation) continue;
                const obligation_index = diagnostic.entity_index orelse continue;
                if (obligation_index >= parsed.value.obligations.len) continue;
                const obligation = parsed.value.obligations[obligation_index];
                const target = lifter.blocker_report.invocationTarget(&parsed.value, obligation.subject) orelse continue;
                if (std.mem.eql(u8, @tagName(obligation.kind), expected_kind) and
                    std.mem.eql(u8, @tagName(obligation.subject), expected_subject) and
                    std.mem.eql(u8, lifter.blocker_report.subjectOperation(&parsed.value, obligation.subject), expected_operation) and
                    std.mem.eql(u8, target.producer.label(), expected_producer) and
                    std.mem.eql(u8, @tagName(target.value_type), expected_value_type) and
                    (expected_proof_links == null or lifter.blocker_report.obligationProofLinksMatch(obligation, expected_proof_links.?)) and
                    lifter.blocker_report.placeFlowClassMatches(
                        lifter.blocker_report.placeFlowClass(allocator, &parsed.value, target) catch .{ .unavailable = {} },
                        expected_place_flow,
                    ))
                {
                    actual_count += 1;
                }
            }
            if (actual_count != expected_count) {
                printDiagnostics(allocator, &report, &parsed.value);
                return error.ExpectedObligationCensusMismatch;
            }
            expected_sum = std.math.add(usize, expected_sum, expected_count) catch return error.InvalidArguments;
        }
        if (expected_sum != expected_total) return error.InvalidArguments;
        return;
    }

    if (emissionCommand(command)) |emission_command| {
        if (args.len != emissionArgumentCount(emission_command)) {
            usage();
            return error.InvalidArguments;
        }
        switch (emission_command) {
            .unsolved => try emitLuauChecked(
                io,
                allocator,
                args[2],
                args[3],
                lifter.solver_backend.internalFacts(),
                try emissionTarget(args[4]),
                args[5],
                false,
                false,
            ),
            .solved => try emitLuauChecked(
                io,
                allocator,
                args[2],
                args[3],
                try solverBackend(args[4]),
                try emissionTarget(args[5]),
                args[6],
                false,
                false,
            ),
        }
        return;
    }

    if (std.mem.eql(u8, command, "emit-readable-luau")) {
        if (args.len != 6) {
            usage();
            return error.InvalidArguments;
        }
        try emitLuauChecked(
            io,
            allocator,
            args[2],
            args[3],
            lifter.solver_backend.internalFacts(),
            try emissionTarget(args[4]),
            args[5],
            true,
            false,
        );
        return;
    }

    if (std.mem.eql(u8, command, "emit-admitted-readable-luau")) {
        if (args.len != 6) {
            usage();
            return error.InvalidArguments;
        }
        try emitLuauChecked(
            io,
            allocator,
            args[2],
            args[3],
            lifter.solver_backend.internalFacts(),
            try emissionTarget(args[4]),
            args[5],
            true,
            true,
        );
        return;
    }

    if (std.mem.eql(u8, command, "emit-readable-luau-strategy")) {
        if (args.len != 6) {
            usage();
            return error.InvalidArguments;
        }
        const force_dispatcher = if (std.mem.eql(u8, args[5], "automatic"))
            false
        else if (std.mem.eql(u8, args[5], "dispatcher"))
            true
        else
            return error.InvalidArguments;
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        const target = try emissionTarget(args[4]);
        // The admission emit_luau.emitAllocForTargetWithOptions runs, with the
        // report printed instead of collapsed into error.InvalidIr.
        var report = try lifter.validate.validateForTargetWithStrategy(
            allocator,
            &parsed.value,
            .readable_luau,
            target,
            if (force_dispatcher) .dispatcher else .automatic,
        );
        defer report.deinit();
        printDiagnostics(allocator, &report, &parsed.value);
        if (!report.isClean()) return error.ValidationFailed;
        const emitted = try lifter.emit_luau.emitAdmittedAllocForTargetWithOptions(
            allocator,
            &parsed.value,
            target,
            .{ .force_dispatcher = force_dispatcher },
        );
        defer allocator.free(emitted);
        try writeFile(io, args[3], emitted);
        return;
    }

    if (std.mem.eql(u8, command, "emit-admitted-readable-luau-raw")) {
        if (args.len != 5) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        const emitted = try lifter.emit_luau.emitAdmittedAllocForTarget(
            allocator,
            &parsed.value,
            try emissionTarget(args[4]),
        );
        defer allocator.free(emitted);
        try writeFile(io, args[3], emitted);
        return;
    }

    if (std.mem.eql(u8, command, "validate-solved")) {
        if (args.len != 5) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        var outcome = try lifter.pipeline.runAlloc(
            allocator,
            &parsed.value,
            try solverBackend(args[4]),
            .{ .profile = try parseProfile(args[3]) },
        );
        defer outcome.deinit();
        printDiagnostics(allocator, &outcome.report, outcome.program() orelse &parsed.value);
        if (!outcome.isAdmitted()) return error.ValidationFailed;
        return;
    }

    if (std.mem.eql(u8, command, "resolve-ir")) {
        if (args.len != 5) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        var outcome = try lifter.pipeline.runAlloc(
            allocator,
            &parsed.value,
            try solverBackend(args[4]),
            .{ .profile = .core },
        );
        defer outcome.deinit();
        printDiagnostics(allocator, &outcome.report, outcome.program() orelse &parsed.value);
        if (!outcome.isAdmitted()) return error.ValidationFailed;
        const resolved_program = outcome.program() orelse return error.ValidationFailed;
        const encoded = try lifter.codec.encodeAlloc(allocator, resolved_program);
        defer allocator.free(encoded);
        try writeFile(io, args[3], encoded);
        return;
    }

    if (std.mem.eql(u8, command, "resolve-exact-control-ir")) {
        if (args.len != 5) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();

        var resolved = try lifter.proof_orchestrator.resolveExactControlAlloc(
            allocator,
            &parsed.value,
            try solverBackend(args[4]),
        );
        defer resolved.deinit();
        if (resolved.control_result.conflicting_certificate) |certificate| {
            std.debug.print("diagnostic=contradictory_solver_proof entity={d}\n", .{certificate});
            return error.ValidationFailed;
        }
        printDiagnostics(allocator, &resolved.solve_report, &resolved.program);
        const encoded = try lifter.codec.encodeCompactAlloc(allocator, &resolved.program);
        defer allocator.free(encoded);
        try writeFile(io, args[3], encoded);
        return;
    }

    if (std.mem.eql(u8, command, "resolve-readable-ir")) {
        if (args.len != 5) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        var outcome = try lifter.pipeline.runAlloc(
            allocator,
            &parsed.value,
            try solverBackend(args[4]),
            .{
                .profile = .readable_luau,
                .preserve_admitted_readable = true,
            },
        );
        defer outcome.deinit();
        printDiagnostics(allocator, &outcome.report, outcome.program() orelse &parsed.value);
        if (!outcome.isAdmitted()) return error.ValidationFailed;
        const resolved_program = outcome.program() orelse return error.ValidationFailed;
        const encoded = try lifter.codec.encodeAlloc(allocator, resolved_program);
        defer allocator.free(encoded);
        try writeFile(io, args[3], encoded);
        return;
    }

    if (std.mem.eql(u8, command, "resolve-admitted-readable-ir")) {
        if (args.len != 4) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        var outcome = try lifter.pipeline.runAlloc(
            allocator,
            &parsed.value,
            lifter.solver_backend.internalFacts(),
            .{
                .profile = .readable_luau,
                .preserve_admitted_readable = true,
                .force_preserve_admitted_readable = true,
            },
        );
        defer outcome.deinit();
        printDiagnostics(allocator, &outcome.report, outcome.program() orelse &parsed.value);
        if (!outcome.isAdmitted()) return error.ValidationFailed;
        const resolved_program = outcome.program() orelse return error.ValidationFailed;
        const encoded = try lifter.codec.encodeAlloc(allocator, resolved_program);
        defer allocator.free(encoded);
        try writeFile(io, args[3], encoded);
        return;
    }

    if (std.mem.eql(u8, command, "refresh-proof-digests")) {
        if (args.len != 4) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        try prepareNormalizedPublication(allocator, parsed.arena.allocator(), &parsed.value);
        const encoded = try lifter.codec.encodeCompactAlloc(allocator, &parsed.value);
        defer allocator.free(encoded);
        try writeFile(io, args[3], encoded);
        return;
    }

    if (std.mem.eql(u8, command, "emit-function-probe")) {
        if (args.len != 5) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        const function_index = try std.fmt.parseInt(usize, args[4], 10);
        const emitted = try lifter.emit_luau.emitAdmittedFunctionAlloc(
            allocator,
            &parsed.value,
            .standard_luau,
            lifter.ir.FunctionId.fromIndex(function_index),
        );
        defer allocator.free(emitted);
        try writeFile(io, args[3], emitted);
        return;
    }

    if (std.mem.eql(u8, command, "inspect-edge-rewrite")) {
        if (args.len != 4) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        const rewrite_index = try std.fmt.parseInt(usize, args[3], 10);
        if (rewrite_index >= parsed.value.edge_rewrites.len) return error.InvalidRewriteIndex;
        const rewrite = parsed.value.edge_rewrites[rewrite_index];
        std.debug.print(
            "rewrite={d} source={d} kind={s} from={d} to={d} rule={s} group={?d}\n",
            .{
                rewrite.id.index(),
                rewrite.source.index(),
                @tagName(rewrite.kind),
                rewrite.from.target.index(),
                rewrite.to.target.index(),
                @tagName(rewrite.rule),
                if (rewrite.node_split_group) |group| group.index() else null,
            },
        );
        if (rewrite.from.target.index() < parsed.value.blocks.len and
            rewrite.to.target.index() < parsed.value.blocks.len)
        {
            const source_terminator = parsed.value.blocks[rewrite.from.target.index()].terminator;
            const clone_terminator = parsed.value.blocks[rewrite.to.target.index()].terminator;
            std.debug.print("source_terminator={s} clone_terminator={s} source_consumed={} clone_consumed={}\n", .{
                @tagName(std.meta.activeTag(source_terminator)),
                @tagName(std.meta.activeTag(clone_terminator)),
                lifter.edge_path.consumedBranchForReplay(&parsed.value, rewrite.from.target) != null,
                lifter.edge_path.consumedBranchForReplay(&parsed.value, rewrite.to.target) != null,
            });
        }
        if (rewrite.rule != .node_split) return;
        const group = rewrite.node_split_group orelse {
            std.debug.print("replay=missing_node_split_group\n", .{});
            return;
        };
        var replay_index = try lifter.node_split.ReplayIndex.init(allocator, &parsed.value);
        defer replay_index.deinit();
        std.debug.print("replay_index_valid={} clone_source={?d}\n", .{
            replay_index.valid,
            if (rewrite.to.target.index() < replay_index.clone_sources.len)
                if (replay_index.clone_sources[rewrite.to.target.index()]) |source_id| source_id.index() else null
            else
                null,
        });
        const mappings = try lifter.node_split.replayMappingsForCloneAllocWithIndex(
            allocator,
            &parsed.value,
            &replay_index,
            rewrite.from.target,
            rewrite.to.target,
            group,
        );
        if (mappings) |mapping_value| {
            var mapping = mapping_value;
            defer mapping.deinit();
            std.debug.print(
                "mapping=ok values={d} packs={d} history_start={?d}\n",
                .{ mapping.source_values.len, mapping.source_packs.len, mapping.history_start },
            );
        } else {
            std.debug.print("mapping=null\n", .{});
        }
        const replayed = try lifter.control_flow.replayNodeSplitWithIndex(
            allocator,
            &parsed.value,
            rewrite.from,
            rewrite.to.target,
            group,
            &replay_index,
        );
        if (replayed) |edge| {
            defer if (edge.arguments.len != 0) allocator.free(edge.arguments);
            std.debug.print("replay=ok target={d} arguments={any}\n", .{ edge.target.index(), edge.arguments });
        } else {
            std.debug.print("replay=null\n", .{});
        }
        return;
    }

    if (std.mem.eql(u8, command, "normalize-ir-budget")) {
        if (args.len != 6 and args.len != 7) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        const function_index = try std.fmt.parseInt(usize, args[4], 10);
        if (function_index >= parsed.value.functions.len) return error.InvalidFunctionIndex;
        const feedback_iterations = try std.fmt.parseInt(usize, args[5], 10);
        const resume_requested = if (args.len == 7) blk: {
            if (!std.mem.eql(u8, args[6], "resume")) return error.InvalidArguments;
            break :blk true;
        } else false;
        var arena_state = std.heap.ArenaAllocator.init(allocator);
        defer arena_state.deinit();
        var normalized = if (resume_requested)
            try lifter.irreducible_normalize.normalizeFunctionWithScratchInArenaResumeBudget(
                arena_state.allocator(),
                allocator,
                &parsed.value,
                function_index,
                feedback_iterations,
            )
        else
            try lifter.irreducible_normalize.normalizeFunctionWithScratchInArenaBudget(
                arena_state.allocator(),
                allocator,
                &parsed.value,
                function_index,
                feedback_iterations,
            );
        try prepareNormalizedPublication(allocator, arena_state.allocator(), &normalized.program);
        const encoded = try lifter.codec.encodeCompactAlloc(allocator, &normalized.program);
        defer allocator.free(encoded);
        try writeFile(io, args[3], encoded);
        return;
    }

    if (std.mem.eql(u8, command, "normalize-ir-resume")) {
        if (args.len != 7) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        const function_index = try std.fmt.parseInt(usize, args[4], 10);
        if (function_index >= parsed.value.functions.len) return error.InvalidFunctionIndex;
        const feedback_iterations = try std.fmt.parseInt(usize, args[5], 10);

        var token_source: ?[]u8 = null;
        defer if (token_source) |bytes| allocator.free(bytes);
        var parsed_token: ?std.json.Parsed(?lifter.irreducible_normalize.ResumeSeed) = null;
        defer if (parsed_token) |*value| value.deinit();
        if (Io.Dir.cwd().readFileAlloc(io, args[6], allocator, .limited(1024 * 1024))) |bytes| {
            token_source = bytes;
            parsed_token = try std.json.parseFromSlice(
                ?lifter.irreducible_normalize.ResumeSeed,
                allocator,
                bytes,
                .{ .allocate = .alloc_always },
            );
        } else |err| switch (err) {
            error.FileNotFound => {},
            else => return err,
        }
        const initial_seed = if (parsed_token) |value| value.value else null;
        var arena_state = std.heap.ArenaAllocator.init(allocator);
        defer arena_state.deinit();
        var normalized = try lifter.irreducible_normalize.normalizeFunctionWithScratchInArenaResumeSeedBudget(
            arena_state.allocator(),
            allocator,
            &parsed.value,
            function_index,
            feedback_iterations,
            initial_seed,
        );
        try prepareNormalizedPublication(allocator, arena_state.allocator(), &normalized.program);
        const encoded = try lifter.codec.encodeCompactAlloc(allocator, &normalized.program);
        defer allocator.free(encoded);
        try writeFile(io, args[3], encoded);
        const encoded_seed = try std.json.Stringify.valueAlloc(allocator, normalized.resume_seed, .{});
        defer allocator.free(encoded_seed);
        try writeFile(io, args[6], encoded_seed);
        return;
    }

    if (std.mem.eql(u8, command, "normalize-control-ir") or std.mem.eql(u8, command, "normalize-ir")) {
        const control_only = std.mem.eql(u8, command, "normalize-control-ir");
        if ((control_only and args.len != 4) or (!control_only and args.len != 4 and args.len != 5)) {
            usage();
            return error.InvalidArguments;
        }
        const source = try Io.Dir.cwd().readFileAlloc(io, args[2], allocator, .limited(max_ir_json_bytes));
        defer allocator.free(source);
        var parsed = try lifter.codec.parse(allocator, source);
        defer parsed.deinit();
        const only_function: ?usize = if (!control_only and args.len == 5) blk: {
            const function_index = try std.fmt.parseInt(usize, args[4], 10);
            if (function_index >= parsed.value.functions.len) return error.InvalidFunctionIndex;
            break :blk function_index;
        } else null;
        var arena_state = std.heap.ArenaAllocator.init(allocator);
        defer arena_state.deinit();
        var normalized = if (control_only)
            try lifter.irreducible_normalize.normalizeControlWithScratchInArena(
                arena_state.allocator(),
                allocator,
                &parsed.value,
            )
        else if (only_function) |function_index|
            try lifter.irreducible_normalize.normalizeFunctionWithScratchInArena(
                arena_state.allocator(),
                allocator,
                &parsed.value,
                function_index,
            )
        else
            try lifter.irreducible_normalize.normalizeWithScratchInArena(
                arena_state.allocator(),
                allocator,
                &parsed.value,
            );
        try prepareNormalizedPublication(allocator, arena_state.allocator(), &normalized.program);
        const encoded = try lifter.codec.encodeAlloc(allocator, &normalized.program);
        defer allocator.free(encoded);
        try writeFile(io, args[3], encoded);
        return;
    }

    usage();
    return error.UnknownCommand;
}

test "profile spelling stays stable at the CLI boundary" {
    try std.testing.expectEqual(lifter.ir.AdmissionProfile.core, try parseProfile("core"));
    try std.testing.expectEqual(lifter.ir.AdmissionProfile.readable_luau, try parseProfile("readable-luau"));
    try std.testing.expectError(error.UnknownProfile, parseProfile("family-specific"));
}

test "solver backend spelling stays explicit" {
    try std.testing.expectEqual(lifter.ir.SolverEngine.internal_facts, (try solverBackend("internal")).engine);
    try std.testing.expectError(error.UnknownSolverBackend, solverBackend("sample-specific"));
}

test "public emission commands require checked publication arguments" {
    try std.testing.expectEqual(EmissionCommand.unsolved, emissionCommand("emit-luau").?);
    try std.testing.expectEqual(EmissionCommand.unsolved, emissionCommand("emit-luau-checked").?);
    try std.testing.expectEqual(EmissionCommand.solved, emissionCommand("emit-luau-solved").?);
    try std.testing.expectEqual(EmissionCommand.solved, emissionCommand("emit-luau-solved-checked").?);
    try std.testing.expectEqual(@as(usize, 6), emissionArgumentCount(.unsolved));
    try std.testing.expectEqual(@as(usize, 7), emissionArgumentCount(.solved));
    try std.testing.expect(emissionCommand("emit-luau-unchecked") == null);
}

test "fixture registry contains only family-neutral contract cases" {
    try std.testing.expectEqualStrings("generic-arithmetic-module", (try fixtureByName("arithmetic")).program_id);
    try std.testing.expectEqualStrings("generic-absolute-value-module", (try fixtureByName("absolute")).program_id);
    try std.testing.expectEqualStrings("generic-function-reference-identity", (try fixtureByName("function-reference-identity")).program_id);
    try std.testing.expectEqualStrings("generic-dynamic-truthiness", (try fixtureByName("dynamic-truthiness")).program_id);
    try std.testing.expectEqualStrings("generic-variadic-identity-module", (try fixtureByName("variadic-identity")).program_id);
    try std.testing.expectEqualStrings("generic-open-result-pack", (try fixtureByName("open-pack")).program_id);
    try std.testing.expectEqualStrings("generic-immutable-closure-module", (try fixtureByName("immutable-closure")).program_id);
    try std.testing.expectEqualStrings("generic-shared-place-closure-module", (try fixtureByName("shared-place-closure")).program_id);
    try std.testing.expectError(error.UnknownFixture, fixtureByName("sample-family"));
}

test "diagnostic-only commands are labelled in the usage text" {
    const header = "diagnostic-only or unchecked";
    const header_pos = std.mem.indexOf(u8, usage_text, header);
    try std.testing.expect(header_pos != null);
    const diagnostic_only_commands = [_][]const u8{
        "emit-admitted-readable-luau-raw",
        "emit-readable-luau-strategy",
        "resolve-exact-control-ir",
        "emit-function-probe",
    };
    for (diagnostic_only_commands) |command| {
        const command_pos = std.mem.indexOf(u8, usage_text, command);
        try std.testing.expect(command_pos != null);
        try std.testing.expect(command_pos.? > header_pos.?);
    }
    // emit-readable-luau-strategy names its admission refusals as typed diagnostics.
    try std.testing.expect(std.mem.indexOf(u8, usage_text, "no diagnostic lines on refusal") == null);
}

test "normalized publication keeps refreshed proof digests in the published program's allocator" {
    // A program read back from its encoding, as the publication commands read one: its certificate holds a framework
    // digest, which the publication refresh recomputes and stores in the program. std.testing.allocator fails the
    // test when a recomputed digest is allocated where nothing releases it.
    const fixture = lifter.fixtures.arithmetic_module;
    const terms = [_]lifter.ir.SolverTerm{.{
        .id = lifter.ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const queries = [_]lifter.ir.SolverQuery{.{
        .id = lifter.ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = lifter.ir.SolverTermId.fromIndex(0),
    }};
    const claims = [_]lifter.ir.Claim{.{
        .id = lifter.ir.ClaimId.fromIndex(0),
        .subject = .{ .program = {} },
        .predicate = lifter.ir.SolverTermId.fromIndex(0),
        .status = .unproven,
        .required_for_emission = true,
        .evidence = &.{fixture.proof},
        .query = lifter.ir.QueryId.fromIndex(0),
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.claims = &claims;

    var resolved = try lifter.proof_orchestrator.resolveAlloc(
        std.testing.allocator,
        &program,
        lifter.solver_backend.internalFacts(),
    );
    defer resolved.deinit();
    try std.testing.expectEqual(@as(usize, 1), resolved.program.certificates.len);
    const encoded = try lifter.codec.encodeAlloc(std.testing.allocator, &resolved.program);
    defer std.testing.allocator.free(encoded);

    var parsed = try lifter.codec.parse(std.testing.allocator, encoded);
    defer parsed.deinit();
    const recorded = parsed.value.certificates[0].certificate_digest.?;
    try std.testing.expect(lifter.proof_digest.isFrameworkDigest(recorded));

    try prepareNormalizedPublication(std.testing.allocator, parsed.arena.allocator(), &parsed.value);
    const refreshed = parsed.value.certificates[0].certificate_digest.?;
    try std.testing.expect(refreshed.ptr != recorded.ptr);
    try std.testing.expectEqualStrings(recorded, refreshed);

    const published = try lifter.codec.encodeCompactAlloc(std.testing.allocator, &parsed.value);
    defer std.testing.allocator.free(published);
    try std.testing.expect(std.mem.indexOf(u8, published, refreshed) != null);
}
