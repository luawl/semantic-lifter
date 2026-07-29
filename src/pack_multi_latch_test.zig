const std = @import("std");
const diagnostics = @import("diagnostics.zig");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const fixtures = @import("fixtures.zig");
const validation = @import("validate.zig");
const emit_luau = @import("emit_luau.zig");
const loop_continue_shape = @import("loop_continue_shape.zig");
const loop_exit_shape = @import("loop_exit_shape.zig");
const natural_loop = @import("natural_loop.zig");
const pack_plan = @import("pack_plan.zig");
const structure = @import("structure.zig");

const fixture_evidence = [_]ir.EvidenceId{fixtures.open_pack_adjust_module.proof};

fn diagnosticCount(report: *const validation.Report, code: diagnostics.Code) usize {
    var count: usize = 0;
    for (report.diagnostics.items) |diagnostic| {
        if (diagnostic.code == code) count += 1;
    }
    return count;
}

fn sharedExitCount(region: *const structure.Region) usize {
    var count: usize = 0;
    for (region.nodes) |node| switch (node) {
        .branch => |branch| {
            count += sharedExitCount(branch.then_region);
            count += sharedExitCount(branch.else_region);
        },
        .loop => |loop| count += sharedExitCount(loop.body_region),
        .latch_loop => |loop| count += sharedExitCount(loop.body_region),
        .infinite_loop => |loop| count += sharedExitCount(loop.body_region),
        .loop_boundary => |control| {
            count += sharedExitCount(control.body_region);
            switch (control.boundary) {
                .shared_exit => count += 1,
                .side_exit => |side_exit| count += sharedExitCount(side_exit.region),
                .side_escape => |side_escape| count += sharedExitCount(side_escape.region),
                .exit, .escape, .terminal => {},
            }
        },
        .block, .loop_control, .loop_terminal => {},
    };
    return count;
}

fn expectOrdinaryPackRoles(program: *const ir.Program, return_block: ir.BlockId) !void {
    const fixture = fixtures.open_pack_adjust_module;
    var plan = try pack_plan.Plan.init(std.testing.allocator, program);
    defer plan.deinit();
    try std.testing.expect(plan.role(fixture.i_call) == .ordinary);
    try std.testing.expect(plan.role(fixture.i_adjust) == .ordinary);
    try std.testing.expect(plan.terminatorRole(return_block) == .ordinary);

    var report = try validation.validate(std.testing.allocator, program, .readable_luau);
    defer report.deinit();
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&report, .variadic_result_arity));
    try std.testing.expectEqual(@as(usize, 2), diagnosticCount(&report, .unsupported_readable_pack_operation));
}

fn expectStoredPackRoles(program: *const ir.Program, return_block: ir.BlockId) !void {
    const fixture = fixtures.open_pack_adjust_module;
    var plan = try pack_plan.Plan.init(std.testing.allocator, program);
    defer plan.deinit();
    try std.testing.expect(plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, plan.role(fixture.i_adjust).stored_adjustment);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        plan.terminatorRole(return_block),
    );

    var report = try validation.validate(std.testing.allocator, program, .readable_luau);
    defer report.deinit();
    try std.testing.expect(report.isClean());
    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, program);
    defer std.testing.allocator.free(source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "producer()"));
}

test "stored pack reentry admits multiple latches only at one canonical exit" {
    const fixture = fixtures.open_pack_adjust_module;
    const split_block = ir.BlockId.fromIndex(fixture.blocks.len);
    const first_latch = ir.BlockId.fromIndex(fixture.blocks.len + 1);
    const second_latch = ir.BlockId.fromIndex(fixture.blocks.len + 2);
    const return_block = ir.BlockId.fromIndex(fixture.blocks.len + 3);
    var blocks = fixture.blocks ++ [_]ir.Block{
        .{
            .id = split_block,
            .function = fixture.f_entry,
            .terminator = .{ .branch = .{
                .condition = fixture.v_callee,
                .then_edge = .{ .target = first_latch },
                .else_edge = .{ .target = second_latch },
            } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = first_latch,
            .function = fixture.f_entry,
            .terminator = .{ .branch = .{
                .condition = fixture.v_first,
                .then_edge = .{ .target = fixture.b_entry },
                .else_edge = .{ .target = return_block },
            } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = second_latch,
            .function = fixture.f_entry,
            .terminator = .{ .branch = .{
                .condition = fixture.v_first,
                .then_edge = .{ .target = fixture.b_entry },
                .else_edge = .{ .target = return_block },
            } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = return_block,
            .function = fixture.f_entry,
            .terminator = .{ .return_expanded = .{
                .values = &.{fixture.v_first},
                .pack = fixture.p_results,
            } },
            .evidence = &fixture_evidence,
        },
    };
    blocks[fixture.b_entry.index()].terminator = .{ .jump = .{ .target = split_block } };
    const function_blocks = [_]ir.BlockId{
        second_latch,
        return_block,
        split_block,
        fixture.b_entry,
        first_latch,
    };
    var functions = fixture.functions;
    functions[fixture.f_entry.index()].blocks = &function_blocks;
    var values = fixture.values;
    values[fixture.v_callee.index()].name_hint = "producer";
    values[fixture.v_first.index()].name_hint = "materialized";
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.values = &values;

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[fixture.f_entry.index()]);
    defer analysis.deinit();
    var structure_plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer structure_plan.deinit();
    const loop = structure_plan.root.nodes[0].latch_loop;
    try std.testing.expectEqual(@as(usize, 2), loop.latch_count);
    try std.testing.expectEqual(return_block, loop.exit);

    try expectStoredPackRoles(&program, return_block);

    const first_exit_forward = ir.BlockId.fromIndex(blocks.len);
    const second_exit_forward = ir.BlockId.fromIndex(blocks.len + 1);
    var forwarded_exit_blocks = blocks ++ [_]ir.Block{
        .{
            .id = first_exit_forward,
            .function = fixture.f_entry,
            .terminator = .{ .jump = .{ .target = return_block } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = second_exit_forward,
            .function = fixture.f_entry,
            .terminator = .{ .jump = .{ .target = return_block } },
            .evidence = &fixture_evidence,
        },
    };
    forwarded_exit_blocks[first_latch.index()].terminator.branch.else_edge = .{ .target = first_exit_forward };
    forwarded_exit_blocks[second_latch.index()].terminator.branch.else_edge = .{ .target = second_exit_forward };
    const forwarded_exit_function_blocks = function_blocks ++ [_]ir.BlockId{
        first_exit_forward,
        second_exit_forward,
    };
    var forwarded_exit_functions = functions;
    forwarded_exit_functions[fixture.f_entry.index()].blocks = &forwarded_exit_function_blocks;
    var forwarded_exit_program = program;
    forwarded_exit_program.functions = &forwarded_exit_functions;
    forwarded_exit_program.blocks = &forwarded_exit_blocks;
    var forwarded_exit_core_report = try validation.validate(std.testing.allocator, &forwarded_exit_program, .core);
    defer forwarded_exit_core_report.deinit();
    try std.testing.expect(forwarded_exit_core_report.isClean());
    try expectStoredPackRoles(&forwarded_exit_program, return_block);

    var shared_exit_blocks = forwarded_exit_blocks;
    shared_exit_blocks[second_latch.index()].terminator.branch.else_edge = .{ .target = first_exit_forward };
    var shared_exit_program = forwarded_exit_program;
    shared_exit_program.blocks = &shared_exit_blocks;
    var shared_exit_core_report = try validation.validate(std.testing.allocator, &shared_exit_program, .core);
    defer shared_exit_core_report.deinit();
    try std.testing.expect(shared_exit_core_report.isClean());
    var shared_exit_pack_plan = try pack_plan.Plan.init(std.testing.allocator, &shared_exit_program);
    defer shared_exit_pack_plan.deinit();
    try std.testing.expect(shared_exit_pack_plan.role(fixture.i_call) == .stored_invocation_producer);
    var shared_exit_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &shared_exit_program,
        forwarded_exit_functions[fixture.f_entry.index()],
    );
    defer shared_exit_analysis.deinit();
    var shared_exit_structure = try structure.Plan.init(std.testing.allocator, &shared_exit_analysis);
    defer shared_exit_structure.deinit();
    const shared_loop = shared_exit_structure.root.nodes[0].latch_loop;
    const shared_paths = shared_loop.shared_exits.?;
    try std.testing.expectEqual(@as(usize, 1), shared_paths.blocks.len);
    try std.testing.expectEqual(@as(usize, 2), shared_paths.entries.len);
    try std.testing.expectEqual(first_exit_forward, shared_paths.blocks[0]);
    try std.testing.expectEqual(@as(usize, 2), sharedExitCount(shared_loop.body_region));
    try loop_exit_shape.validateAllAlloc(std.testing.allocator, &shared_exit_program, shared_paths);
    const first_exit_entry = shared_paths.entryRef(.{
        .source = first_latch,
        .kind = .branch_else,
        .target = first_exit_forward,
    }).?;
    const first_route_index = shared_paths.route_indices[0];
    shared_paths.route_indices[0] = @intCast(shared_paths.blocks.len);
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        loop_exit_shape.validateAllAlloc(std.testing.allocator, &shared_exit_program, shared_paths),
    );
    shared_paths.route_indices[0] = first_route_index;
    shared_exit_blocks[first_latch.index()].terminator.branch.else_edge.target = second_exit_forward;
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        loop_exit_shape.validateEntryAlloc(std.testing.allocator, &shared_exit_program, first_exit_entry),
    );
    shared_exit_blocks[first_latch.index()].terminator.branch.else_edge.target = first_exit_forward;
    try loop_exit_shape.validateAllAlloc(std.testing.allocator, &shared_exit_program, shared_paths);
    var shared_exit_readable = try validation.validate(std.testing.allocator, &shared_exit_program, .readable_luau);
    defer shared_exit_readable.deinit();
    try std.testing.expect(shared_exit_readable.isClean());
    const shared_exit_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &shared_exit_program);
    defer std.testing.allocator.free(shared_exit_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, shared_exit_source, "producer()"));

    var partial_shared_blocks = forwarded_exit_blocks;
    partial_shared_blocks[first_exit_forward.index()].terminator.jump.target = second_exit_forward;
    var partial_shared_program = forwarded_exit_program;
    partial_shared_program.blocks = &partial_shared_blocks;
    var partial_shared_core_report = try validation.validate(std.testing.allocator, &partial_shared_program, .core);
    defer partial_shared_core_report.deinit();
    try std.testing.expect(partial_shared_core_report.isClean());
    try expectStoredPackRoles(&partial_shared_program, return_block);
    var partial_shared_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &partial_shared_program,
        forwarded_exit_functions[fixture.f_entry.index()],
    );
    defer partial_shared_analysis.deinit();
    var partial_shared_structure = try structure.Plan.init(std.testing.allocator, &partial_shared_analysis);
    defer partial_shared_structure.deinit();
    const partial_shared_loop = partial_shared_structure.root.nodes[0].latch_loop;
    const partial_shared_paths = partial_shared_loop.shared_exits.?;
    try std.testing.expectEqual(@as(usize, 2), partial_shared_paths.blocks.len);
    try std.testing.expectEqual(@as(usize, 2), partial_shared_paths.entries.len);
    try std.testing.expectEqual(@as(usize, 2), sharedExitCount(partial_shared_loop.body_region));
    const partial_first_entry = partial_shared_paths.entryRef(.{
        .source = first_latch,
        .kind = .branch_else,
        .target = first_exit_forward,
    }).?.value().?;
    const partial_second_entry = partial_shared_paths.entryRef(.{
        .source = second_latch,
        .kind = .branch_else,
        .target = second_exit_forward,
    }).?.value().?;
    try std.testing.expectEqual(@as(u32, 2), partial_first_entry.route_len);
    try std.testing.expectEqual(@as(u32, 1), partial_second_entry.route_len);
    const partial_shared_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &partial_shared_program);
    defer std.testing.allocator.free(partial_shared_source);
    try std.testing.expectEqualSlices(u8, shared_exit_source, partial_shared_source);

    const third_split = ir.BlockId.fromIndex(forwarded_exit_blocks.len);
    const third_latch = ir.BlockId.fromIndex(forwarded_exit_blocks.len + 1);
    var mixed_exit_blocks = shared_exit_blocks ++ [_]ir.Block{
        .{
            .id = third_split,
            .function = fixture.f_entry,
            .terminator = .{ .branch = .{
                .condition = fixture.v_callee,
                .then_edge = .{ .target = second_latch },
                .else_edge = .{ .target = third_latch },
            } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = third_latch,
            .function = fixture.f_entry,
            .terminator = .{ .branch = .{
                .condition = fixture.v_first,
                .then_edge = .{ .target = fixture.b_entry },
                .else_edge = .{ .target = return_block },
            } },
            .evidence = &fixture_evidence,
        },
    };
    mixed_exit_blocks[split_block.index()].terminator.branch.else_edge.target = third_split;
    const mixed_exit_function_blocks = forwarded_exit_function_blocks ++ [_]ir.BlockId{
        third_split,
        third_latch,
    };
    var mixed_exit_functions = forwarded_exit_functions;
    mixed_exit_functions[fixture.f_entry.index()].blocks = &mixed_exit_function_blocks;
    var mixed_exit_program = shared_exit_program;
    mixed_exit_program.blocks = &mixed_exit_blocks;
    mixed_exit_program.functions = &mixed_exit_functions;
    var mixed_exit_report = try validation.validate(std.testing.allocator, &mixed_exit_program, .core);
    defer mixed_exit_report.deinit();
    try std.testing.expect(mixed_exit_report.isClean());
    try expectStoredPackRoles(&mixed_exit_program, return_block);
    var mixed_exit_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &mixed_exit_program,
        mixed_exit_functions[fixture.f_entry.index()],
    );
    defer mixed_exit_analysis.deinit();
    var mixed_exit_structure = try structure.Plan.init(std.testing.allocator, &mixed_exit_analysis);
    defer mixed_exit_structure.deinit();
    const mixed_exit_loop = mixed_exit_structure.root.nodes[0].latch_loop;
    try std.testing.expectEqual(@as(usize, 3), mixed_exit_loop.latch_count);
    try std.testing.expectEqual(@as(usize, 2), mixed_exit_loop.shared_exits.?.entries.len);
    try std.testing.expectEqual(@as(usize, 2), sharedExitCount(mixed_exit_loop.body_region));
    const mixed_exit_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &mixed_exit_program);
    defer std.testing.allocator.free(mixed_exit_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, mixed_exit_source, "producer()"));

    const group_second_split = ir.BlockId.fromIndex(forwarded_exit_blocks.len);
    const group_third_split = ir.BlockId.fromIndex(forwarded_exit_blocks.len + 1);
    const group_third_latch = ir.BlockId.fromIndex(forwarded_exit_blocks.len + 2);
    const group_fourth_latch = ir.BlockId.fromIndex(forwarded_exit_blocks.len + 3);
    var grouped_exit_blocks = forwarded_exit_blocks ++ [_]ir.Block{
        .{
            .id = group_second_split,
            .function = fixture.f_entry,
            .terminator = .{ .branch = .{
                .condition = fixture.v_callee,
                .then_edge = .{ .target = second_latch },
                .else_edge = .{ .target = group_third_split },
            } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = group_third_split,
            .function = fixture.f_entry,
            .terminator = .{ .branch = .{
                .condition = fixture.v_callee,
                .then_edge = .{ .target = group_third_latch },
                .else_edge = .{ .target = group_fourth_latch },
            } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = group_third_latch,
            .function = fixture.f_entry,
            .terminator = .{ .branch = .{
                .condition = fixture.v_first,
                .then_edge = .{ .target = fixture.b_entry },
                .else_edge = .{ .target = second_exit_forward },
            } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = group_fourth_latch,
            .function = fixture.f_entry,
            .terminator = .{ .branch = .{
                .condition = fixture.v_first,
                .then_edge = .{ .target = fixture.b_entry },
                .else_edge = .{ .target = second_exit_forward },
            } },
            .evidence = &fixture_evidence,
        },
    };
    grouped_exit_blocks[split_block.index()].terminator.branch.else_edge.target = group_second_split;
    grouped_exit_blocks[second_latch.index()].terminator.branch.else_edge.target = first_exit_forward;
    const grouped_exit_function_blocks = forwarded_exit_function_blocks ++ [_]ir.BlockId{
        group_second_split,
        group_third_split,
        group_third_latch,
        group_fourth_latch,
    };
    var grouped_exit_functions = forwarded_exit_functions;
    grouped_exit_functions[fixture.f_entry.index()].blocks = &grouped_exit_function_blocks;
    var grouped_exit_program = forwarded_exit_program;
    grouped_exit_program.blocks = &grouped_exit_blocks;
    grouped_exit_program.functions = &grouped_exit_functions;
    var grouped_exit_report = try validation.validate(std.testing.allocator, &grouped_exit_program, .core);
    defer grouped_exit_report.deinit();
    try std.testing.expect(grouped_exit_report.isClean());
    try expectStoredPackRoles(&grouped_exit_program, return_block);
    var grouped_exit_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &grouped_exit_program,
        grouped_exit_functions[fixture.f_entry.index()],
    );
    defer grouped_exit_analysis.deinit();
    var grouped_exit_structure = try structure.Plan.init(std.testing.allocator, &grouped_exit_analysis);
    defer grouped_exit_structure.deinit();
    const grouped_exit_loop = grouped_exit_structure.root.nodes[0].latch_loop;
    const grouped_exit_paths = grouped_exit_loop.shared_exits.?;
    try std.testing.expectEqual(@as(usize, 4), grouped_exit_loop.latch_count);
    try std.testing.expectEqual(@as(usize, 2), grouped_exit_paths.blocks.len);
    try std.testing.expectEqual(@as(usize, 4), grouped_exit_paths.entries.len);
    try std.testing.expectEqual(@as(usize, 4), sharedExitCount(grouped_exit_loop.body_region));
    const grouped_first_entry = grouped_exit_paths.entryRef(.{
        .source = first_latch,
        .kind = .branch_else,
        .target = first_exit_forward,
    }).?.value().?;
    const grouped_route_start: usize = grouped_first_entry.route_start;
    const grouped_route_index = grouped_exit_paths.route_indices[grouped_route_start];
    grouped_exit_paths.route_indices[grouped_route_start] = if (grouped_route_index == 0) 1 else 0;
    try std.testing.expectError(
        error.UnsupportedControlFlow,
        loop_exit_shape.validateAllAlloc(std.testing.allocator, &grouped_exit_program, grouped_exit_paths),
    );
    grouped_exit_paths.route_indices[grouped_route_start] = grouped_route_index;
    try loop_exit_shape.validateAllAlloc(std.testing.allocator, &grouped_exit_program, grouped_exit_paths);
    const grouped_exit_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &grouped_exit_program);
    defer std.testing.allocator.free(grouped_exit_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, grouped_exit_source, "producer()"));
    var reordered_grouped_blocks = grouped_exit_function_blocks;
    std.mem.reverse(ir.BlockId, &reordered_grouped_blocks);
    var reordered_grouped_functions = grouped_exit_functions;
    reordered_grouped_functions[fixture.f_entry.index()].blocks = &reordered_grouped_blocks;
    var reordered_grouped_program = grouped_exit_program;
    reordered_grouped_program.functions = &reordered_grouped_functions;
    var reordered_grouped_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &reordered_grouped_program,
        reordered_grouped_functions[fixture.f_entry.index()],
    );
    defer reordered_grouped_analysis.deinit();
    var reordered_grouped_structure = try structure.Plan.init(std.testing.allocator, &reordered_grouped_analysis);
    defer reordered_grouped_structure.deinit();
    try std.testing.expectEqual(@as(usize, 4), reordered_grouped_structure.root.nodes[0].latch_loop.shared_exits.?.entries.len);
    const reordered_grouped_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &reordered_grouped_program);
    defer std.testing.allocator.free(reordered_grouped_source);
    try std.testing.expectEqualSlices(u8, grouped_exit_source, reordered_grouped_source);

    var external_entry_blocks = shared_exit_blocks;
    external_entry_blocks[second_exit_forward.index()].terminator = .{ .branch = .{
        .condition = fixture.v_callee,
        .then_edge = .{ .target = fixture.b_entry },
        .else_edge = .{ .target = first_exit_forward },
    } };
    var external_entry_functions = forwarded_exit_functions;
    external_entry_functions[fixture.f_entry.index()].entry_block = second_exit_forward;
    var external_entry_program = shared_exit_program;
    external_entry_program.blocks = &external_entry_blocks;
    external_entry_program.functions = &external_entry_functions;
    var external_entry_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &external_entry_program,
        external_entry_functions[fixture.f_entry.index()],
    );
    defer external_entry_analysis.deinit();
    var external_entry_membership = (try natural_loop.collect(
        std.testing.allocator,
        &external_entry_analysis,
        fixture.b_entry,
    )).?;
    defer external_entry_membership.deinit();
    const external_entry_shape = (try natural_loop.classifyPostTested(
        &external_entry_analysis,
        fixture.b_entry,
        external_entry_membership.bits,
    )).?;
    var external_entry_latches = try natural_loop.collectExitLatches(
        std.testing.allocator,
        &external_entry_analysis,
        fixture.b_entry,
        external_entry_membership.bits,
        external_entry_shape.exit,
    );
    defer external_entry_latches.deinit();
    try std.testing.expectError(
        error.UnsupportedShape,
        loop_exit_shape.auditSharedAlloc(
            std.testing.allocator,
            &external_entry_analysis,
            fixture.b_entry,
            external_entry_membership.bits,
            external_entry_latches.bits,
            external_entry_shape.exit,
        ),
    );

    const exit_forward_parameter = ir.ValueId.fromIndex(values.len);
    var parameterized_exit_values = values ++ [_]ir.Value{.{
        .id = exit_forward_parameter,
        .function = fixture.f_entry,
        .type = .dynamic,
        .origin = .{ .block_parameter = .{ .block = first_exit_forward, .index = 0 } },
    }};
    var parameterized_exit_blocks = forwarded_exit_blocks;
    parameterized_exit_blocks[first_exit_forward.index()].parameters = &.{exit_forward_parameter};
    parameterized_exit_blocks[first_latch.index()].terminator.branch.else_edge.arguments = &.{fixture.v_first};
    var parameterized_exit_program = forwarded_exit_program;
    parameterized_exit_program.blocks = &parameterized_exit_blocks;
    parameterized_exit_program.values = &parameterized_exit_values;
    var parameterized_exit_core_report = try validation.validate(std.testing.allocator, &parameterized_exit_program, .core);
    defer parameterized_exit_core_report.deinit();
    try std.testing.expect(parameterized_exit_core_report.isClean());
    try expectOrdinaryPackRoles(&parameterized_exit_program, return_block);

    const alternate_exit = ir.BlockId.fromIndex(blocks.len);
    var alternate_blocks = blocks ++ [_]ir.Block{.{
        .id = alternate_exit,
        .function = fixture.f_entry,
        .terminator = .{ .return_values = &.{fixture.v_first} },
        .evidence = &fixture_evidence,
    }};
    alternate_blocks[second_latch.index()].terminator.branch.else_edge = .{ .target = alternate_exit };
    const alternate_function_blocks = function_blocks ++ [_]ir.BlockId{alternate_exit};
    var alternate_functions = functions;
    alternate_functions[fixture.f_entry.index()].blocks = &alternate_function_blocks;
    var alternate_program = program;
    alternate_program.functions = &alternate_functions;
    alternate_program.blocks = &alternate_blocks;
    var alternate_core_report = try validation.validate(std.testing.allocator, &alternate_program, .core);
    defer alternate_core_report.deinit();
    try std.testing.expect(alternate_core_report.isClean());
    try expectOrdinaryPackRoles(&alternate_program, return_block);

    const early_continue = ir.BlockId.fromIndex(blocks.len);
    var combined_blocks = blocks ++ [_]ir.Block{.{
        .id = early_continue,
        .function = fixture.f_entry,
        .terminator = .{ .branch = .{
            .condition = fixture.v_callee,
            .then_edge = .{ .target = fixture.b_entry },
            .else_edge = .{ .target = split_block },
        } },
        .evidence = &fixture_evidence,
    }};
    combined_blocks[fixture.b_entry.index()].terminator.jump.target = early_continue;
    const combined_function_blocks = function_blocks ++ [_]ir.BlockId{early_continue};
    var combined_functions = functions;
    combined_functions[fixture.f_entry.index()].blocks = &combined_function_blocks;
    var combined_program = program;
    combined_program.functions = &combined_functions;
    combined_program.blocks = &combined_blocks;
    var combined_core_report = try validation.validate(std.testing.allocator, &combined_program, .core);
    defer combined_core_report.deinit();
    try std.testing.expect(combined_core_report.isClean());
    try expectStoredPackRoles(&combined_program, return_block);

    var combined_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &combined_program,
        combined_functions[fixture.f_entry.index()],
    );
    defer combined_analysis.deinit();
    var combined_membership = (try natural_loop.collect(
        std.testing.allocator,
        &combined_analysis,
        fixture.b_entry,
    )).?;
    defer combined_membership.deinit();
    const combined_shape = (try natural_loop.classifyPostTested(
        &combined_analysis,
        fixture.b_entry,
        combined_membership.bits,
    )).?;
    var combined_latches = try natural_loop.collectExitLatches(
        std.testing.allocator,
        &combined_analysis,
        fixture.b_entry,
        combined_membership.bits,
        combined_shape.exit,
    );
    defer combined_latches.deinit();
    try std.testing.expectEqual(@as(usize, 2), combined_latches.count);
    const complete_audit = try loop_continue_shape.auditAlloc(
        std.testing.allocator,
        &combined_analysis,
        fixture.b_entry,
        combined_membership.bits,
        combined_latches.bits,
    );
    try std.testing.expect(complete_audit == null);

    combined_latches.bits[combined_analysis.blockIndex(second_latch).?] = false;
    try std.testing.expectError(
        error.UnsupportedShape,
        loop_continue_shape.auditAlloc(
            std.testing.allocator,
            &combined_analysis,
            fixture.b_entry,
            combined_membership.bits,
            combined_latches.bits,
        ),
    );

    const second_continue_decision = ir.BlockId.fromIndex(combined_blocks.len);
    const shared_relay = ir.BlockId.fromIndex(combined_blocks.len + 1);
    var shared_blocks = combined_blocks ++ [_]ir.Block{
        .{
            .id = second_continue_decision,
            .function = fixture.f_entry,
            .terminator = .{ .branch = .{
                .condition = fixture.v_callee,
                .then_edge = .{ .target = shared_relay },
                .else_edge = .{ .target = split_block },
            } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = shared_relay,
            .function = fixture.f_entry,
            .terminator = .{ .jump = .{ .target = fixture.b_entry } },
            .evidence = &fixture_evidence,
        },
    };
    shared_blocks[early_continue.index()].terminator.branch.then_edge = .{ .target = shared_relay };
    shared_blocks[early_continue.index()].terminator.branch.else_edge = .{ .target = second_continue_decision };
    const shared_function_blocks = combined_function_blocks ++ [_]ir.BlockId{
        second_continue_decision,
        shared_relay,
    };
    var shared_functions = combined_functions;
    shared_functions[fixture.f_entry.index()].blocks = &shared_function_blocks;
    var shared_program = combined_program;
    shared_program.functions = &shared_functions;
    shared_program.blocks = &shared_blocks;
    var shared_core_report = try validation.validate(std.testing.allocator, &shared_program, .core);
    defer shared_core_report.deinit();
    try std.testing.expect(shared_core_report.isClean());
    try expectStoredPackRoles(&shared_program, return_block);

    var shared_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &shared_program,
        shared_functions[fixture.f_entry.index()],
    );
    defer shared_analysis.deinit();
    var shared_structure = try structure.Plan.init(std.testing.allocator, &shared_analysis);
    defer shared_structure.deinit();
    const shared_reentries = shared_structure.root.nodes[0].latch_loop.shared_reentries.?;
    try std.testing.expectEqualSlices(ir.BlockId, &.{shared_relay}, shared_reentries.blocks);
    try std.testing.expectEqual(@as(usize, 2), shared_reentries.entries.len);

    const combined_shared_exit = ir.BlockId.fromIndex(shared_blocks.len);
    var combined_shared_blocks = shared_blocks ++ [_]ir.Block{.{
        .id = combined_shared_exit,
        .function = fixture.f_entry,
        .terminator = .{ .jump = .{ .target = return_block } },
        .evidence = &fixture_evidence,
    }};
    combined_shared_blocks[first_latch.index()].terminator.branch.else_edge = .{ .target = combined_shared_exit };
    combined_shared_blocks[second_latch.index()].terminator.branch.else_edge = .{ .target = combined_shared_exit };
    const combined_shared_function_blocks = shared_function_blocks ++ [_]ir.BlockId{combined_shared_exit};
    var combined_shared_functions = shared_functions;
    combined_shared_functions[fixture.f_entry.index()].blocks = &combined_shared_function_blocks;
    var combined_shared_program = shared_program;
    combined_shared_program.functions = &combined_shared_functions;
    combined_shared_program.blocks = &combined_shared_blocks;
    var combined_shared_report = try validation.validate(std.testing.allocator, &combined_shared_program, .core);
    defer combined_shared_report.deinit();
    try std.testing.expect(combined_shared_report.isClean());
    try expectStoredPackRoles(&combined_shared_program, return_block);
    var combined_shared_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &combined_shared_program,
        combined_shared_functions[fixture.f_entry.index()],
    );
    defer combined_shared_analysis.deinit();
    var combined_shared_structure = try structure.Plan.init(std.testing.allocator, &combined_shared_analysis);
    defer combined_shared_structure.deinit();
    const combined_shared_loop = combined_shared_structure.root.nodes[0].latch_loop;
    try std.testing.expectEqual(@as(usize, 2), combined_shared_loop.shared_reentries.?.entries.len);
    try std.testing.expectEqual(@as(usize, 2), combined_shared_loop.shared_exits.?.entries.len);
    try std.testing.expectEqual(@as(usize, 2), sharedExitCount(combined_shared_loop.body_region));
    var combined_shared_readable = try validation.validate(std.testing.allocator, &combined_shared_program, .readable_luau);
    defer combined_shared_readable.deinit();
    try std.testing.expect(combined_shared_readable.isClean());
    const combined_shared_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &combined_shared_program);
    defer std.testing.allocator.free(combined_shared_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, combined_shared_source, "producer()"));
}
