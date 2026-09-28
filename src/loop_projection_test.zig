const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const emit_luau = @import("emit_luau.zig");
const loop_side_exit = @import("loop_side_exit.zig");
const natural_loop = @import("natural_loop.zig");
const structure = @import("structure.zig");
const structured_escape = @import("structured_escape.zig");
const structural_overlap = @import("structural_overlap.zig");
const validate = @import("validate.zig");

fn expectReadableEmission(program: *const ir.Program) ![]u8 {
    var report = try validate.validate(std.testing.allocator, program, .readable_luau);
    defer report.deinit();
    try std.testing.expect(report.isClean());
    return emit_luau.emitStandardLuauAlloc(std.testing.allocator, program);
}

test "effectful parameterized side exit is owned once after an infinite loop" {
    const function_id = ir.FunctionId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);
    const proof_ids = [_]ir.EvidenceId{proof};
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const choose_first = ir.BlockId.fromIndex(2);
    const choose_second = ir.BlockId.fromIndex(3);
    const first_exit = ir.BlockId.fromIndex(4);
    const second_exit = ir.BlockId.fromIndex(5);
    const direct_exit = ir.BlockId.fromIndex(6);
    const first_continue = ir.BlockId.fromIndex(7);
    const second_continue = ir.BlockId.fromIndex(8);
    const direct_continue = ir.BlockId.fromIndex(9);
    const shared_side = ir.BlockId.fromIndex(10);
    const canonical_exit = ir.BlockId.fromIndex(11);
    const side_parameter = ir.ValueId.fromIndex(7);
    const side_place = ir.PlaceId.fromIndex(0);
    const write_id = ir.InstructionId.fromIndex(0);
    const first_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(5)};
    const second_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(6)};
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = choose_first } } },
        .{ .id = choose_first, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = first_exit },
            .else_edge = .{ .target = choose_second },
        } } },
        .{ .id = choose_second, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = second_exit },
            .else_edge = .{ .target = direct_exit },
        } } },
        .{ .id = first_exit, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = first_continue },
            .else_edge = .{ .target = shared_side, .arguments = &first_arguments },
        } } },
        .{ .id = second_exit, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(3),
            .then_edge = .{ .target = second_continue },
            .else_edge = .{ .target = shared_side, .arguments = &second_arguments },
        } } },
        .{ .id = direct_exit, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(4),
            .then_edge = .{ .target = direct_continue },
            .else_edge = .{ .target = canonical_exit },
        } } },
        .{ .id = first_continue, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = second_continue, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = direct_continue, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{
            .id = shared_side,
            .function = function_id,
            .parameters = &.{side_parameter},
            .instructions = &.{write_id},
            .terminator = .{ .jump = .{ .target = canonical_exit } },
        },
        .{ .id = canonical_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    for (&blocks) |*block| block.evidence = &proof_ids;
    const values = [_]ir.Value{
        .{ .id = ir.ValueId.fromIndex(0), .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = ir.ValueId.fromIndex(1), .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = ir.ValueId.fromIndex(2), .function = function_id, .type = .boolean, .origin = .{ .parameter = 2 } },
        .{ .id = ir.ValueId.fromIndex(3), .function = function_id, .type = .boolean, .origin = .{ .parameter = 3 } },
        .{ .id = ir.ValueId.fromIndex(4), .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } },
        .{ .id = ir.ValueId.fromIndex(5), .function = function_id, .type = .integer, .origin = .{ .parameter = 5 } },
        .{ .id = ir.ValueId.fromIndex(6), .function = function_id, .type = .integer, .origin = .{ .parameter = 6 } },
        .{ .id = side_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = shared_side, .index = 0 } } },
    };
    const places = [_]ir.Place{.{
        .id = side_place,
        .function = function_id,
        .type = .integer,
        .origin = .{ .local = 0 },
        .evidence = &proof_ids,
    }};
    const instructions = [_]ir.Instruction{.{
        .id = write_id,
        .block = shared_side,
        .operation = .{ .place_write = .{ .place = side_place, .value = side_parameter } },
        .results = &.{},
        .effects = .place_write,
        .evidence = &proof_ids,
    }};
    const function: ir.Function = .{
        .id = function_id,
        .parameters = &.{
            ir.ValueId.fromIndex(0),
            ir.ValueId.fromIndex(1),
            ir.ValueId.fromIndex(2),
            ir.ValueId.fromIndex(3),
            ir.ValueId.fromIndex(4),
            ir.ValueId.fromIndex(5),
            ir.ValueId.fromIndex(6),
        },
        .local_places = &.{side_place},
        .blocks = &.{ entry, header, choose_first, choose_second, first_exit, second_exit, direct_exit, first_continue, second_continue, direct_continue, shared_side, canonical_exit },
        .entry_block = entry,
        .evidence = &proof_ids,
    };
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .structural_derivation, .locator = "fixture:shared-parameterized-loop-side-exit" }};
    const program: ir.Program = .{
        .program_id = "shared-parameterized-loop-side-exit",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
        .evidence = &evidence,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var membership = (try natural_loop.collect(std.testing.allocator, &analysis, header)).?;
    defer membership.deinit();
    try std.testing.expectEqual(
        shared_side,
        (try loop_side_exit.selectSharedRegionEntryAlloc(
            std.testing.allocator,
            &analysis,
            membership.bits,
            canonical_exit,
        )).?,
    );
    try std.testing.expectEqual(@as(usize, 1), blocks[shared_side.index()].parameters.len);
    try std.testing.expectEqual(@as(usize, 1), blocks[shared_side.index()].instructions.len);
}

test "direct loop escape reaches an enclosing parameterized join" {
    const function_id = ir.FunctionId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);
    const proof_ids = [_]ir.EvidenceId{proof};
    const entry = ir.BlockId.fromIndex(0);
    const outer_header = ir.BlockId.fromIndex(1);
    const inner_header = ir.BlockId.fromIndex(2);
    const inner_decision = ir.BlockId.fromIndex(3);
    const outer_continue = ir.BlockId.fromIndex(4);
    const join = ir.BlockId.fromIndex(5);
    const terminal = ir.BlockId.fromIndex(6);
    const escape_argument = ir.ValueId.fromIndex(4);
    const fallback_argument = ir.ValueId.fromIndex(5);
    const join_parameter = ir.ValueId.fromIndex(6);
    const escape_arguments = [_]ir.ValueId{escape_argument};
    const fallback_arguments = [_]ir.ValueId{fallback_argument};
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = outer_header },
            .else_edge = .{ .target = join, .arguments = &fallback_arguments },
        } } },
        .{ .id = outer_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = inner_header },
            .else_edge = .{ .target = join, .arguments = &fallback_arguments },
        } } },
        .{ .id = inner_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = inner_decision },
            .else_edge = .{ .target = outer_continue },
        } } },
        .{ .id = inner_decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(3),
            .then_edge = .{ .target = inner_header },
            .else_edge = .{ .target = join, .arguments = &escape_arguments },
        } } },
        .{ .id = outer_continue, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = join, .function = function_id, .parameters = &.{join_parameter}, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{join_parameter} } },
    };
    for (&blocks) |*block| block.evidence = &proof_ids;
    const values = [_]ir.Value{
        .{ .id = ir.ValueId.fromIndex(0), .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = ir.ValueId.fromIndex(1), .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = ir.ValueId.fromIndex(2), .function = function_id, .type = .boolean, .origin = .{ .parameter = 2 } },
        .{ .id = ir.ValueId.fromIndex(3), .function = function_id, .type = .boolean, .origin = .{ .parameter = 3 } },
        .{ .id = escape_argument, .function = function_id, .type = .integer, .origin = .{ .parameter = 4 } },
        .{ .id = fallback_argument, .function = function_id, .type = .integer, .origin = .{ .parameter = 5 } },
        .{ .id = join_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = join, .index = 0 } } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .parameters = &.{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1), ir.ValueId.fromIndex(2), ir.ValueId.fromIndex(3), escape_argument, fallback_argument },
        .blocks = &.{ entry, outer_header, inner_header, inner_decision, outer_continue, join, terminal },
        .entry_block = entry,
        .evidence = &proof_ids,
    };
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .structural_derivation, .locator = "fixture:direct-loop-escape-to-join" }};
    const program: ir.Program = .{
        .program_id = "direct-loop-escape-to-join",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const root_branch = plan.root.nodes[0].branch;
    try std.testing.expect(structured_escape.regionOwnsEscape(root_branch.then_region));
    try std.testing.expectEqual(join, root_branch.then_region.nodes[0].loop.exit_edge.target);

    const source = try expectReadableEmission(&program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "__lifter_escape_") != null);
}

test "direct successor remains a join when another arm may exit the loop" {
    const function_id = ir.FunctionId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);
    const proof_ids = [_]ir.EvidenceId{proof};
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const decision = ir.BlockId.fromIndex(2);
    const shared = ir.BlockId.fromIndex(3);
    const bypass = ir.BlockId.fromIndex(4);
    const exit = ir.BlockId.fromIndex(5);
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = decision },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = shared },
            .else_edge = .{ .target = bypass },
        } } },
        .{ .id = shared, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = bypass, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = shared },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    for (&blocks) |*block| block.evidence = &proof_ids;
    const values = [_]ir.Value{
        .{ .id = ir.ValueId.fromIndex(0), .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = ir.ValueId.fromIndex(1), .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = ir.ValueId.fromIndex(2), .function = function_id, .type = .boolean, .origin = .{ .parameter = 2 } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .parameters = &.{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1), ir.ValueId.fromIndex(2) },
        .blocks = &.{ entry, header, decision, shared, bypass, exit },
        .entry_block = entry,
        .evidence = &proof_ids,
    };
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .structural_derivation, .locator = "fixture:partial-direct-successor-convergence" }};
    const program: ir.Program = .{
        .program_id = "partial-direct-successor-convergence",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const loop = plan.root.nodes[1].loop;
    try std.testing.expectEqual(shared, loop.body_region.nodes[0].branch.join.?);

    const source = try expectReadableEmission(&program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "while ") != null);
}

test "nested infinite loop may exit to its enclosing continue target" {
    const function_id = ir.FunctionId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);
    const proof_ids = [_]ir.EvidenceId{proof};
    const entry = ir.BlockId.fromIndex(0);
    const outer_header = ir.BlockId.fromIndex(1);
    const inner_header = ir.BlockId.fromIndex(2);
    const inner_decision = ir.BlockId.fromIndex(3);
    const inner_body = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = outer_header, .function = function_id, .terminator = .{ .jump = .{ .target = inner_header } } },
        .{ .id = inner_header, .function = function_id, .terminator = .{ .jump = .{ .target = inner_decision } } },
        .{ .id = inner_decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = inner_body },
            .else_edge = .{ .target = outer_header },
        } } },
        .{ .id = inner_body, .function = function_id, .terminator = .{ .jump = .{ .target = inner_header } } },
    };
    for (&blocks) |*block| block.evidence = &proof_ids;
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const function: ir.Function = .{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, outer_header, inner_header, inner_decision, inner_body },
        .entry_block = entry,
        .evidence = &proof_ids,
    };
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .structural_derivation, .locator = "fixture:nested-infinite-loop-enclosing-continue" }};
    const program: ir.Program = .{
        .program_id = "nested-infinite-loop-enclosing-continue",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const outer = plan.root.nodes[1].infinite_loop;
    const inner = outer.body_region.nodes[1].infinite_loop;
    try std.testing.expectEqual(outer_header, inner.exit.?);

    const source = try expectReadableEmission(&program);
    defer std.testing.allocator.free(source);
    try std.testing.expectEqual(@as(usize, 2), std.mem.count(u8, source, "while true do"));
}

test "multiple parameterized side entries preserve deterministic ownership" {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const first = ir.BlockId.fromIndex(2);
    const second = ir.BlockId.fromIndex(3);
    const first_latch = ir.BlockId.fromIndex(4);
    const second_latch = ir.BlockId.fromIndex(5);
    const third_latch = ir.BlockId.fromIndex(6);
    const fourth_latch = ir.BlockId.fromIndex(7);
    const target_a = ir.BlockId.fromIndex(8);
    const target_b = ir.BlockId.fromIndex(9);
    const exit = ir.BlockId.fromIndex(10);
    const condition_a = ir.ValueId.fromIndex(0);
    const condition_b = ir.ValueId.fromIndex(1);
    const condition_c = ir.ValueId.fromIndex(2);
    const condition_d = ir.ValueId.fromIndex(3);
    const argument_a = ir.ValueId.fromIndex(4);
    const argument_b = ir.ValueId.fromIndex(5);
    const target_a_parameter = ir.ValueId.fromIndex(6);
    const target_b_parameter = ir.ValueId.fromIndex(7);
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition_a,
            .then_edge = .{ .target = first },
            .else_edge = .{ .target = second },
        } } },
        .{ .id = first, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition_b,
            .then_edge = .{ .target = target_a, .arguments = &.{argument_a} },
            .else_edge = .{ .target = first_latch },
        } } },
        .{ .id = second, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition_c,
            .then_edge = .{ .target = target_a, .arguments = &.{argument_b} },
            .else_edge = .{ .target = second_latch },
        } } },
        .{ .id = first_latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition_d,
            .then_edge = .{ .target = target_b, .arguments = &.{argument_a} },
            .else_edge = .{ .target = third_latch },
        } } },
        .{ .id = second_latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition_b,
            .then_edge = .{ .target = target_b, .arguments = &.{argument_b} },
            .else_edge = .{ .target = fourth_latch },
        } } },
        .{ .id = third_latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = fourth_latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = target_a, .function = function_id, .parameters = &.{target_a_parameter}, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = target_b, .function = function_id, .parameters = &.{target_b_parameter}, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const values = [_]ir.Value{
        .{ .id = condition_a, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = condition_b, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = condition_c, .function = function_id, .type = .boolean, .origin = .{ .parameter = 2 } },
        .{ .id = condition_d, .function = function_id, .type = .boolean, .origin = .{ .parameter = 3 } },
        .{ .id = argument_a, .function = function_id, .type = .integer, .origin = .{ .parameter = 4 } },
        .{ .id = argument_b, .function = function_id, .type = .integer, .origin = .{ .parameter = 5 } },
        .{ .id = target_a_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_a, .index = 0 } } },
        .{ .id = target_b_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_b, .index = 0 } } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ condition_a, condition_b, condition_c, condition_d, argument_a, argument_b },
        .blocks = &.{ entry, header, first, second, first_latch, second_latch, third_latch, fourth_latch, target_a, target_b, exit },
        .entry_block = entry,
    };
    const program = ir.Program{
        .program_id = "multiple-parameterized-side-entries",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    const membership = [_]bool{ false, true, true, true, true, true, true, true, false, false, false };

    var analysis = try cfg.Analysis.init(allocator, &program, function);
    const selected = try loop_side_exit.selectSharedRegionEntriesAllocWithReplayContext(
        allocator,
        &analysis,
        &membership,
        exit,
        null,
    );
    defer allocator.free(selected);
    try std.testing.expectEqualSlices(ir.BlockId, &.{ target_a, target_b }, selected);
    try std.testing.expect((try loop_side_exit.selectSharedRegionEntryAlloc(
        allocator,
        &analysis,
        &membership,
        exit,
    )) == null);
    analysis.deinit();

    blocks[target_a.index()].parameters = &.{};
    var tampered_analysis = try cfg.Analysis.init(allocator, &program, function);
    defer tampered_analysis.deinit();
    const tampered = try loop_side_exit.selectSharedRegionEntriesAllocWithReplayContext(
        allocator,
        &tampered_analysis,
        &membership,
        exit,
        null,
    );
    defer allocator.free(tampered);
    try std.testing.expectEqualSlices(ir.BlockId, &.{target_b}, tampered);

    // Independently owned side regions may converge only at the canonical
    // exit. A shared non-exit tail must reject the multi-entry set.
    blocks[target_a.index()].terminator = .{ .jump = .{
        .target = target_b,
        .arguments = &.{argument_a},
    } };
    var overlap_analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer overlap_analysis.deinit();
    const overlapping = try loop_side_exit.selectSharedRegionEntriesAllocWithReplayContext(
        allocator,
        &overlap_analysis,
        &membership,
        exit,
        null,
    );
    defer allocator.free(overlapping);
    try std.testing.expectEqual(@as(usize, 0), overlapping.len);
}

test "effectful parameterized jump SCC boundary authenticates its tuple" {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const body = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const seed = ir.ValueId.fromIndex(0);
    const target_parameter = ir.ValueId.fromIndex(1);
    const target_place = ir.PlaceId.fromIndex(0);
    const write = ir.InstructionId.fromIndex(0);
    const canonical_arguments = [_]ir.ValueId{seed};
    const tampered_arguments = [_]ir.ValueId{target_parameter};
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &canonical_arguments,
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{target_parameter}, .instructions = &.{write}, .terminator = .{ .jump = .{ .target = body } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const values = [_]ir.Value{
        .{ .id = seed, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = target_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
    };
    const places = [_]ir.Place{.{
        .id = target_place,
        .function = function_id,
        .type = .integer,
        .origin = .{ .local = 0 },
    }};
    const instructions = [_]ir.Instruction{.{
        .id = write,
        .block = target,
        .operation = .{ .place_write = .{ .place = target_place, .value = target_parameter } },
        .results = &.{},
        .effects = .place_write,
    }};
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{seed},
        .local_places = &.{target_place},
        .blocks = &.{ entry, source, target, body, exit },
        .entry_block = entry,
    };
    const program = ir.Program{
        .program_id = "effectful-parameterized-jump-scc-boundary",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = source,
        .kind = .jump,
        .target = target,
    }};

    var split = (try structural_overlap.findCollisionSplitAlloc(
        allocator,
        &program,
        0,
        target,
        &incoming,
    )) orelse return error.TestUnexpectedResult;
    defer split.deinit();
    try std.testing.expectEqualSlices(ir.BlockId, &.{target}, split.closure);

    blocks[source.index()].terminator = .{ .jump = .{
        .target = target,
        .arguments = &tampered_arguments,
    } };
    try std.testing.expect((try structural_overlap.findCollisionSplitAlloc(
        allocator,
        &program,
        0,
        target,
        &incoming,
    )) == null);
}
