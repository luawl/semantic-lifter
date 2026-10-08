const std = @import("std");
const lifter = @import("semantic_lifter");
const ir = lifter.ir;
const cfg = lifter.cfg;
const Plan = lifter.structure.Plan;

test "nested side escape participates in the structure free-target census" {
    const target = ir.BlockId.fromIndex(4);
    var body_region: lifter.structure.Region = .{ .nodes = &.{}, .stop = null, .loop_exit = null };
    var side_region: lifter.structure.Region = .{ .nodes = &.{}, .stop = target, .loop_exit = null };
    var nodes = [_]lifter.structure.Node{.{ .loop_boundary = .{
        .block = ir.BlockId.fromIndex(0),
        .body_edge = .{ .target = ir.BlockId.fromIndex(1) },
        .body_region = &body_region,
        .boundary = .{ .side_escape = .{
            .entry_edge = .{ .target = ir.BlockId.fromIndex(2) },
            .region = &side_region,
            .target = target,
        } },
        .body_on_true = true,
    } }};
    const free_region: lifter.structure.Region = .{ .nodes = &nodes, .stop = null, .loop_exit = null };
    const free_targets = try lifter.structure.regionFreeTargetsAlloc(std.testing.allocator, &free_region);
    defer std.testing.allocator.free(free_targets);
    try std.testing.expectEqualSlices(ir.BlockId, &.{target}, free_targets);

    const captured_region: lifter.structure.Region = .{ .nodes = &nodes, .stop = target, .loop_exit = null };
    const captured_targets = try lifter.structure.regionFreeTargetsAlloc(std.testing.allocator, &captured_region);
    defer std.testing.allocator.free(captured_targets);
    try std.testing.expectEqual(@as(usize, 0), captured_targets.len);
    try std.testing.expect(lifter.structure.regionOwnsEscape(&captured_region));
}

test "nested loop escape preserves an enclosing join transfer" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const outer_header = ir.BlockId.fromIndex(1);
    const inner_header = ir.BlockId.fromIndex(2);
    const inner_decision = ir.BlockId.fromIndex(3);
    const outer_continue = ir.BlockId.fromIndex(4);
    const join = ir.BlockId.fromIndex(5);
    const terminal = ir.BlockId.fromIndex(6);
    const escape_argument = ir.ValueId.fromIndex(4);
    const join_parameter = ir.ValueId.fromIndex(5);
    const escape_arguments = [_]ir.ValueId{escape_argument};
    const fallback_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(3)};
    const blocks = [_]ir.Block{
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
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1), ir.ValueId.fromIndex(2), ir.ValueId.fromIndex(3), escape_argument },
        .blocks = &.{ entry, outer_header, inner_header, inner_decision, outer_continue, join, terminal },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "nested-loop-escape",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const root_branch = plan.root.nodes[0].branch;
    try std.testing.expectEqual(join, root_branch.join.?);
    try std.testing.expect(lifter.structured_escape.regionOwnsEscape(root_branch.then_region));
    try std.testing.expectEqual(@as(usize, 1), lifter.structured_escape.maxOwnedDepth(plan.root));
    const outer = root_branch.then_region.nodes[0].loop;
    try std.testing.expect(outer.exit_is_escape);
    try std.testing.expectEqual(join, outer.exit_edge.target);
    const inner = outer.body_region.nodes[0].loop;
    const escape = inner.body_region.nodes[0].loop_boundary.boundary.escape;
    try std.testing.expectEqual(join, escape.target);
    try std.testing.expectEqualSlices(ir.ValueId, &escape_arguments, escape.arguments);
}

test "nested loop exit to an enclosing loop boundary is an escape" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const outer_header = ir.BlockId.fromIndex(1);
    const inner_header = ir.BlockId.fromIndex(2);
    const inner_body = ir.BlockId.fromIndex(3);
    const outer_exit = ir.BlockId.fromIndex(4);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = outer_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = inner_header },
            .else_edge = .{ .target = outer_exit },
        } } },
        .{ .id = inner_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = inner_body },
            .else_edge = .{ .target = outer_exit },
        } } },
        .{ .id = inner_body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = inner_header },
            .else_edge = .{ .target = outer_header },
        } } },
        .{ .id = outer_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1), ir.ValueId.fromIndex(2) },
        .blocks = &.{ entry, outer_header, inner_header, inner_body, outer_exit },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "nested-loop-enclosing-exit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 3), plan.root.nodes.len);
    const outer = plan.root.nodes[1].loop;
    try std.testing.expectEqual(outer_exit, outer.exit_edge.target);
    try std.testing.expectEqual(@as(usize, 1), outer.body_region.nodes.len);
    const inner = outer.body_region.nodes[0].loop;
    try std.testing.expectEqual(outer_exit, inner.exit_edge.target);
    try std.testing.expect(inner.exit_is_escape);
}

test "nested loop side path forwards to an enclosing continue" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const outer_header = ir.BlockId.fromIndex(1);
    const inner_header = ir.BlockId.fromIndex(2);
    const inner_body = ir.BlockId.fromIndex(3);
    const side_path = ir.BlockId.fromIndex(4);
    const inner_exit = ir.BlockId.fromIndex(5);
    const outer_latch = ir.BlockId.fromIndex(6);
    const terminal = ir.BlockId.fromIndex(7);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = outer_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = inner_header },
            .else_edge = .{ .target = terminal },
        } } },
        .{ .id = inner_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = inner_body },
            .else_edge = .{ .target = inner_exit },
        } } },
        .{ .id = inner_body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = inner_header },
            .else_edge = .{ .target = side_path },
        } } },
        .{ .id = side_path, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = inner_exit, .function = function_id, .terminator = .{ .jump = .{ .target = outer_latch } } },
        .{ .id = outer_latch, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1), ir.ValueId.fromIndex(2) },
        .blocks = &.{ inner_body, entry, terminal, inner_exit, outer_header, side_path, outer_latch, inner_header },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "nested-loop-forwarded-continue",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const outer = plan.root.nodes[1].loop;
    const inner = outer.body_region.nodes[0].loop;
    const side_escape = inner.body_region.nodes[0].loop_boundary.boundary.side_escape;
    try std.testing.expectEqual(side_path, side_escape.entry_edge.target);
    try std.testing.expectEqual(outer_header, side_escape.target);
    try std.testing.expectEqual(outer_header, side_escape.region.stop.?);
    try std.testing.expectEqual(side_path, side_escape.region.nodes[0].block);
}

test "nested loop side path forwards to an enclosing infinite continue" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const outer_header = ir.BlockId.fromIndex(1);
    const inner_header = ir.BlockId.fromIndex(2);
    const inner_body = ir.BlockId.fromIndex(3);
    const side_path = ir.BlockId.fromIndex(4);
    const outer_latch = ir.BlockId.fromIndex(5);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = outer_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = inner_header },
            .else_edge = .{ .target = outer_latch },
        } } },
        .{ .id = inner_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = inner_body },
            .else_edge = .{ .target = outer_latch },
        } } },
        .{ .id = inner_body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = inner_header },
            .else_edge = .{ .target = side_path },
        } } },
        .{ .id = side_path, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = outer_latch, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1), ir.ValueId.fromIndex(2) },
        .blocks = &.{ inner_body, entry, outer_header, side_path, outer_latch, inner_header },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "nested-loop-forwarded-infinite-continue",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const outer = plan.root.nodes[1].infinite_loop;
    const inner = outer.body_region.nodes[0].branch.then_region.nodes[0].loop;
    const side_escape = inner.body_region.nodes[0].loop_boundary.boundary.side_escape;
    try std.testing.expectEqual(side_path, side_escape.entry_edge.target);
    try std.testing.expectEqual(outer_header, side_escape.target);
    try std.testing.expectEqual(outer_header, side_escape.region.stop.?);
    try std.testing.expectEqual(side_path, side_escape.region.nodes[0].block);
}

test "loop branch factors a shared tail bypassed only by continue" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const decision = ir.BlockId.fromIndex(1);
    const nested = ir.BlockId.fromIndex(2);
    const shared = ir.BlockId.fromIndex(3);
    const continue_path = ir.BlockId.fromIndex(4);
    const terminal = ir.BlockId.fromIndex(5);
    const continue_instruction = ir.InstructionId.fromIndex(0);
    const continue_value = ir.ValueId.fromIndex(3);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = decision },
            .else_edge = .{ .target = terminal },
        } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = nested },
            .else_edge = .{ .target = shared },
        } } },
        .{ .id = nested, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = shared },
            .else_edge = .{ .target = continue_path },
        } } },
        .{ .id = shared, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = continue_path, .function = function_id, .instructions = &.{continue_instruction}, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1), ir.ValueId.fromIndex(2) },
        .blocks = &.{ nested, terminal, header, shared, decision, continue_path },
        .entry_block = header,
    }};
    const program: ir.Program = .{
        .program_id = "loop-shared-tail-before-continue",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{.{
            .id = continue_instruction,
            .block = continue_path,
            .operation = .{ .constant = .{ .integer = "1" } },
            .results = &.{continue_value},
            .effects = .pure,
        }},
        .values = &.{.{
            .id = continue_value,
            .function = function_id,
            .type = .integer,
            .origin = .{ .instruction_result = .{ .instruction = continue_instruction, .index = 0 } },
        }},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[0].loop;
    const branch = loop.body_region.nodes[0].branch;
    try std.testing.expectEqual(shared, branch.join.?);
    try std.testing.expectEqual(shared, loop.body_region.nodes[1].block);
}

test "pre-tested loop owns an effectful secondary path that must terminate" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const primary_path = ir.BlockId.fromIndex(3);
    const secondary_path = ir.BlockId.fromIndex(4);
    const primary_return = ir.BlockId.fromIndex(5);
    const secondary_return = ir.BlockId.fromIndex(6);
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = primary_path },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = secondary_path },
        } } },
        .{ .id = primary_path, .function = function_id, .terminator = .{ .jump = .{ .target = primary_return } } },
        .{ .id = secondary_path, .function = function_id, .terminator = .{ .jump = .{ .target = secondary_return } } },
        .{ .id = primary_return, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = secondary_return, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ ir.ValueId.fromIndex(0), ir.ValueId.fromIndex(1) },
        .blocks = &.{ preheader, header, body, primary_path, secondary_path, primary_return, secondary_return },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "pre-tested-secondary-terminating-path",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[1].loop;
    const boundary = loop.body_region.nodes[0].loop_boundary.boundary.side_exit;
    try std.testing.expectEqual(secondary_path, boundary.entry_edge.target);
    try std.testing.expectEqual(secondary_path, boundary.region.nodes[0].block);
    try std.testing.expectEqual(secondary_return, boundary.region.nodes[1].block);
}

test "canonical diamond becomes a branch followed by its join" {
    const fixtures = lifter.fixtures;
    const program = &fixtures.absolute_value_module.program;
    var analysis = try cfg.Analysis.init(std.testing.allocator, program, fixtures.absolute_value_module.functions[1]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 2), plan.root.nodes.len);
    try std.testing.expect(plan.root.nodes[0] == .branch);
    try std.testing.expectEqual(fixtures.absolute_value_module.b_join, plan.root.nodes[0].branch.join.?);
    try std.testing.expectEqual(fixtures.absolute_value_module.b_join, plan.root.nodes[1].block);
}

test "nested acyclic branches form recursive regions" {
    const function_id = ir.FunctionId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = ir.BlockId.fromIndex(0), .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = ir.BlockId.fromIndex(1) },
            .else_edge = .{ .target = ir.BlockId.fromIndex(2) },
        } } },
        .{ .id = ir.BlockId.fromIndex(1), .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = ir.BlockId.fromIndex(3) },
            .else_edge = .{ .target = ir.BlockId.fromIndex(4) },
        } } },
        .{ .id = ir.BlockId.fromIndex(2), .function = function_id, .terminator = .{ .jump = .{ .target = ir.BlockId.fromIndex(6) } } },
        .{ .id = ir.BlockId.fromIndex(3), .function = function_id, .terminator = .{ .jump = .{ .target = ir.BlockId.fromIndex(5) } } },
        .{ .id = ir.BlockId.fromIndex(4), .function = function_id, .terminator = .{ .jump = .{ .target = ir.BlockId.fromIndex(5) } } },
        .{ .id = ir.BlockId.fromIndex(5), .function = function_id, .terminator = .{ .jump = .{ .target = ir.BlockId.fromIndex(6) } } },
        .{ .id = ir.BlockId.fromIndex(6), .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ ir.BlockId.fromIndex(6), ir.BlockId.fromIndex(3), ir.BlockId.fromIndex(0), ir.BlockId.fromIndex(5), ir.BlockId.fromIndex(2), ir.BlockId.fromIndex(4), ir.BlockId.fromIndex(1) },
        .entry_block = ir.BlockId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "nested-branch-plan",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const outer = plan.root.nodes[0].branch;
    try std.testing.expectEqual(ir.BlockId.fromIndex(6), outer.join.?);
    try std.testing.expect(outer.then_region.nodes[0] == .branch);
    try std.testing.expectEqual(ir.BlockId.fromIndex(5), outer.then_region.nodes[0].branch.join.?);
}

test "branches with independent terminal arms need no synthetic join" {
    const function_id = ir.FunctionId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = ir.BlockId.fromIndex(0), .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = ir.BlockId.fromIndex(1) },
            .else_edge = .{ .target = ir.BlockId.fromIndex(2) },
        } } },
        .{ .id = ir.BlockId.fromIndex(1), .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = ir.BlockId.fromIndex(2), .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ ir.BlockId.fromIndex(0), ir.BlockId.fromIndex(1), ir.BlockId.fromIndex(2) },
        .entry_block = ir.BlockId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "terminal-branch-plan",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    try std.testing.expect(plan.root.nodes[0].branch.join == null);
}

test "dominated four-arm terminal remains the outer branch continuation" {
    const function_id = ir.FunctionId.fromIndex(0);
    const ids = [_]ir.BlockId{
        ir.BlockId.fromIndex(0), ir.BlockId.fromIndex(1),
        ir.BlockId.fromIndex(2), ir.BlockId.fromIndex(3),
        ir.BlockId.fromIndex(4), ir.BlockId.fromIndex(5),
        ir.BlockId.fromIndex(6), ir.BlockId.fromIndex(7),
    };
    const terminal = ids[7];
    const blocks = [_]ir.Block{
        .{ .id = ids[0], .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = ids[1] }, .else_edge = .{ .target = ids[2] },
        } } },
        .{ .id = ids[1], .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = ids[2], .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = ids[3] }, .else_edge = .{ .target = ids[4] },
        } } },
        .{ .id = ids[3], .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = ids[4], .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = ids[5] }, .else_edge = .{ .target = ids[6] },
        } } },
        .{ .id = ids[5], .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = ids[6], .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{ir.ValueId.fromIndex(0)} } },
    };
    const functions = [_]ir.Function{.{ .id = function_id, .blocks = &ids, .entry_block = ids[0] }};
    const program: ir.Program = .{
        .program_id = "dominated-four-arm-terminal",
        .entry_function = function_id, .functions = &functions,
        .blocks = &blocks, .instructions = &.{}, .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    try std.testing.expectEqual(@as(usize, 4), analysis.predecessorCount(terminal));
    try std.testing.expect(analysis.dominates(ids[0], terminal));
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    try std.testing.expectEqual(@as(usize, 2), plan.root.nodes.len);
    try std.testing.expectEqual(terminal, plan.root.nodes[0].branch.join.?);
    try std.testing.expectEqual(terminal, plan.root.nodes[1].block);
    const free_targets = try lifter.structure.regionFreeTargetsAlloc(std.testing.allocator, plan.root);
    defer std.testing.allocator.free(free_targets);
    try std.testing.expectEqual(@as(usize, 0), free_targets.len);
}

test "nested terminal arm may bypass an acyclic parent join" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const direct = ir.BlockId.fromIndex(1);
    const nested_entry = ir.BlockId.fromIndex(2);
    const nested = ir.BlockId.fromIndex(3);
    const join = ir.BlockId.fromIndex(4);
    const terminal = ir.BlockId.fromIndex(5);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = direct },
            .else_edge = .{ .target = nested_entry },
        } } },
        .{ .id = direct, .function = function_id, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = nested_entry, .function = function_id, .terminator = .{ .jump = .{ .target = nested } } },
        .{ .id = nested, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = join },
            .else_edge = .{ .target = terminal },
        } } },
        .{ .id = join, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ terminal, nested, entry, join, direct, nested_entry },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "nested-terminal-partial-convergence",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 2), plan.root.nodes.len);
    const outer = plan.root.nodes[0].branch;
    try std.testing.expectEqual(join, outer.join.?);
    try std.testing.expectEqual(join, plan.root.nodes[1].block);
    try std.testing.expectEqual(direct, outer.then_region.nodes[0].block);
    try std.testing.expectEqual(nested_entry, outer.else_region.nodes[0].block);
    const inner = outer.else_region.nodes[1].branch;
    try std.testing.expect(inner.join == null);
    try std.testing.expectEqual(@as(usize, 0), inner.then_region.nodes.len);
    try std.testing.expectEqual(terminal, inner.else_region.nodes[0].block);
}

test "nested arm may bypass an acyclic join to its shared terminal" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const direct_entry = ir.BlockId.fromIndex(1);
    const nested_entry = ir.BlockId.fromIndex(2);
    const nested = ir.BlockId.fromIndex(3);
    const early = ir.BlockId.fromIndex(4);
    const join = ir.BlockId.fromIndex(5);
    const terminal = ir.BlockId.fromIndex(6);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = nested_entry },
            .else_edge = .{ .target = direct_entry },
        } } },
        .{ .id = direct_entry, .function = function_id, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = nested_entry, .function = function_id, .terminator = .{ .jump = .{ .target = nested } } },
        .{ .id = nested, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = early },
            .else_edge = .{ .target = join },
        } } },
        .{ .id = early, .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = join, .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ terminal, nested, direct_entry, entry, join, early, nested_entry },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "nested-shared-terminal-partial-convergence",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 3), plan.root.nodes.len);
    const outer = plan.root.nodes[0].branch;
    try std.testing.expectEqual(entry, outer.block);
    try std.testing.expectEqual(join, outer.join.?);
    try std.testing.expectEqual(direct_entry, outer.else_region.nodes[0].block);
    try std.testing.expectEqual(nested_entry, outer.then_region.nodes[0].block);
    const inner = outer.then_region.nodes[1].branch;
    try std.testing.expect(inner.join == null);
    try std.testing.expectEqual(early, inner.then_region.nodes[0].block);
    try std.testing.expectEqual(terminal, inner.then_region.terminal_projection.?.terminal);
    try std.testing.expect(inner.then_region.terminal_projection.?.edge != null);
    try std.testing.expectEqual(@as(usize, 0), inner.else_region.nodes.len);
    try std.testing.expectEqual(join, plan.root.nodes[1].block);
    try std.testing.expectEqual(terminal, plan.root.nodes[2].block);

    var direct_blocks = blocks;
    direct_blocks[nested.index()].terminator.branch.then_edge.target = terminal;
    const direct_functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ terminal, nested, direct_entry, entry, join, nested_entry },
        .entry_block = entry,
    }};
    var direct_program = program;
    direct_program.program_id = "nested-direct-shared-terminal-partial-convergence";
    direct_program.functions = &direct_functions;
    direct_program.blocks = &direct_blocks;
    var direct_analysis = try cfg.Analysis.init(std.testing.allocator, &direct_program, direct_functions[0]);
    defer direct_analysis.deinit();
    var direct_plan = try Plan.init(std.testing.allocator, &direct_analysis);
    defer direct_plan.deinit();
    const direct_inner = direct_plan.root.nodes[0].branch.then_region.nodes[1].branch;
    try std.testing.expectEqual(@as(usize, 0), direct_inner.then_region.nodes.len);
    try std.testing.expectEqual(terminal, direct_inner.then_region.terminal_projection.?.terminal);
    try std.testing.expect(direct_inner.then_region.terminal_projection.?.edge == null);
}

test "forwarding history restores an acyclic local stop before a shared terminating suffix" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const direct = ir.BlockId.fromIndex(1);
    const nested_entry = ir.BlockId.fromIndex(2);
    const nested = ir.BlockId.fromIndex(3);
    const nested_then = ir.BlockId.fromIndex(4);
    const stop = ir.BlockId.fromIndex(5);
    const relay = ir.BlockId.fromIndex(6);
    const tail = ir.BlockId.fromIndex(7);
    const tail_then = ir.BlockId.fromIndex(8);
    const tail_else = ir.BlockId.fromIndex(9);
    const terminal = ir.BlockId.fromIndex(10);
    const historical = ir.BlockId.fromIndex(11);
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = direct },
            .else_edge = .{ .target = nested_entry },
        } } },
        .{ .id = direct, .function = function_id, .terminator = .{ .jump = .{ .target = stop } } },
        .{ .id = nested_entry, .function = function_id, .terminator = .{ .jump = .{ .target = nested } } },
        .{ .id = nested, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = nested_then },
            .else_edge = .{ .target = tail },
        } } },
        .{ .id = nested_then, .function = function_id, .terminator = .{ .jump = .{ .target = stop } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .jump = .{ .target = relay } } },
        .{ .id = relay, .function = function_id, .terminator = .{ .jump = .{ .target = tail } } },
        .{ .id = tail, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = tail_then },
            .else_edge = .{ .target = tail_else },
        } } },
        .{ .id = tail_then, .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = tail_else, .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = historical, .function = function_id, .terminator = .{ .jump = .{ .target = stop } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ entry, direct, nested_entry, nested, nested_then, stop, relay, tail, tail_then, tail_else, terminal, historical },
        .entry_block = entry,
    }};
    var rewrites = [_]ir.CfgEdgeRewrite{
        .{ .id = ir.EdgeRewriteId.fromIndex(0), .source = nested, .kind = .branch_else, .from = .{ .target = historical }, .to = .{ .target = stop }, .rule = .forwarding_jump },
        .{ .id = ir.EdgeRewriteId.fromIndex(1), .source = nested, .kind = .branch_else, .from = .{ .target = stop }, .to = .{ .target = relay }, .rule = .forwarding_jump },
        .{ .id = ir.EdgeRewriteId.fromIndex(2), .source = nested, .kind = .branch_else, .from = .{ .target = relay }, .to = .{ .target = tail }, .rule = .forwarding_jump },
    };
    var program: ir.Program = .{
        .program_id = "acyclic-forwarding-history-stop",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const outer = plan.root.nodes[0].branch;
    try std.testing.expectEqual(stop, outer.join.?);
    const restored = outer.else_region.nodes[1].branch;
    try std.testing.expectEqual(stop, restored.join.?);
    try std.testing.expect(restored.else_edge_override.? == .history_cut);
    try std.testing.expectEqual(stop, restored.else_edge_override.?.history_cut.edge.target);
    try std.testing.expectEqual(@as(usize, 0), restored.else_region.nodes.len);
    try std.testing.expectEqual(stop, plan.root.nodes[1].block);
    try std.testing.expectEqual(tail, plan.root.nodes[3].branch.block);

    rewrites[1].rule = .proved_branch;
    var rejected_analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer rejected_analysis.deinit();
    try std.testing.expectError(error.UnsupportedShape, Plan.init(std.testing.allocator, &rejected_analysis));
}

test "dominated backedge becomes a natural loop with an owned body" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const exit_block = ir.BlockId.fromIndex(3);
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit_block },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ exit_block, body, preheader, header },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "natural-loop-plan",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 3), plan.root.nodes.len);
    try std.testing.expectEqual(preheader, plan.root.nodes[0].block);
    try std.testing.expectEqual(header, plan.root.nodes[1].loop.header);
    try std.testing.expect(plan.root.nodes[1].loop.continue_on_true);
    try std.testing.expectEqual(@as(usize, 1), plan.root.nodes[1].loop.body_region.nodes.len);
    try std.testing.expectEqual(body, plan.root.nodes[1].loop.body_region.nodes[0].block);
    try std.testing.expectEqual(exit_block, plan.root.nodes[2].block);
}

test "solved loop header replays its authenticated inactive continuation" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const path = ir.BlockId.fromIndex(3);
    const latch = ir.BlockId.fromIndex(4);
    const side = ir.BlockId.fromIndex(5);
    const exit_block = ir.BlockId.fromIndex(6);
    const terminal = ir.BlockId.fromIndex(7);
    const side_terminal = ir.BlockId.fromIndex(8);
    const inactive_relay = ir.BlockId.fromIndex(9);
    const header_instruction = ir.InstructionId.fromIndex(0);
    const exit_instruction = ir.InstructionId.fromIndex(1);
    const header_condition = ir.ValueId.fromIndex(0);
    const body_condition = ir.ValueId.fromIndex(1);
    const path_condition = ir.ValueId.fromIndex(2);
    const side_condition = ir.ValueId.fromIndex(3);
    const exit_value = ir.ValueId.fromIndex(4);
    const proof = ir.EvidenceId.fromIndex(0);
    const values = [_]ir.Value{
        .{
            .id = header_condition,
            .function = function_id,
            .type = .{ .kind = .boolean },
            .origin = .{ .instruction_result = .{ .instruction = header_instruction, .index = 0 } },
        },
        .{ .id = body_condition, .function = function_id, .type = .{ .kind = .boolean }, .origin = .{ .parameter = 0 } },
        .{ .id = path_condition, .function = function_id, .type = .{ .kind = .boolean }, .origin = .{ .parameter = 1 } },
        .{ .id = side_condition, .function = function_id, .type = .{ .kind = .boolean }, .origin = .{ .parameter = 2 } },
        .{
            .id = exit_value,
            .function = function_id,
            .type = .{ .kind = .nil_value },
            .origin = .{ .instruction_result = .{ .instruction = exit_instruction, .index = 0 } },
        },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = header_instruction,
            .block = header,
            .operation = .{ .constant = .{ .boolean = true } },
            .results = &.{header_condition},
            .effects = .pure,
            .evidence = &.{proof},
        },
        .{
            .id = exit_instruction,
            .block = exit_block,
            .operation = .{ .constant = .{ .nil_value = {} } },
            .results = &.{exit_value},
            .effects = .pure,
            .evidence = &.{proof},
        },
    };
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } }, .evidence = &.{proof} },
        .{
            .id = header,
            .function = function_id,
            .instructions = &.{header_instruction},
            .terminator = .{ .branch = .{
                .condition = header_condition,
                .then_edge = .{ .target = body },
                .else_edge = .{ .target = inactive_relay },
            } },
            .evidence = &.{proof},
        },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = body_condition,
            .then_edge = .{ .target = path },
            .else_edge = .{ .target = side },
        } }, .evidence = &.{proof} },
        .{ .id = path, .function = function_id, .terminator = .{ .branch = .{
            .condition = path_condition,
            .then_edge = .{ .target = latch },
            .else_edge = .{ .target = exit_block },
        } }, .evidence = &.{proof} },
        .{ .id = latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } }, .evidence = &.{proof} },
        .{ .id = side, .function = function_id, .terminator = .{ .branch = .{
            .condition = side_condition,
            .then_edge = .{ .target = exit_block },
            .else_edge = .{ .target = side_terminal },
        } }, .evidence = &.{proof} },
        .{
            .id = exit_block,
            .function = function_id,
            .instructions = &.{exit_instruction},
            .terminator = .{ .jump = .{ .target = terminal } },
            .evidence = &.{proof},
        },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
        .{ .id = side_terminal, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
        .{ .id = inactive_relay, .function = function_id, .terminator = .{ .jump = .{ .target = exit_block } }, .evidence = &.{proof} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ body_condition, path_condition, side_condition },
        .blocks = &.{ preheader, header, body, path, latch, side, exit_block, terminal, side_terminal, inactive_relay },
        .entry_block = preheader,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .structural_derivation,
        .locator = "fixture:solved-loop-header-continuation",
    }};
    const program: ir.Program = .{
        .program_id = "solved-loop-header-continuation",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };

    var resolved = try lifter.proof_orchestrator.resolveAlloc(
        std.testing.allocator,
        &program,
        lifter.solver_backend.internalFacts(),
    );
    defer resolved.deinit();
    try std.testing.expectEqual(body, resolved.program.blocks[header.index()].terminator.jump.target);
    try std.testing.expectEqual(@as(usize, 1), resolved.program.obligations.len);

    var analysis = try cfg.Analysis.init(std.testing.allocator, &resolved.program, resolved.program.functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    try std.testing.expectEqual(preheader, plan.root.nodes[0].block);
    switch (plan.root.nodes[1]) {
        .infinite_loop => |loop| {
            try std.testing.expectEqual(header, loop.header);
            try std.testing.expectEqual(exit_block, loop.exit.?);
        },
        .latch_loop => |loop| {
            try std.testing.expectEqual(header, loop.header);
            try std.testing.expectEqual(exit_block, loop.exit);
        },
        else => return error.TestUnexpectedResult,
    }
    try std.testing.expectEqual(exit_block, plan.root.nodes[2].block);
}

test "conditional latch becomes a latch-tested natural loop" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const latch = ir.BlockId.fromIndex(3);
    const exit_block = ir.BlockId.fromIndex(4);
    const initial = [_]ir.ValueId{ir.ValueId.fromIndex(0)};
    const body_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(1)};
    const latch_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(2)};
    const next_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(3)};
    const exit_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(4)};
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header, .arguments = &initial } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = body, .arguments = &body_arguments } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = latch, .arguments = &latch_arguments } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(5),
            .then_edge = .{ .target = header, .arguments = &next_arguments },
            .else_edge = .{ .target = exit_block, .arguments = &exit_arguments },
        } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ exit_block, latch, body, preheader, header },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "latch-loop-plan",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 3), plan.root.nodes.len);
    const loop = plan.root.nodes[1].latch_loop;
    try std.testing.expectEqual(header, loop.header);
    try std.testing.expectEqual(exit_block, loop.exit);
    try std.testing.expectEqual(@as(usize, 1), loop.latch_count);
    try std.testing.expectEqual(@as(usize, 3), loop.body_region.nodes.len);
    try std.testing.expectEqual(header, loop.body_region.nodes[0].block);
    try std.testing.expectEqual(body, loop.body_region.nodes[1].block);
    const control = loop.body_region.nodes[2].loop_control;
    try std.testing.expectEqual(latch, control.block);
    try std.testing.expectEqualSlices(ir.ValueId, &next_arguments, control.continue_edge.arguments);
    try std.testing.expectEqualSlices(ir.ValueId, &exit_arguments, control.exit_edge.arguments);
}

test "post-tested loop header may contain an internal diamond" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const left = ir.BlockId.fromIndex(2);
    const right = ir.BlockId.fromIndex(3);
    const join = ir.BlockId.fromIndex(4);
    const latch = ir.BlockId.fromIndex(5);
    const exit_block = ir.BlockId.fromIndex(6);
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = left },
            .else_edge = .{ .target = right },
        } } },
        .{ .id = left, .function = function_id, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = right, .function = function_id, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = join, .function = function_id, .terminator = .{ .jump = .{ .target = latch } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = exit_block },
            .else_edge = .{ .target = header },
        } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ exit_block, join, right, preheader, latch, header, left },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "latch-loop-diamond-header",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[1].latch_loop;
    try std.testing.expectEqual(header, loop.header);
    try std.testing.expectEqual(exit_block, loop.exit);
    try std.testing.expectEqual(@as(usize, 1), loop.latch_count);
    try std.testing.expectEqual(@as(usize, 3), loop.body_region.nodes.len);
    const header_branch = loop.body_region.nodes[0].branch;
    try std.testing.expectEqual(header, header_branch.block);
    try std.testing.expectEqual(join, header_branch.join.?);
    try std.testing.expectEqual(left, header_branch.then_region.nodes[0].block);
    try std.testing.expectEqual(right, header_branch.else_region.nodes[0].block);
    try std.testing.expectEqual(join, loop.body_region.nodes[1].block);
    try std.testing.expectEqual(latch, loop.body_region.nodes[2].loop_control.block);
}

test "multiple conditional latches may share a canonical exit" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const split = ir.BlockId.fromIndex(1);
    const first_latch = ir.BlockId.fromIndex(2);
    const second_latch = ir.BlockId.fromIndex(3);
    const exit_block = ir.BlockId.fromIndex(4);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = split } } },
        .{ .id = split, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = first_latch },
            .else_edge = .{ .target = second_latch },
        } } },
        .{ .id = first_latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = exit_block },
        } } },
        .{ .id = second_latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = exit_block },
        } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ second_latch, exit_block, split, header, first_latch },
        .entry_block = header,
    }};
    const program: ir.Program = .{
        .program_id = "multiple-latch-loop-plan",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[0].latch_loop;
    try std.testing.expectEqual(exit_block, loop.exit);
    try std.testing.expectEqual(@as(usize, 2), loop.latch_count);
    try std.testing.expectEqual(header, loop.body_region.nodes[0].block);
    const split_branch = loop.body_region.nodes[1].branch;
    try std.testing.expect(split_branch.join == null);
    try std.testing.expectEqual(first_latch, split_branch.then_region.nodes[0].loop_control.block);
    try std.testing.expectEqual(second_latch, split_branch.else_region.nodes[0].loop_control.block);
}

test "post-tested loop may contain an early continue backedge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const decision = ir.BlockId.fromIndex(2);
    const latch = ir.BlockId.fromIndex(3);
    const exit_block = ir.BlockId.fromIndex(4);
    const initial_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(0)};
    const early_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(1)};
    const latch_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(2)};
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header, .arguments = &initial_arguments } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = decision } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(3),
            .then_edge = .{ .target = header, .arguments = &early_arguments },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(4),
            .then_edge = .{ .target = exit_block },
            .else_edge = .{ .target = header, .arguments = &latch_arguments },
        } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ exit_block, latch, decision, preheader, header },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "post-tested-early-continue",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[1].latch_loop;
    try std.testing.expectEqual(@as(usize, 1), loop.latch_count);
    const decision_branch = loop.body_region.nodes[1].branch;
    try std.testing.expect(decision_branch.join == null);
    try std.testing.expectEqual(@as(usize, 0), decision_branch.then_region.nodes.len);
    try std.testing.expectEqual(header, decision_branch.then_region.stop.?);
    try std.testing.expectEqual(latch, decision_branch.else_region.nodes[0].loop_control.block);

    const forwarding_continue = ir.BlockId.fromIndex(blocks.len);
    var forwarded_blocks = blocks ++ [_]ir.Block{.{
        .id = forwarding_continue,
        .function = function_id,
        .terminator = .{ .jump = .{ .target = header, .arguments = &early_arguments } },
    }};
    forwarded_blocks[decision.index()].terminator.branch.then_edge = .{ .target = forwarding_continue };
    var forwarded_functions = functions;
    forwarded_functions[0].blocks = &.{ exit_block, latch, decision, forwarding_continue, preheader, header };
    var forwarded_program = program;
    forwarded_program.functions = &forwarded_functions;
    forwarded_program.blocks = &forwarded_blocks;
    var forwarded_analysis = try cfg.Analysis.init(std.testing.allocator, &forwarded_program, forwarded_functions[0]);
    defer forwarded_analysis.deinit();
    var forwarded_plan = try Plan.init(std.testing.allocator, &forwarded_analysis);
    defer forwarded_plan.deinit();

    const forwarded_loop = forwarded_plan.root.nodes[1].latch_loop;
    const forwarded_decision = forwarded_loop.body_region.nodes[1].branch;
    try std.testing.expect(forwarded_decision.join == null);
    try std.testing.expectEqual(@as(usize, 1), forwarded_decision.then_region.nodes.len);
    try std.testing.expectEqual(forwarding_continue, forwarded_decision.then_region.nodes[0].block);
    try std.testing.expectEqual(header, forwarded_decision.then_region.stop.?);
    try std.testing.expectEqual(latch, forwarded_decision.else_region.nodes[0].loop_control.block);

    const header_parameter = ir.ValueId.fromIndex(5);
    const forwarding_parameter = ir.ValueId.fromIndex(6);
    const parameterized_values = [_]ir.Value{
        .{ .id = initial_arguments[0], .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = early_arguments[0], .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = latch_arguments[0], .function = function_id, .origin = .{ .parameter = 2 } },
        .{ .id = ir.ValueId.fromIndex(3), .function = function_id, .type = .boolean, .origin = .{ .parameter = 3 } },
        .{ .id = ir.ValueId.fromIndex(4), .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } },
        .{ .id = header_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = forwarding_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = forwarding_continue, .index = 0 } } },
    };
    var parameterized_blocks = forwarded_blocks;
    parameterized_blocks[header.index()].parameters = &.{header_parameter};
    parameterized_blocks[forwarding_continue.index()].parameters = &.{forwarding_parameter};
    parameterized_blocks[decision.index()].terminator.branch.then_edge = .{
        .target = forwarding_continue,
        .arguments = &early_arguments,
    };
    parameterized_blocks[forwarding_continue.index()].terminator = .{ .jump = .{
        .target = header,
        .arguments = &.{forwarding_parameter},
    } };
    var parameterized_functions = forwarded_functions;
    parameterized_functions[0].parameters = &.{
        initial_arguments[0],
        early_arguments[0],
        latch_arguments[0],
        ir.ValueId.fromIndex(3),
        ir.ValueId.fromIndex(4),
    };
    var parameterized_program = forwarded_program;
    parameterized_program.program_id = "post-tested-parameterized-forwarding-continue";
    parameterized_program.functions = &parameterized_functions;
    parameterized_program.blocks = &parameterized_blocks;
    parameterized_program.values = &parameterized_values;

    const replayed = (try lifter.control_flow.replayForwardingJump(
        std.testing.allocator,
        &parameterized_program,
        parameterized_blocks[decision.index()].terminator.branch.then_edge,
    )) orelse return error.TestUnexpectedResult;
    defer if (replayed.arguments.len != 0) std.testing.allocator.free(replayed.arguments);
    try std.testing.expectEqual(header, replayed.target);
    try std.testing.expectEqualSlices(ir.ValueId, &early_arguments, replayed.arguments);

    var parameterized_analysis = try cfg.Analysis.init(std.testing.allocator, &parameterized_program, parameterized_functions[0]);
    defer parameterized_analysis.deinit();
    var parameterized_plan = try Plan.init(std.testing.allocator, &parameterized_analysis);
    defer parameterized_plan.deinit();

    const parameterized_loop = parameterized_plan.root.nodes[1].latch_loop;
    const parameterized_decision = parameterized_loop.body_region.nodes[1].branch;
    try std.testing.expect(parameterized_decision.join == null);
    try std.testing.expectEqual(@as(usize, 0), parameterized_decision.then_region.nodes.len);
    try std.testing.expectEqual(header, parameterized_decision.then_region.stop.?);
    const edge_override = parameterized_decision.then_edge_override.?;
    try std.testing.expect(edge_override == .forwarding);
    try std.testing.expectEqual(header, edge_override.forwarding.edge.target);
    try std.testing.expectEqualSlices(ir.ValueId, &early_arguments, edge_override.forwarding.edge.arguments);
    try std.testing.expectEqualSlices(ir.BlockId, &.{forwarding_continue}, edge_override.forwarding.blocks);
    try std.testing.expect(parameterized_decision.else_edge_override == null);
    try std.testing.expect(parameterized_decision.then_region.terminal_projection == null);

    const first_copy_instruction = ir.InstructionId.fromIndex(0);
    const second_copy_instruction = ir.InstructionId.fromIndex(1);
    const first_copy_result = ir.ValueId.fromIndex(parameterized_values.len);
    const second_copy_result = ir.ValueId.fromIndex(parameterized_values.len + 1);
    const copy_values = parameterized_values ++ [_]ir.Value{
        .{
            .id = first_copy_result,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = first_copy_instruction, .index = 0 } },
        },
        .{
            .id = second_copy_result,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = second_copy_instruction, .index = 0 } },
        },
    };
    const copy_instructions = [_]ir.Instruction{
        .{
            .id = first_copy_instruction,
            .block = forwarding_continue,
            .operation = .{ .copy = forwarding_parameter },
            .results = &.{first_copy_result},
            .effects = .pure,
        },
        .{
            .id = second_copy_instruction,
            .block = forwarding_continue,
            .operation = .{ .copy = first_copy_result },
            .results = &.{second_copy_result},
            .effects = .pure,
        },
    };
    var copy_blocks = parameterized_blocks;
    copy_blocks[forwarding_continue.index()].instructions = &.{ first_copy_instruction, second_copy_instruction };
    copy_blocks[forwarding_continue.index()].terminator.jump.arguments = &.{second_copy_result};
    var copy_program = parameterized_program;
    copy_program.program_id = "post-tested-copy-forwarding-continue";
    copy_program.blocks = &copy_blocks;
    copy_program.instructions = &copy_instructions;
    copy_program.values = &copy_values;

    var copy_analysis = try cfg.Analysis.init(std.testing.allocator, &copy_program, parameterized_functions[0]);
    defer copy_analysis.deinit();
    var copy_plan = try Plan.init(std.testing.allocator, &copy_analysis);
    defer copy_plan.deinit();

    const copy_decision = copy_plan.root.nodes[1].latch_loop.body_region.nodes[1].branch;
    try std.testing.expectEqual(@as(usize, 0), copy_decision.then_region.nodes.len);
    const copy_edge_override = copy_decision.then_edge_override.?;
    try std.testing.expect(copy_edge_override == .forwarding);
    try std.testing.expectEqual(header, copy_edge_override.forwarding.edge.target);
    try std.testing.expectEqualSlices(ir.ValueId, &early_arguments, copy_edge_override.forwarding.edge.arguments);
    try std.testing.expectEqualSlices(ir.BlockId, &.{forwarding_continue}, copy_edge_override.forwarding.blocks);

    const relay_continue = ir.BlockId.fromIndex(copy_blocks.len);
    const relay_parameter = ir.ValueId.fromIndex(copy_values.len);
    const relay_values = copy_values ++ [_]ir.Value{.{
        .id = relay_parameter,
        .function = function_id,
        .origin = .{ .block_parameter = .{ .block = relay_continue, .index = 0 } },
    }};
    var relay_blocks = copy_blocks ++ [_]ir.Block{.{
        .id = relay_continue,
        .function = function_id,
        .parameters = &.{relay_parameter},
        .terminator = .{ .jump = .{ .target = header, .arguments = &.{relay_parameter} } },
    }};
    relay_blocks[forwarding_continue.index()].terminator.jump = .{
        .target = relay_continue,
        .arguments = &.{second_copy_result},
    };
    const relay_function_blocks = [_]ir.BlockId{
        exit_block,
        latch,
        decision,
        forwarding_continue,
        relay_continue,
        preheader,
        header,
    };
    var relay_functions = parameterized_functions;
    relay_functions[0].blocks = &relay_function_blocks;
    var relay_program = copy_program;
    relay_program.program_id = "post-tested-copy-forwarding-path-continue";
    relay_program.functions = &relay_functions;
    relay_program.blocks = &relay_blocks;
    relay_program.values = &relay_values;

    var relay_analysis = try cfg.Analysis.init(std.testing.allocator, &relay_program, relay_functions[0]);
    defer relay_analysis.deinit();
    var relay_plan = try Plan.init(std.testing.allocator, &relay_analysis);
    defer relay_plan.deinit();

    const relay_decision = relay_plan.root.nodes[1].latch_loop.body_region.nodes[1].branch;
    try std.testing.expectEqual(@as(usize, 0), relay_decision.then_region.nodes.len);
    const relay_override = relay_decision.then_edge_override.?;
    try std.testing.expect(relay_override == .forwarding);
    try std.testing.expectEqual(header, relay_override.forwarding.edge.target);
    try std.testing.expectEqualSlices(ir.ValueId, &early_arguments, relay_override.forwarding.edge.arguments);
    try std.testing.expectEqualSlices(
        ir.BlockId,
        &.{ forwarding_continue, relay_continue },
        relay_override.forwarding.blocks,
    );

    var cyclic_blocks = relay_blocks;
    cyclic_blocks[relay_continue.index()].terminator.jump.target = forwarding_continue;
    var cyclic_program = relay_program;
    cyclic_program.blocks = &cyclic_blocks;
    try std.testing.expect((try lifter.control_flow.replayForwardingPathTo(
        std.testing.allocator,
        &cyclic_program,
        cyclic_blocks[decision.index()].terminator.branch.then_edge,
        header,
    )) == null);
}

test "post-tested loop may break before its final latch" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const decision = ir.BlockId.fromIndex(2);
    const latch = ir.BlockId.fromIndex(3);
    const exit_block = ir.BlockId.fromIndex(4);
    const break_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(0)};
    const latch_exit_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(1)};
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = decision } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = exit_block, .arguments = &break_arguments },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(3),
            .then_edge = .{ .target = exit_block, .arguments = &latch_exit_arguments },
            .else_edge = .{ .target = header },
        } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ exit_block, latch, decision, preheader, header },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "post-tested-early-break",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[1].latch_loop;
    const control = loop.body_region.nodes[1].loop_boundary;
    try std.testing.expectEqual(decision, control.block);
    try std.testing.expect(!control.body_on_true);
    try std.testing.expectEqual(exit_block, control.boundary.exit.target);
    try std.testing.expectEqualSlices(ir.ValueId, &break_arguments, control.boundary.exit.arguments);
    try std.testing.expectEqual(latch, control.body_region.nodes[0].loop_control.block);
}

test "post-tested continue and break arms may share one final latch" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const continue_path = ir.BlockId.fromIndex(2);
    const break_decision = ir.BlockId.fromIndex(3);
    const break_path = ir.BlockId.fromIndex(4);
    const normal_path = ir.BlockId.fromIndex(5);
    const latch = ir.BlockId.fromIndex(6);
    const exit_block = ir.BlockId.fromIndex(7);
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = continue_path },
            .else_edge = .{ .target = break_decision },
        } } },
        .{ .id = continue_path, .function = function_id, .terminator = .{ .jump = .{ .target = latch } } },
        .{ .id = break_decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = break_path },
            .else_edge = .{ .target = normal_path },
        } } },
        .{ .id = break_path, .function = function_id, .terminator = .{ .jump = .{ .target = exit_block } } },
        .{ .id = normal_path, .function = function_id, .terminator = .{ .jump = .{ .target = latch } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = exit_block },
            .else_edge = .{ .target = header },
        } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ normal_path, exit_block, continue_path, latch, preheader, break_path, header, break_decision },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "post-tested-shared-latch-boundaries",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[1].latch_loop;
    try std.testing.expectEqual(@as(usize, 2), loop.body_region.nodes.len);
    const split = loop.body_region.nodes[0].branch;
    try std.testing.expectEqual(header, split.block);
    try std.testing.expectEqual(continue_path, split.then_region.nodes[0].block);
    try std.testing.expectEqual(break_decision, split.else_region.nodes[0].loop_boundary.block);
    try std.testing.expectEqual(latch, loop.body_region.nodes[1].loop_control.block);
}

test "early loop boundary may own cleanup before breaking" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const decision = ir.BlockId.fromIndex(2);
    const latch = ir.BlockId.fromIndex(3);
    const cleanup_first = ir.BlockId.fromIndex(4);
    const cleanup_second = ir.BlockId.fromIndex(5);
    const exit_block = ir.BlockId.fromIndex(6);
    const cleanup_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(0)};
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = decision } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = cleanup_first, .arguments = &cleanup_arguments },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = exit_block },
            .else_edge = .{ .target = header },
        } } },
        .{ .id = cleanup_first, .function = function_id, .terminator = .{ .jump = .{ .target = cleanup_second } } },
        .{ .id = cleanup_second, .function = function_id, .terminator = .{ .jump = .{ .target = exit_block } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ cleanup_second, exit_block, latch, decision, preheader, cleanup_first, header },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "post-tested-cleanup-break",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[1].latch_loop;
    const control = loop.body_region.nodes[1].loop_boundary;
    try std.testing.expect(!control.body_on_true);
    try std.testing.expectEqual(cleanup_first, control.boundary.side_exit.entry_edge.target);
    try std.testing.expectEqualSlices(ir.ValueId, &cleanup_arguments, control.boundary.side_exit.entry_edge.arguments);
    try std.testing.expectEqual(@as(usize, 2), control.boundary.side_exit.region.nodes.len);
    try std.testing.expectEqual(cleanup_first, control.boundary.side_exit.region.nodes[0].block);
    try std.testing.expectEqual(cleanup_second, control.boundary.side_exit.region.nodes[1].block);
    try std.testing.expectEqual(exit_block, control.boundary.side_exit.region.stop.?);
}

test "post-tested loop promotes bypassing exits to their common convergence" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const decision = ir.BlockId.fromIndex(2);
    const latch = ir.BlockId.fromIndex(3);
    const side_cleanup = ir.BlockId.fromIndex(4);
    const normal_cleanup = ir.BlockId.fromIndex(5);
    const join = ir.BlockId.fromIndex(6);
    const side_instruction = ir.InstructionId.fromIndex(0);
    const normal_instruction = ir.InstructionId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = decision } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = side_cleanup },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = normal_cleanup },
            .else_edge = .{ .target = header },
        } } },
        .{ .id = side_cleanup, .function = function_id, .instructions = &.{side_instruction}, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = normal_cleanup, .function = function_id, .instructions = &.{normal_instruction}, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = join, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = side_instruction, .block = side_cleanup, .operation = .{ .constant = .nil_value }, .results = &.{}, .effects = .pure },
        .{ .id = normal_instruction, .block = normal_cleanup, .operation = .{ .constant = .nil_value }, .results = &.{}, .effects = .pure },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ preheader, header, decision, latch, side_cleanup, normal_cleanup, join },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "post-tested-promoted-exit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[1].latch_loop;
    try std.testing.expectEqual(join, loop.exit);
    const early = loop.body_region.nodes[1].loop_boundary;
    try std.testing.expectEqual(side_cleanup, early.boundary.side_exit.entry_edge.target);
    try std.testing.expectEqual(join, early.boundary.side_exit.region.stop.?);
    const final = early.body_region.nodes[0].loop_boundary;
    try std.testing.expectEqual(normal_cleanup, final.boundary.side_exit.entry_edge.target);
    try std.testing.expectEqual(join, final.boundary.side_exit.region.stop.?);
}

test "post-tested exit promotion permits a nonreturning continuation arm" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const decision = ir.BlockId.fromIndex(2);
    const latch = ir.BlockId.fromIndex(3);
    const side_cleanup = ir.BlockId.fromIndex(4);
    const normal_cleanup = ir.BlockId.fromIndex(5);
    const cycle = ir.BlockId.fromIndex(6);
    const join = ir.BlockId.fromIndex(7);
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = decision } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = side_cleanup },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = normal_cleanup },
            .else_edge = .{ .target = header },
        } } },
        .{ .id = side_cleanup, .function = function_id, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = normal_cleanup, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = join },
            .else_edge = .{ .target = cycle },
        } } },
        .{ .id = cycle, .function = function_id, .terminator = .{ .jump = .{ .target = cycle } } },
        .{ .id = join, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ cycle, normal_cleanup, preheader, header, decision, latch, side_cleanup, join },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "post-tested-nonreturning-promoted-exit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    try std.testing.expect((try analysis.immediateConvergenceBetween(
        std.testing.allocator,
        normal_cleanup,
        side_cleanup,
        null,
    )) == null);
    try std.testing.expectEqual(join, (try analysis.immediateStructuralConvergenceBetween(
        std.testing.allocator,
        normal_cleanup,
        side_cleanup,
        null,
    )).?);

    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    const loop = plan.root.nodes[1].latch_loop;
    try std.testing.expectEqual(join, loop.exit);
    try std.testing.expectEqual(join, plan.root.nodes[2].block);
}

test "post-tested loop may return before its final latch" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const decision = ir.BlockId.fromIndex(2);
    const latch = ir.BlockId.fromIndex(3);
    const terminal = ir.BlockId.fromIndex(4);
    const exit_block = ir.BlockId.fromIndex(5);
    const terminal_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(0)};
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = decision } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = terminal, .arguments = &terminal_arguments },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = exit_block },
            .else_edge = .{ .target = header },
        } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ terminal, exit_block, latch, decision, preheader, header },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "post-tested-early-terminal",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[1].latch_loop;
    const control = loop.body_region.nodes[1].loop_boundary;
    try std.testing.expect(!control.body_on_true);
    try std.testing.expectEqual(terminal, control.boundary.terminal.block);
    try std.testing.expectEqualSlices(ir.ValueId, &terminal_arguments, control.boundary.terminal.edge.arguments);
    try std.testing.expectEqual(latch, control.body_region.nodes[0].loop_control.block);
}

test "loop body branch to header or canonical exit becomes loop control" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const exit_block = ir.BlockId.fromIndex(3);
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit_block },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = exit_block },
        } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ exit_block, body, preheader, header },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "loop-control-plan",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 1), plan.root.nodes[1].loop.body_region.nodes.len);
    const control = plan.root.nodes[1].loop.body_region.nodes[0].loop_control;
    try std.testing.expectEqual(body, control.block);
    try std.testing.expectEqual(header, control.continue_edge.target);
    try std.testing.expectEqual(exit_block, control.exit_edge.target);
    try std.testing.expect(control.continue_on_true);
}

test "loop body branch to header or terminal block owns the terminal arm" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const terminal = ir.BlockId.fromIndex(3);
    const exit_block = ir.BlockId.fromIndex(4);
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit_block },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = terminal },
        } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ terminal, exit_block, body, preheader, header },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "loop-terminal-plan",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const control = plan.root.nodes[1].loop.body_region.nodes[0].loop_terminal;
    try std.testing.expectEqual(body, control.block);
    try std.testing.expectEqual(header, control.continue_edge.target);
    try std.testing.expectEqual(terminal, control.terminal_block);
    try std.testing.expect(control.continue_on_true);
}

test "loop side exit owns an acyclic region ending at the canonical exit" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const side_first = ir.BlockId.fromIndex(3);
    const side_second = ir.BlockId.fromIndex(4);
    const exit_block = ir.BlockId.fromIndex(5);
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit_block },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = side_first },
            .else_edge = .{ .target = header },
        } } },
        .{ .id = side_first, .function = function_id, .terminator = .{ .jump = .{ .target = side_second } } },
        .{ .id = side_second, .function = function_id, .terminator = .{ .jump = .{ .target = exit_block } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ side_second, exit_block, body, preheader, side_first, header },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "loop-side-exit-plan",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const control = plan.root.nodes[1].loop.body_region.nodes[0].loop_boundary;
    try std.testing.expectEqual(body, control.block);
    try std.testing.expect(!control.body_on_true);
    try std.testing.expectEqual(header, control.body_edge.target);
    try std.testing.expectEqual(side_first, control.boundary.side_exit.entry_edge.target);
    try std.testing.expectEqual(@as(usize, 2), control.boundary.side_exit.region.nodes.len);
    try std.testing.expectEqual(side_first, control.boundary.side_exit.region.nodes[0].block);
    try std.testing.expectEqual(side_second, control.boundary.side_exit.region.nodes[1].block);
    try std.testing.expectEqual(exit_block, control.boundary.side_exit.region.stop.?);
}

test "dominated unconditional cycle becomes an infinite natural loop" {
    const function_id = ir.FunctionId.fromIndex(0);
    const body_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(1)};
    const header_arguments = [_]ir.ValueId{ir.ValueId.fromIndex(0)};
    const blocks = [_]ir.Block{
        .{ .id = ir.BlockId.fromIndex(0), .function = function_id, .terminator = .{ .jump = .{ .target = ir.BlockId.fromIndex(1), .arguments = &body_arguments } } },
        .{ .id = ir.BlockId.fromIndex(1), .function = function_id, .terminator = .{ .jump = .{ .target = ir.BlockId.fromIndex(0), .arguments = &header_arguments } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ ir.BlockId.fromIndex(0), ir.BlockId.fromIndex(1) },
        .entry_block = ir.BlockId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "cyclic-plan",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 1), plan.root.nodes.len);
    const loop = plan.root.nodes[0].infinite_loop;
    try std.testing.expectEqual(ir.BlockId.fromIndex(0), loop.header);
    try std.testing.expectEqual(@as(usize, 2), loop.body_region.nodes.len);
    try std.testing.expectEqual(ir.BlockId.fromIndex(0), loop.body_region.nodes[0].block);
    try std.testing.expectEqual(ir.BlockId.fromIndex(1), loop.body_region.nodes[1].block);
    try std.testing.expectEqual(ir.BlockId.fromIndex(0), loop.body_region.stop.?);
}

test "normalized nested loop may exit to its visited enclosing continuation" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const outer_header = ir.BlockId.fromIndex(1);
    const inner_header = ir.BlockId.fromIndex(2);
    const decision = ir.BlockId.fromIndex(3);
    const body = ir.BlockId.fromIndex(4);
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = outer_header, .function = function_id, .terminator = .{ .jump = .{ .target = inner_header } } },
        .{ .id = inner_header, .function = function_id, .terminator = .{ .jump = .{ .target = decision } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = outer_header },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = inner_header } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ preheader, outer_header, inner_header, decision, body },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "nested-visited-continuation-loop",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 2), plan.root.nodes.len);
    try std.testing.expectEqual(preheader, plan.root.nodes[0].block);
    const outer = plan.root.nodes[1].infinite_loop;
    try std.testing.expectEqual(outer_header, outer.header);
    try std.testing.expect(outer.exit == null);
    const inner = outer.body_region.nodes[1].infinite_loop;
    try std.testing.expectEqual(inner_header, inner.header);
    try std.testing.expectEqual(outer_header, inner.exit.?);
    try std.testing.expectEqual(outer_header, inner.body_region.loop_exit.?);
}

test "infinite natural loop retains its unique internal break exit" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const decision = ir.BlockId.fromIndex(1);
    const latch = ir.BlockId.fromIndex(2);
    const exit_block = ir.BlockId.fromIndex(3);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = decision } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = exit_block },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ header, decision, latch, exit_block },
        .entry_block = header,
    }};
    const program: ir.Program = .{
        .program_id = "infinite-loop-unique-break-exit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 2), plan.root.nodes.len);
    const loop = plan.root.nodes[0].infinite_loop;
    try std.testing.expectEqual(header, loop.header);
    try std.testing.expectEqual(exit_block, loop.exit.?);
    try std.testing.expectEqual(exit_block, loop.body_region.loop_exit.?);
    try std.testing.expectEqual(exit_block, plan.root.nodes[1].block);
    const boundary = loop.body_region.nodes[1].loop_boundary;
    try std.testing.expectEqual(decision, boundary.block);
    try std.testing.expectEqual(exit_block, boundary.boundary.exit.target);
}

test "nested natural loop selects the exit reaching its enclosing continuation" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const outer_header = ir.BlockId.fromIndex(1);
    const outer_body = ir.BlockId.fromIndex(2);
    const inner_header = ir.BlockId.fromIndex(3);
    const normal_decision = ir.BlockId.fromIndex(4);
    const normal_exit = ir.BlockId.fromIndex(5);
    const side_decision = ir.BlockId.fromIndex(6);
    const side_cycle = ir.BlockId.fromIndex(7);
    const inner_latch = ir.BlockId.fromIndex(8);
    const outer_latch = ir.BlockId.fromIndex(9);
    const function_exit = ir.BlockId.fromIndex(10);
    const normal_argument = [_]ir.ValueId{ir.ValueId.fromIndex(2)};
    const normal_parameter = [_]ir.ValueId{ir.ValueId.fromIndex(2)};
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = outer_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = outer_body },
            .else_edge = .{ .target = function_exit },
        } } },
        .{ .id = outer_body, .function = function_id, .terminator = .{ .jump = .{ .target = inner_header } } },
        .{ .id = inner_header, .function = function_id, .terminator = .{ .jump = .{ .target = normal_decision } } },
        .{ .id = normal_decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = normal_exit, .arguments = &normal_argument },
            .else_edge = .{ .target = side_decision },
        } } },
        .{ .id = normal_exit, .function = function_id, .parameters = &normal_parameter, .terminator = .{ .jump = .{ .target = outer_latch } } },
        .{ .id = side_decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = side_cycle },
            .else_edge = .{ .target = inner_latch },
        } } },
        .{ .id = side_cycle, .function = function_id, .terminator = .{ .jump = .{ .target = side_cycle } } },
        .{ .id = inner_latch, .function = function_id, .terminator = .{ .jump = .{ .target = inner_header } } },
        .{ .id = outer_latch, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = function_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ preheader, outer_header, outer_body, inner_header, normal_decision, normal_exit, side_decision, side_cycle, inner_latch, outer_latch, function_exit },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "nested-loop-nonreturning-side-exit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const outer = plan.root.nodes[1].loop;
    const inner = outer.body_region.nodes[1].infinite_loop;
    try std.testing.expectEqual(inner_header, inner.header);
    try std.testing.expectEqual(normal_exit, inner.exit.?);
    const normal_boundary = inner.body_region.nodes[1].loop_boundary;
    try std.testing.expectEqual(normal_decision, normal_boundary.block);
    const side_boundary = normal_boundary.body_region.nodes[0].loop_boundary;
    try std.testing.expectEqual(side_decision, side_boundary.block);
    try std.testing.expectEqual(side_cycle, side_boundary.boundary.side_exit.entry_edge.target);
    try std.testing.expectEqual(side_cycle, side_boundary.boundary.side_exit.region.nodes[0].infinite_loop.header);
}

test "nested terminal side exit closes its enclosing infinite loop" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const outer_header = ir.BlockId.fromIndex(1);
    const inner_header = ir.BlockId.fromIndex(2);
    const normal_decision = ir.BlockId.fromIndex(3);
    const normal_exit = ir.BlockId.fromIndex(4);
    const side_decision = ir.BlockId.fromIndex(5);
    const terminal_forward = ir.BlockId.fromIndex(6);
    const inner_latch = ir.BlockId.fromIndex(7);
    const outer_latch = ir.BlockId.fromIndex(8);
    const terminal = ir.BlockId.fromIndex(9);
    const outer_parameter = [_]ir.ValueId{ir.ValueId.fromIndex(2)};
    const outer_argument = [_]ir.ValueId{ir.ValueId.fromIndex(2)};
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header, .arguments = &outer_argument } } },
        .{ .id = outer_header, .function = function_id, .parameters = &outer_parameter, .terminator = .{ .jump = .{ .target = inner_header } } },
        .{ .id = inner_header, .function = function_id, .terminator = .{ .jump = .{ .target = normal_decision } } },
        .{ .id = normal_decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = normal_exit },
            .else_edge = .{ .target = side_decision },
        } } },
        .{ .id = normal_exit, .function = function_id, .terminator = .{ .jump = .{ .target = outer_latch } } },
        .{ .id = side_decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = terminal_forward },
            .else_edge = .{ .target = inner_latch },
        } } },
        .{ .id = terminal_forward, .function = function_id, .terminator = .{ .jump = .{ .target = terminal } } },
        .{ .id = inner_latch, .function = function_id, .terminator = .{ .jump = .{ .target = inner_header } } },
        .{ .id = outer_latch, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header, .arguments = &outer_argument } } },
        .{ .id = terminal, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ preheader, outer_header, inner_header, normal_decision, normal_exit, side_decision, terminal_forward, inner_latch, outer_latch, terminal },
        .entry_block = preheader,
    }};
    const program: ir.Program = .{
        .program_id = "nested-terminal-owned-infinite-loop-exit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 2), plan.root.nodes.len);
    const outer = plan.root.nodes[1].infinite_loop;
    try std.testing.expectEqual(outer_header, outer.header);
    try std.testing.expect(outer.exit == null);
    try std.testing.expect(outer.body_region.loop_exit == null);
    const inner = outer.body_region.nodes[1].infinite_loop;
    try std.testing.expectEqual(inner_header, inner.header);
    try std.testing.expectEqual(outer_latch, inner.exit.?);
    const normal_boundary = inner.body_region.nodes[1].loop_boundary;
    const side_boundary = normal_boundary.body_region.nodes[0].loop_boundary;
    try std.testing.expectEqual(terminal_forward, side_boundary.boundary.side_exit.entry_edge.target);
    try std.testing.expectEqual(@as(usize, 2), side_boundary.boundary.side_exit.region.nodes.len);
    try std.testing.expectEqual(terminal_forward, side_boundary.boundary.side_exit.region.nodes[0].block);
    try std.testing.expectEqual(terminal, side_boundary.boundary.side_exit.region.nodes[1].block);
}

test "infinite loop may sequence a conditional join and repeated unique-exit breaks" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const body = ir.BlockId.fromIndex(1);
    const optional_then = ir.BlockId.fromIndex(2);
    const first_break = ir.BlockId.fromIndex(3);
    const second_break = ir.BlockId.fromIndex(4);
    const latch = ir.BlockId.fromIndex(5);
    const break_forward = ir.BlockId.fromIndex(6);
    const exit_block = ir.BlockId.fromIndex(7);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = body } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = optional_then },
            .else_edge = .{ .target = first_break },
        } } },
        .{ .id = optional_then, .function = function_id, .terminator = .{ .jump = .{ .target = first_break } } },
        .{ .id = first_break, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = exit_block },
            .else_edge = .{ .target = second_break },
        } } },
        .{ .id = second_break, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = break_forward },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = break_forward, .function = function_id, .terminator = .{ .jump = .{ .target = exit_block } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ header, body, optional_then, first_break, second_break, latch, break_forward, exit_block },
        .entry_block = header,
    }};
    const program: ir.Program = .{
        .program_id = "infinite-loop-repeated-breaks",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[0].infinite_loop;
    try std.testing.expectEqual(exit_block, loop.exit.?);
    try std.testing.expectEqual(@as(usize, 3), loop.body_region.nodes.len);
    try std.testing.expectEqual(header, loop.body_region.nodes[0].block);
    const optional = loop.body_region.nodes[1].branch;
    try std.testing.expectEqual(first_break, optional.join.?);
    try std.testing.expectEqual(first_break, optional.else_region.stop.?);
    const first_boundary = loop.body_region.nodes[2].loop_boundary;
    try std.testing.expectEqual(first_break, first_boundary.block);
    try std.testing.expectEqual(exit_block, first_boundary.boundary.exit.target);
    const second_boundary = first_boundary.body_region.nodes[0].loop_boundary;
    try std.testing.expectEqual(second_break, second_boundary.block);
    try std.testing.expectEqual(break_forward, second_boundary.boundary.side_exit.entry_edge.target);
    try std.testing.expectEqual(exit_block, second_boundary.boundary.side_exit.region.stop.?);
}

test "infinite loop owns multiple semantic exits converging at its enclosing stop" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const first_exit_path = ir.BlockId.fromIndex(3);
    const decision = ir.BlockId.fromIndex(4);
    const second_exit_path = ir.BlockId.fromIndex(5);
    const latch = ir.BlockId.fromIndex(6);
    const exit_block = ir.BlockId.fromIndex(7);
    const outer_condition = ir.ValueId.fromIndex(0);
    const first_condition = ir.ValueId.fromIndex(1);
    const second_condition = ir.ValueId.fromIndex(2);
    const first_value = ir.ValueId.fromIndex(3);
    const second_value = ir.ValueId.fromIndex(4);
    const first_instruction = ir.InstructionId.fromIndex(0);
    const second_instruction = ir.InstructionId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = outer_condition,
            .then_edge = .{ .target = header },
            .else_edge = .{ .target = exit_block },
        } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = body } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = first_condition,
            .then_edge = .{ .target = first_exit_path },
            .else_edge = .{ .target = decision },
        } } },
        .{ .id = first_exit_path, .function = function_id, .instructions = &.{first_instruction}, .terminator = .{ .jump = .{ .target = exit_block } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = second_condition,
            .then_edge = .{ .target = second_exit_path },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = second_exit_path, .function = function_id, .instructions = &.{second_instruction}, .terminator = .{ .jump = .{ .target = exit_block } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ outer_condition, first_condition, second_condition },
        .blocks = &.{ decision, entry, second_exit_path, latch, header, first_exit_path, body, exit_block },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = outer_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = first_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = second_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 2 } },
        .{ .id = first_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = first_instruction, .index = 0 } } },
        .{ .id = second_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = second_instruction, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = first_instruction,
            .block = first_exit_path,
            .operation = .{ .constant = .{ .integer = "1" } },
            .results = &.{first_value},
            .effects = .pure,
        },
        .{
            .id = second_instruction,
            .block = second_exit_path,
            .operation = .{ .constant = .{ .integer = "2" } },
            .results = &.{second_value},
            .effects = .pure,
        },
    };
    const program: ir.Program = .{
        .program_id = "infinite-loop-multiple-semantic-exits",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const outer = plan.root.nodes[0].branch;
    try std.testing.expectEqual(exit_block, outer.join.?);
    const loop = outer.then_region.nodes[0].infinite_loop;
    try std.testing.expectEqual(header, loop.header);
    try std.testing.expectEqual(exit_block, loop.exit.?);
    const first_boundary = loop.body_region.nodes[1].loop_boundary;
    try std.testing.expectEqual(first_exit_path, first_boundary.boundary.side_exit.entry_edge.target);
    try std.testing.expectEqual(exit_block, first_boundary.boundary.side_exit.region.stop.?);
    const second_boundary = first_boundary.body_region.nodes[0].loop_boundary;
    try std.testing.expectEqual(second_exit_path, second_boundary.boundary.side_exit.entry_edge.target);
    try std.testing.expectEqual(exit_block, second_boundary.boundary.side_exit.region.stop.?);
}

test "root branch loop owns multiple semantic exits converging outside the cycle" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const first_body = ir.BlockId.fromIndex(1);
    const second_body = ir.BlockId.fromIndex(2);
    const first_exit_path = ir.BlockId.fromIndex(3);
    const second_exit_path = ir.BlockId.fromIndex(4);
    const latch = ir.BlockId.fromIndex(5);
    const exit_block = ir.BlockId.fromIndex(6);
    const header_condition = ir.ValueId.fromIndex(0);
    const first_condition = ir.ValueId.fromIndex(1);
    const second_condition = ir.ValueId.fromIndex(2);
    const first_value = ir.ValueId.fromIndex(3);
    const second_value = ir.ValueId.fromIndex(4);
    const first_instruction = ir.InstructionId.fromIndex(0);
    const second_instruction = ir.InstructionId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = header_condition,
            .then_edge = .{ .target = first_body },
            .else_edge = .{ .target = second_body },
        } } },
        .{ .id = first_body, .function = function_id, .terminator = .{ .branch = .{
            .condition = first_condition,
            .then_edge = .{ .target = first_exit_path },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = second_body, .function = function_id, .terminator = .{ .branch = .{
            .condition = second_condition,
            .then_edge = .{ .target = second_exit_path },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = first_exit_path, .function = function_id, .instructions = &.{first_instruction}, .terminator = .{ .jump = .{ .target = exit_block } } },
        .{ .id = second_exit_path, .function = function_id, .instructions = &.{second_instruction}, .terminator = .{ .jump = .{ .target = exit_block } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ header_condition, first_condition, second_condition },
        .blocks = &.{ second_body, header, second_exit_path, latch, first_exit_path, first_body, exit_block },
        .entry_block = header,
    }};
    const values = [_]ir.Value{
        .{ .id = header_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = first_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = second_condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 2 } },
        .{ .id = first_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = first_instruction, .index = 0 } } },
        .{ .id = second_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = second_instruction, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = first_instruction,
            .block = first_exit_path,
            .operation = .{ .constant = .{ .integer = "1" } },
            .results = &.{first_value},
            .effects = .pure,
        },
        .{
            .id = second_instruction,
            .block = second_exit_path,
            .operation = .{ .constant = .{ .integer = "2" } },
            .results = &.{second_value},
            .effects = .pure,
        },
    };
    const program: ir.Program = .{
        .program_id = "root-branch-loop-multiple-semantic-exits",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[0].infinite_loop;
    try std.testing.expectEqual(exit_block, loop.exit.?);
    try std.testing.expectEqual(exit_block, plan.root.nodes[1].block);
}

test "infinite natural loop may branch into independent backedges" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const left = ir.BlockId.fromIndex(1);
    const right = ir.BlockId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = left },
            .else_edge = .{ .target = right },
        } } },
        .{ .id = left, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = right, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ right, header, left },
        .entry_block = header,
    }};
    const program: ir.Program = .{
        .program_id = "infinite-branch-loop-plan",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    const loop = plan.root.nodes[0].infinite_loop;
    const header_branch = loop.body_region.nodes[0].branch;
    try std.testing.expect(header_branch.join == null);
    try std.testing.expectEqual(left, header_branch.then_region.nodes[0].block);
    try std.testing.expectEqual(right, header_branch.else_region.nodes[0].block);
}

test "source-shaped infinite loop may contain sequential conditional joins" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const unreachable_exit = ir.BlockId.fromIndex(3);
    const first_then = ir.BlockId.fromIndex(4);
    const first_dead_else = ir.BlockId.fromIndex(5);
    const first_join = ir.BlockId.fromIndex(6);
    const second_then = ir.BlockId.fromIndex(7);
    const second_dead_else = ir.BlockId.fromIndex(8);
    const second_join = ir.BlockId.fromIndex(9);
    const third_then = ir.BlockId.fromIndex(10);
    const third_dead_else = ir.BlockId.fromIndex(11);
    const third_join = ir.BlockId.fromIndex(12);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = body } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = first_then },
            .else_edge = .{ .target = first_join },
        } } },
        .{ .id = unreachable_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = first_then, .function = function_id, .terminator = .{ .jump = .{ .target = first_join } } },
        .{ .id = first_dead_else, .function = function_id, .terminator = .{ .jump = .{ .target = first_join } } },
        .{ .id = first_join, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = second_then },
            .else_edge = .{ .target = second_join },
        } } },
        .{ .id = second_then, .function = function_id, .terminator = .{ .jump = .{ .target = second_join } } },
        .{ .id = second_dead_else, .function = function_id, .terminator = .{ .jump = .{ .target = second_join } } },
        .{ .id = second_join, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = third_then },
            .else_edge = .{ .target = third_join },
        } } },
        .{ .id = third_then, .function = function_id, .terminator = .{ .jump = .{ .target = third_join } } },
        .{ .id = third_dead_else, .function = function_id, .terminator = .{ .jump = .{ .target = third_join } } },
        .{ .id = third_join, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ entry, header, body, unreachable_exit, first_then, first_dead_else, first_join, second_then, second_dead_else, second_join, third_then, third_dead_else, third_join },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "source-shaped-infinite-sequential-conditions",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 2), plan.root.nodes.len);
    try std.testing.expectEqual(entry, plan.root.nodes[0].block);
    const loop = plan.root.nodes[1].infinite_loop;
    try std.testing.expectEqual(header, loop.header);
    try std.testing.expectEqual(@as(usize, 5), loop.body_region.nodes.len);
}

test "irreducible two-entry cycle remains unsupported" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const first = ir.BlockId.fromIndex(1);
    const second = ir.BlockId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = first },
            .else_edge = .{ .target = second },
        } } },
        .{ .id = first, .function = function_id, .terminator = .{ .jump = .{ .target = second } } },
        .{ .id = second, .function = function_id, .terminator = .{ .jump = .{ .target = first } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ second, entry, first },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "irreducible-cycle-plan",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    try std.testing.expectError(error.UnsupportedShape, Plan.init(std.testing.allocator, &analysis));
}

test "authenticated arbitrary fallback uses the shared block budget" {
    const function_id = ir.FunctionId.fromIndex(0);
    var large_block_ids: [Plan.arbitrary_fallback_block_limit + 1]ir.BlockId = undefined;
    var boundary_block_ids: [Plan.arbitrary_fallback_block_limit]ir.BlockId = undefined;
    const function = ir.Function{
        .id = function_id,
        .blocks = &large_block_ids,
        .entry_block = ir.BlockId.fromIndex(0),
    };
    const rewrite = ir.CfgEdgeRewrite{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = ir.BlockId.fromIndex(0),
        .kind = .jump,
        .from = .{ .target = ir.BlockId.fromIndex(0) },
        .to = .{ .target = ir.BlockId.fromIndex(0) },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{rewrite};
    const program = ir.Program{
        .program_id = "authenticated-arbitrary-fallback-budget",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };

    try std.testing.expect(Plan.shouldUseArbitraryFallbackForFunction(&program, function));

    var boundary_function = function;
    boundary_function.blocks = &boundary_block_ids;
    try std.testing.expect(!Plan.shouldUseArbitraryFallbackForFunction(&program, boundary_function));

    var no_history_program = program;
    no_history_program.edge_rewrites = &.{};
    try std.testing.expect(!Plan.shouldUseArbitraryFallbackForFunction(&no_history_program, function));
}
