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
