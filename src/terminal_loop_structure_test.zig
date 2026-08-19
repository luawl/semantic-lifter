const std = @import("std");
const lifter = @import("semantic_lifter");
const ir = lifter.ir;
const cfg = lifter.cfg;
const Plan = lifter.structure.Plan;
const emit_luau = lifter.emit_luau;

fn expectPlan(program: *const ir.Program, function: ir.Function) !Plan {
    var analysis = try cfg.Analysis.init(std.testing.allocator, program, function);
    defer analysis.deinit();
    return Plan.init(std.testing.allocator, &analysis);
}

test "short-circuit loop selects its nonterminal continuation beside a terminal arm" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const true_forward = ir.BlockId.fromIndex(1);
    const right_guard = ir.BlockId.fromIndex(2);
    const guard_join = ir.BlockId.fromIndex(3);
    const body = ir.BlockId.fromIndex(4);
    const latch = ir.BlockId.fromIndex(5);
    const exit = ir.BlockId.fromIndex(6);
    const early_return = ir.BlockId.fromIndex(7);
    const exit_left = ir.BlockId.fromIndex(8);
    const exit_right = ir.BlockId.fromIndex(9);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = true_forward },
            .else_edge = .{ .target = right_guard },
        } } },
        .{ .id = true_forward, .function = function_id, .terminator = .{ .jump = .{ .target = guard_join } } },
        .{ .id = right_guard, .function = function_id, .terminator = .{ .jump = .{ .target = guard_join } } },
        .{ .id = guard_join, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = early_return },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(3),
            .then_edge = .{ .target = exit_left },
            .else_edge = .{ .target = exit_right },
        } } },
        .{ .id = early_return, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = exit_left, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = exit_right, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .blocks = &.{ header, true_forward, right_guard, guard_join, body, latch, exit, early_return, exit_left, exit_right },
        .entry_block = header,
    };
    const program: ir.Program = .{
        .program_id = "short-circuit-loop-terminal-arm",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var plan = try expectPlan(&program, function);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 2), plan.root.nodes.len);
    const loop = plan.root.nodes[0].infinite_loop;
    try std.testing.expectEqual(header, loop.header);
    try std.testing.expectEqual(exit, loop.exit.?);
    try std.testing.expectEqual(exit, plan.root.nodes[1].branch.block);
}

test "short-circuit loop may terminate through every exit arm" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const true_forward = ir.BlockId.fromIndex(1);
    const right_guard = ir.BlockId.fromIndex(2);
    const guard_join = ir.BlockId.fromIndex(3);
    const body = ir.BlockId.fromIndex(4);
    const latch = ir.BlockId.fromIndex(5);
    const ordinary_return = ir.BlockId.fromIndex(6);
    const early_return = ir.BlockId.fromIndex(7);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = true_forward },
            .else_edge = .{ .target = right_guard },
        } } },
        .{ .id = true_forward, .function = function_id, .terminator = .{ .jump = .{ .target = guard_join } } },
        .{ .id = right_guard, .function = function_id, .terminator = .{ .jump = .{ .target = guard_join } } },
        .{ .id = guard_join, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = ordinary_return },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = early_return },
            .else_edge = .{ .target = latch },
        } } },
        .{ .id = latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = ordinary_return, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = early_return, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .blocks = &.{ header, true_forward, right_guard, guard_join, body, latch, ordinary_return, early_return },
        .entry_block = header,
    };
    const program: ir.Program = .{
        .program_id = "short-circuit-loop-all-terminal-arms",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var plan = try expectPlan(&program, function);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 1), plan.root.nodes.len);
    const loop = plan.root.nodes[0].infinite_loop;
    try std.testing.expectEqual(header, loop.header);
    try std.testing.expect(loop.exit == null);
    try std.testing.expect(loop.body_region.loop_exit == null);
}

test "loop-local arms converge after a nested terminal bypass" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const decision = ir.BlockId.fromIndex(1);
    const direct = ir.BlockId.fromIndex(2);
    const nested = ir.BlockId.fromIndex(3);
    const nested_continue = ir.BlockId.fromIndex(4);
    const join = ir.BlockId.fromIndex(5);
    const ordinary_return = ir.BlockId.fromIndex(6);
    const early_return = ir.BlockId.fromIndex(7);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = decision },
            .else_edge = .{ .target = ordinary_return },
        } } },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = nested },
            .else_edge = .{ .target = direct },
        } } },
        .{ .id = direct, .function = function_id, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = nested, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = early_return },
            .else_edge = .{ .target = nested_continue },
        } } },
        .{ .id = nested_continue, .function = function_id, .terminator = .{ .jump = .{ .target = join } } },
        .{ .id = join, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = ordinary_return, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = early_return, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .blocks = &.{ header, decision, direct, nested, nested_continue, join, ordinary_return, early_return },
        .entry_block = header,
    };
    const program: ir.Program = .{
        .program_id = "loop-local-terminal-bypass-convergence",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var plan = try expectPlan(&program, function);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 2), plan.root.nodes.len);
    const loop = plan.root.nodes[0].loop;
    try std.testing.expectEqual(ordinary_return, loop.exit_edge.target);
    const decision_branch = loop.body_region.nodes[0].branch;
    try std.testing.expectEqual(join, decision_branch.join.?);
    try std.testing.expectEqual(join, loop.body_region.nodes[1].block);
    try std.testing.expectEqual(ordinary_return, plan.root.nodes[1].block);
}

test "direct shared terminal owns a sibling with a reducible divergent route" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const nested = ir.BlockId.fromIndex(1);
    const loop_header = ir.BlockId.fromIndex(2);
    const loop_latch = ir.BlockId.fromIndex(3);
    const terminal_relay = ir.BlockId.fromIndex(4);
    const loop_return = ir.BlockId.fromIndex(5);
    const shared_return = ir.BlockId.fromIndex(6);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = nested },
            .else_edge = .{ .target = shared_return },
        } } },
        .{ .id = nested, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = loop_header },
            .else_edge = .{ .target = terminal_relay },
        } } },
        .{ .id = loop_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = loop_latch },
            .else_edge = .{ .target = loop_return },
        } } },
        .{ .id = loop_latch, .function = function_id, .terminator = .{ .jump = .{ .target = loop_header } } },
        .{ .id = terminal_relay, .function = function_id, .terminator = .{ .jump = .{ .target = shared_return } } },
        .{ .id = loop_return, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = shared_return, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .blocks = &.{ entry, nested, loop_header, loop_latch, terminal_relay, loop_return, shared_return },
        .entry_block = entry,
    };
    const program: ir.Program = .{
        .program_id = "direct-shared-terminal-divergent-sibling",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var plan = try expectPlan(&program, function);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 2), plan.root.nodes.len);
    const branch = plan.root.nodes[0].branch;
    try std.testing.expectEqual(entry, branch.block);
    try std.testing.expectEqual(shared_return, branch.join.?);
    try std.testing.expectEqual(shared_return, plan.root.nodes[1].block);
}

test "direct shared terminal rejects external region ownership" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const external_relay = ir.BlockId.fromIndex(2);
    const nested = ir.BlockId.fromIndex(3);
    const loop_header = ir.BlockId.fromIndex(4);
    const loop_latch = ir.BlockId.fromIndex(5);
    const terminal_relay = ir.BlockId.fromIndex(6);
    const loop_return = ir.BlockId.fromIndex(7);
    const shared_return = ir.BlockId.fromIndex(8);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = external_relay },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = nested },
            .else_edge = .{ .target = shared_return },
        } } },
        .{ .id = external_relay, .function = function_id, .terminator = .{ .jump = .{ .target = shared_return } } },
        .{ .id = nested, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = loop_header },
            .else_edge = .{ .target = terminal_relay },
        } } },
        .{ .id = loop_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(3),
            .then_edge = .{ .target = loop_latch },
            .else_edge = .{ .target = loop_return },
        } } },
        .{ .id = loop_latch, .function = function_id, .terminator = .{ .jump = .{ .target = loop_header } } },
        .{ .id = terminal_relay, .function = function_id, .terminator = .{ .jump = .{ .target = shared_return } } },
        .{ .id = loop_return, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = shared_return, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .blocks = &.{ entry, owner, external_relay, nested, loop_header, loop_latch, terminal_relay, loop_return, shared_return },
        .entry_block = entry,
    };
    const program: ir.Program = .{
        .program_id = "direct-shared-terminal-external-entry",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    try std.testing.expectError(error.UnsupportedShape, expectPlan(&program, function));
}

test "transparent shared loop suffix becomes the divergent branch join" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const body = ir.BlockId.fromIndex(1);
    const owner = ir.BlockId.fromIndex(2);
    const direct_latch = ir.BlockId.fromIndex(3);
    const shared_relay = ir.BlockId.fromIndex(4);
    const shared_relay_two = ir.BlockId.fromIndex(5);
    const shared_latch = ir.BlockId.fromIndex(6);
    const exit = ir.BlockId.fromIndex(7);
    const blocks = [_]ir.Block{
        .{
            .id = header,
            .function = function_id,
            .parameters = &.{ir.ValueId.fromIndex(0)},
            .terminator = .{ .branch = .{
                .condition = ir.ValueId.fromIndex(0),
                .then_edge = .{ .target = body },
                .else_edge = .{ .target = exit },
            } },
        },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = shared_latch },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = direct_latch },
            .else_edge = .{ .target = shared_relay },
        } } },
        .{ .id = direct_latch, .function = function_id, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &.{ir.ValueId.fromIndex(0)},
        } } },
        .{ .id = shared_relay, .function = function_id, .terminator = .{ .jump = .{ .target = shared_relay_two } } },
        .{ .id = shared_relay_two, .function = function_id, .terminator = .{ .jump = .{ .target = shared_latch } } },
        .{ .id = shared_latch, .function = function_id, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &.{ir.ValueId.fromIndex(0)},
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .blocks = &.{ header, body, owner, direct_latch, shared_relay, shared_relay_two, shared_latch, exit },
        .entry_block = header,
    };
    const program: ir.Program = .{
        .program_id = "owned-transparent-loop-stop-suffix",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
    };
    var plan = try expectPlan(&program, function);
    defer plan.deinit();

    try std.testing.expectEqual(@as(usize, 2), plan.root.nodes.len);
    const loop = plan.root.nodes[0].loop;
    const divergent = loop.body_region.nodes[0].branch;
    try std.testing.expectEqual(shared_latch, divergent.join.?);
    try std.testing.expectEqual(@as(usize, 0), divergent.else_region.nodes.len);
    try std.testing.expectEqual(shared_latch, divergent.else_region.stop.?);
    try std.testing.expect(divergent.else_region.stop_forwarding == null);
    try std.testing.expectEqual(shared_latch, loop.body_region.nodes[1].block);
    try std.testing.expectEqual(exit, plan.root.nodes[1].block);
}

test "effectful shared loop suffix is owned once after its divergent branch" {
    const function_id = ir.FunctionId.fromIndex(0);
    const header = ir.BlockId.fromIndex(0);
    const body = ir.BlockId.fromIndex(1);
    const owner = ir.BlockId.fromIndex(2);
    const direct_latch = ir.BlockId.fromIndex(3);
    const shared_relay = ir.BlockId.fromIndex(4);
    const shared_relay_two = ir.BlockId.fromIndex(5);
    const shared_latch = ir.BlockId.fromIndex(6);
    const exit = ir.BlockId.fromIndex(7);
    const shared_instruction = ir.InstructionId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = header, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(1),
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = shared_latch },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(2),
            .then_edge = .{ .target = direct_latch },
            .else_edge = .{ .target = shared_relay },
        } } },
        .{ .id = direct_latch, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = shared_relay, .function = function_id, .terminator = .{ .jump = .{ .target = shared_relay_two } } },
        .{ .id = shared_relay_two, .function = function_id, .terminator = .{ .jump = .{ .target = shared_latch } } },
        .{
            .id = shared_latch,
            .function = function_id,
            .instructions = &.{shared_instruction},
            .terminator = .{ .jump = .{ .target = header } },
        },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = shared_instruction,
        .block = shared_latch,
        .operation = .{ .constant = .nil_value },
        .results = &.{},
        .effects = .pure,
    }};
    const function: ir.Function = .{
        .id = function_id,
        .blocks = &.{ header, body, owner, direct_latch, shared_relay, shared_relay_two, shared_latch, exit },
        .entry_block = header,
    };
    const program: ir.Program = .{
        .program_id = "owned-live-loop-stop-suffix",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &.{},
    };
    var plan = try expectPlan(&program, function);
    defer plan.deinit();

    const loop = plan.root.nodes[0].loop;
    const divergent = loop.body_region.nodes[0].branch;
    try std.testing.expectEqual(shared_latch, divergent.join.?);
    try std.testing.expectEqual(@as(usize, 0), divergent.else_region.nodes.len);
    try std.testing.expectEqual(shared_latch, divergent.else_region.stop.?);
    try std.testing.expectEqual(shared_latch, loop.body_region.nodes[1].block);
    try std.testing.expectEqual(@as(usize, 1), blocks[shared_latch.index()].instructions.len);
}

test "terminal loop side exit does not emit an unreachable break" {
    const function_id = ir.FunctionId.fromIndex(0);
    const preheader = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const decision = ir.BlockId.fromIndex(2);
    const latch = ir.BlockId.fromIndex(3);
    const side_branch = ir.BlockId.fromIndex(4);
    const first_return = ir.BlockId.fromIndex(5);
    const second_return = ir.BlockId.fromIndex(6);
    const loop_return = ir.BlockId.fromIndex(7);
    const proof = ir.EvidenceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = ir.ValueId.fromIndex(0), .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = ir.ValueId.fromIndex(1), .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = ir.ValueId.fromIndex(2), .function = function_id, .type = .boolean, .origin = .{ .parameter = 2 } },
    };
    const blocks = [_]ir.Block{
        .{ .id = preheader, .function = function_id, .terminator = .{ .jump = .{ .target = header } }, .evidence = &.{proof} },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = decision } }, .evidence = &.{proof} },
        .{ .id = decision, .function = function_id, .terminator = .{ .branch = .{
            .condition = values[0].id,
            .then_edge = .{ .target = side_branch },
            .else_edge = .{ .target = latch },
        } }, .evidence = &.{proof} },
        .{ .id = latch, .function = function_id, .terminator = .{ .branch = .{
            .condition = values[1].id,
            .then_edge = .{ .target = loop_return },
            .else_edge = .{ .target = header },
        } }, .evidence = &.{proof} },
        .{ .id = side_branch, .function = function_id, .terminator = .{ .branch = .{
            .condition = values[2].id,
            .then_edge = .{ .target = first_return },
            .else_edge = .{ .target = second_return },
        } }, .evidence = &.{proof} },
        .{ .id = first_return, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
        .{ .id = second_return, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
        .{ .id = loop_return, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
    };
    const function: ir.Function = .{
        .id = function_id,
        .parameters = &.{ values[0].id, values[1].id, values[2].id },
        .blocks = &.{ preheader, header, decision, latch, side_branch, first_return, second_return, loop_return },
        .entry_block = preheader,
        .evidence = &.{proof},
    };
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:terminal-loop-side-exit-emission",
    }};
    const program: ir.Program = .{
        .program_id = "terminal-loop-side-exit-emission",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
    };
    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);

    var lines = std.mem.splitScalar(u8, source, '\n');
    var previous_was_return = false;
    while (lines.next()) |line| {
        const statement = std.mem.trim(u8, line, " \t\r");
        if (previous_was_return) try std.testing.expect(!std.mem.eql(u8, statement, "break"));
        previous_was_return = std.mem.eql(u8, statement, "return") or std.mem.startsWith(u8, statement, "return ");
    }
}
