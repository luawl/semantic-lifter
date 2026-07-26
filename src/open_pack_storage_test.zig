const std = @import("std");
const diagnostics = @import("diagnostics.zig");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const fixtures = @import("fixtures.zig");
const validation = @import("validate.zig");
const emit_luau = @import("emit_luau.zig");
const emit_luau_branch_stmt = @import("emit_luau_branch_stmt.zig");
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

fn observableGap(id: ir.InstructionId, block: ir.BlockId, value: ir.ValueId) ir.Instruction {
    return .{
        .id = id,
        .block = block,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "observed",
            .value = value,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
        .evidence = &fixture_evidence,
    };
}

fn expectStoredReentry(
    program: *const ir.Program,
    producer: ir.InstructionId,
    adjustment: ir.InstructionId,
    return_block: ir.BlockId,
) !void {
    var plan = try pack_plan.Plan.init(std.testing.allocator, program);
    defer plan.deinit();
    try std.testing.expect(plan.role(producer) == .stored_invocation_producer);
    try std.testing.expectEqual(producer, plan.role(adjustment).stored_adjustment);
    try std.testing.expectEqual(pack_plan.TerminatorRole{ .stored_pack_return = producer }, plan.terminatorRole(return_block));
    var report = try validation.validate(std.testing.allocator, program, .readable_luau);
    defer report.deinit();
    try std.testing.expect(report.isClean());
    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, program);
    defer std.testing.allocator.free(source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "producer()"));
}

test "pack materialization stores focused same-block, cross-block, and structured reentrant uses" {
    const fixture = fixtures.open_pack_adjust_module;
    const gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    var instructions = fixture.instructions ++ [_]ir.Instruction{
        observableGap(gap_id, fixture.b_entry, fixture.v_callee),
    };
    const instruction_ids = [_]ir.InstructionId{ fixture.i_get, fixture.i_call, gap_id, fixture.i_adjust };
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].instructions = &instruction_ids;
    blocks[fixture.b_entry.index()].terminator = .{ .return_expanded = .{
        .values = &.{fixture.v_first},
        .pack = fixture.p_results,
    } };
    var program = fixture.program;
    program.blocks = &blocks;
    program.instructions = &instructions;
    var values = fixture.values;
    values[fixture.v_callee.index()].name_hint = "producer";
    values[fixture.v_first.index()].name_hint = "materialized";
    program.values = &values;

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var multiple_use_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer multiple_use_report.deinit();
    try std.testing.expect(multiple_use_report.isClean());
    var stored_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer stored_plan.deinit();
    try std.testing.expect(stored_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, stored_plan.role(fixture.i_adjust).stored_adjustment);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        stored_plan.terminatorRole(fixture.b_entry),
    );
    const stored_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(stored_source);
    const stored_producer_offset = std.mem.indexOf(u8, stored_source, "end)(producer())") orelse return error.TestUnexpectedResult;
    const stored_gap_offset = std.mem.indexOf(u8, stored_source, "observed = producer") orelse return error.TestUnexpectedResult;
    const stored_adjustment_offset = std.mem.indexOf(u8, stored_source, "materialized = __lifter_rawget(") orelse return error.TestUnexpectedResult;
    const stored_return_offset = std.mem.indexOf(u8, stored_source, "return materialized, __lifter_table_unpack(") orelse return error.TestUnexpectedResult;
    try std.testing.expect(stored_producer_offset < stored_gap_offset);
    try std.testing.expect(stored_gap_offset < stored_adjustment_offset);
    try std.testing.expect(stored_adjustment_offset < stored_return_offset);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, stored_source, "producer()"));

    const forwarding_block = ir.BlockId.fromIndex(fixture.blocks.len);
    const consumer_block = ir.BlockId.fromIndex(fixture.blocks.len + 1);
    const producer_instruction_ids = [_]ir.InstructionId{ fixture.i_get, fixture.i_call };
    const forwarding_instruction_ids = [_]ir.InstructionId{gap_id};
    const consumer_instruction_ids = [_]ir.InstructionId{fixture.i_adjust};
    var cross_blocks = fixture.blocks ++ [_]ir.Block{
        .{
            .id = forwarding_block,
            .function = fixture.f_entry,
            .instructions = &forwarding_instruction_ids,
            .terminator = .{ .jump = .{ .target = consumer_block } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = consumer_block,
            .function = fixture.f_entry,
            .instructions = &consumer_instruction_ids,
            .terminator = .{ .return_values = &.{fixture.v_first} },
            .evidence = &fixture_evidence,
        },
    };
    cross_blocks[fixture.b_entry.index()].instructions = &producer_instruction_ids;
    cross_blocks[fixture.b_entry.index()].terminator = .{ .jump = .{ .target = forwarding_block } };
    instructions[gap_id.index()].block = forwarding_block;
    instructions[fixture.i_adjust.index()].block = consumer_block;
    var functions = fixture.functions;
    const function_blocks = [_]ir.BlockId{ fixture.b_entry, forwarding_block, consumer_block };
    functions[fixture.f_entry.index()].blocks = &function_blocks;
    program.functions = &functions;
    program.blocks = &cross_blocks;

    cross_blocks[consumer_block.index()].terminator = .{ .return_expanded = .{
        .values = &.{fixture.v_first},
        .pack = fixture.p_results,
    } };
    var cross_block_stored_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer cross_block_stored_plan.deinit();
    try std.testing.expect(cross_block_stored_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, cross_block_stored_plan.role(fixture.i_adjust).stored_adjustment);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        cross_block_stored_plan.terminatorRole(consumer_block),
    );
    var cross_block_stored_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer cross_block_stored_report.deinit();
    try std.testing.expect(cross_block_stored_report.isClean());
    const cross_block_stored_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(cross_block_stored_source);
    const cross_block_declaration_offset = std.mem.indexOf(u8, cross_block_stored_source, "local __lifter_pack_0") orelse return error.TestUnexpectedResult;
    const cross_block_producer_offset = std.mem.indexOf(u8, cross_block_stored_source, "end)(producer())") orelse return error.TestUnexpectedResult;
    const cross_block_gap_offset = std.mem.indexOf(u8, cross_block_stored_source, "observed = producer") orelse return error.TestUnexpectedResult;
    const cross_block_adjustment_offset = std.mem.indexOf(u8, cross_block_stored_source, "materialized = __lifter_rawget(") orelse return error.TestUnexpectedResult;
    const cross_block_return_offset = std.mem.indexOf(u8, cross_block_stored_source, "return materialized, __lifter_table_unpack(") orelse return error.TestUnexpectedResult;
    try std.testing.expect(cross_block_declaration_offset < cross_block_producer_offset);
    try std.testing.expect(cross_block_producer_offset < cross_block_gap_offset);
    try std.testing.expect(cross_block_gap_offset < cross_block_adjustment_offset);
    try std.testing.expect(cross_block_adjustment_offset < cross_block_return_offset);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, cross_block_stored_source, "producer()"));

    const second_adjustment_id = ir.InstructionId.fromIndex(instructions.len);
    const second_result_ids = [_]ir.ValueId{
        ir.ValueId.fromIndex(values.len),
        ir.ValueId.fromIndex(values.len + 1),
        ir.ValueId.fromIndex(values.len + 2),
    };
    const widened_return_block = ir.BlockId.fromIndex(cross_blocks.len);
    var widened_instructions = instructions ++ [_]ir.Instruction{.{
        .id = second_adjustment_id,
        .block = widened_return_block,
        .operation = .{ .adjust_pack = fixture.p_results },
        .results = &second_result_ids,
        .effects = .pure,
        .evidence = &fixture_evidence,
    }};
    var widened_values = values ++ [_]ir.Value{
        .{ .id = second_result_ids[0], .function = fixture.f_entry, .name_hint = "wide_first", .origin = .{ .instruction_result = .{ .instruction = second_adjustment_id, .index = 0 } } },
        .{ .id = second_result_ids[1], .function = fixture.f_entry, .name_hint = "wide_second", .origin = .{ .instruction_result = .{ .instruction = second_adjustment_id, .index = 1 } } },
        .{ .id = second_result_ids[2], .function = fixture.f_entry, .name_hint = "wide_third", .origin = .{ .instruction_result = .{ .instruction = second_adjustment_id, .index = 2 } } },
    };
    const widened_return_instruction_ids = [_]ir.InstructionId{second_adjustment_id};
    var widened_blocks = cross_blocks ++ [_]ir.Block{.{
        .id = widened_return_block,
        .function = fixture.f_entry,
        .instructions = &widened_return_instruction_ids,
        .terminator = .{ .return_expanded = .{
            .values = &.{ fixture.v_first, second_result_ids[2] },
            .pack = fixture.p_results,
        } },
        .evidence = &fixture_evidence,
    }};
    widened_blocks[consumer_block.index()].terminator = .{ .jump = .{ .target = widened_return_block } };
    const widened_function_blocks = [_]ir.BlockId{ fixture.b_entry, forwarding_block, consumer_block, widened_return_block };
    var widened_functions = functions;
    widened_functions[fixture.f_entry.index()].blocks = &widened_function_blocks;
    var widened_program = program;
    widened_program.functions = &widened_functions;
    widened_program.blocks = &widened_blocks;
    widened_program.instructions = &widened_instructions;
    widened_program.values = &widened_values;

    var widened_core_report = try validation.validate(std.testing.allocator, &widened_program, .core);
    defer widened_core_report.deinit();
    try std.testing.expect(widened_core_report.isClean());
    var widened_report = try validation.validate(std.testing.allocator, &widened_program, .readable_luau);
    defer widened_report.deinit();
    try std.testing.expect(widened_report.isClean());
    var widened_plan = try pack_plan.Plan.init(std.testing.allocator, &widened_program);
    defer widened_plan.deinit();
    try std.testing.expect(widened_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, widened_plan.role(fixture.i_adjust).stored_adjustment);
    try std.testing.expectEqual(fixture.i_call, widened_plan.role(second_adjustment_id).stored_adjustment);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        widened_plan.terminatorRole(widened_return_block),
    );
    const widened_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &widened_program);
    defer std.testing.allocator.free(widened_source);
    const widened_first_adjustment_offset = std.mem.indexOf(u8, widened_source, "materialized = __lifter_rawget(") orelse return error.TestUnexpectedResult;
    const widened_second_adjustment_offset = std.mem.indexOf(u8, widened_source, "wide_first, wide_second, wide_third = __lifter_rawget(") orelse return error.TestUnexpectedResult;
    const widened_return_offset = std.mem.indexOf(u8, widened_source, "return materialized, wide_third, __lifter_table_unpack(") orelse return error.TestUnexpectedResult;
    try std.testing.expect(widened_first_adjustment_offset < widened_second_adjustment_offset);
    try std.testing.expect(widened_second_adjustment_offset < widened_return_offset);
    try std.testing.expect(std.mem.indexOf(u8, widened_source, "__lifter_rawget(__lifter_pack_0, 3)") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, widened_source, "producer()"));

    const reentry_return_block = ir.BlockId.fromIndex(cross_blocks.len);
    var reentry_blocks = cross_blocks ++ [_]ir.Block{.{
        .id = reentry_return_block,
        .function = fixture.f_entry,
        .terminator = .{ .return_expanded = .{
            .values = &.{fixture.v_first},
            .pack = fixture.p_results,
        } },
        .evidence = &fixture_evidence,
    }};
    reentry_blocks[consumer_block.index()].terminator = .{ .branch = .{
        .condition = fixture.v_first,
        .then_edge = .{ .target = reentry_return_block },
        .else_edge = .{ .target = fixture.b_entry },
    } };
    const reentry_function_blocks = [_]ir.BlockId{ fixture.b_entry, forwarding_block, consumer_block, reentry_return_block };
    var reentry_functions = functions;
    reentry_functions[fixture.f_entry.index()].blocks = &reentry_function_blocks;
    var reentry_program = program;
    reentry_program.functions = &reentry_functions;
    reentry_program.blocks = &reentry_blocks;
    var reentry_core_report = try validation.validate(std.testing.allocator, &reentry_program, .core);
    defer reentry_core_report.deinit();
    try std.testing.expect(reentry_core_report.isClean());
    var reentry_plan = try pack_plan.Plan.init(std.testing.allocator, &reentry_program);
    defer reentry_plan.deinit();
    try std.testing.expect(reentry_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, reentry_plan.role(fixture.i_adjust).stored_adjustment);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        reentry_plan.terminatorRole(reentry_return_block),
    );
    var reentry_report = try validation.validate(std.testing.allocator, &reentry_program, .readable_luau);
    defer reentry_report.deinit();
    try std.testing.expect(reentry_report.isClean());
    const reentry_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &reentry_program);
    defer std.testing.allocator.free(reentry_source);
    const reentry_declaration_offset = std.mem.indexOf(u8, reentry_source, "__lifter_pack_0") orelse return error.TestUnexpectedResult;
    const reentry_loop_offset = std.mem.indexOf(u8, reentry_source, "while true do") orelse return error.TestUnexpectedResult;
    const reentry_assignment_offset = std.mem.indexOf(u8, reentry_source, "__lifter_pack_0 = (function(...)") orelse return error.TestUnexpectedResult;
    const reentry_return_offset = std.mem.indexOf(u8, reentry_source, "return materialized, __lifter_table_unpack(") orelse return error.TestUnexpectedResult;
    try std.testing.expect(reentry_declaration_offset < reentry_loop_offset);
    try std.testing.expect(reentry_loop_offset < reentry_assignment_offset);
    try std.testing.expect(reentry_assignment_offset < reentry_return_offset);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, reentry_source, "producer()"));

    var early_continue_blocks = reentry_blocks;
    early_continue_blocks[forwarding_block.index()].terminator = .{ .branch = .{
        .condition = fixture.v_callee,
        .then_edge = .{ .target = fixture.b_entry },
        .else_edge = .{ .target = consumer_block },
    } };
    var early_continue_program = reentry_program;
    early_continue_program.blocks = &early_continue_blocks;
    var early_continue_core_report = try validation.validate(std.testing.allocator, &early_continue_program, .core);
    defer early_continue_core_report.deinit();
    try std.testing.expect(early_continue_core_report.isClean());
    var early_continue_plan = try pack_plan.Plan.init(std.testing.allocator, &early_continue_program);
    defer early_continue_plan.deinit();
    try std.testing.expect(early_continue_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, early_continue_plan.role(fixture.i_adjust).stored_adjustment);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        early_continue_plan.terminatorRole(reentry_return_block),
    );
    var early_continue_report = try validation.validate(std.testing.allocator, &early_continue_program, .readable_luau);
    defer early_continue_report.deinit();
    try std.testing.expect(early_continue_report.isClean());
    const early_continue_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &early_continue_program);
    defer std.testing.allocator.free(early_continue_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, early_continue_source, "producer()"));

    const unconditional_continue_block = ir.BlockId.fromIndex(reentry_blocks.len);
    var unconditional_backedge_blocks = reentry_blocks ++ [_]ir.Block{.{
        .id = unconditional_continue_block,
        .function = fixture.f_entry,
        .terminator = .{ .jump = .{ .target = fixture.b_entry } },
        .evidence = &fixture_evidence,
    }};
    unconditional_backedge_blocks[forwarding_block.index()].terminator = .{ .branch = .{
        .condition = fixture.v_callee,
        .then_edge = .{ .target = unconditional_continue_block },
        .else_edge = .{ .target = consumer_block },
    } };
    const unconditional_function_blocks = [_]ir.BlockId{
        fixture.b_entry,
        forwarding_block,
        consumer_block,
        reentry_return_block,
        unconditional_continue_block,
    };
    var unconditional_functions = reentry_functions;
    unconditional_functions[fixture.f_entry.index()].blocks = &unconditional_function_blocks;
    var unconditional_backedge_program = reentry_program;
    unconditional_backedge_program.functions = &unconditional_functions;
    unconditional_backedge_program.blocks = &unconditional_backedge_blocks;
    var unconditional_core_report = try validation.validate(std.testing.allocator, &unconditional_backedge_program, .core);
    defer unconditional_core_report.deinit();
    try std.testing.expect(unconditional_core_report.isClean());
    var unconditional_plan = try pack_plan.Plan.init(std.testing.allocator, &unconditional_backedge_program);
    defer unconditional_plan.deinit();
    try std.testing.expect(unconditional_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, unconditional_plan.role(fixture.i_adjust).stored_adjustment);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        unconditional_plan.terminatorRole(reentry_return_block),
    );
    var unconditional_report = try validation.validate(std.testing.allocator, &unconditional_backedge_program, .readable_luau);
    defer unconditional_report.deinit();
    try std.testing.expect(unconditional_report.isClean());
    const unconditional_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &unconditional_backedge_program);
    defer std.testing.allocator.free(unconditional_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, unconditional_source, "producer()"));

    const parameterized_seed = ir.ValueId.fromIndex(values.len);
    const parameterized_header_parameter = ir.ValueId.fromIndex(values.len + 1);
    const parameterized_continue_parameter = ir.ValueId.fromIndex(values.len + 2);
    var parameterized_values = values ++ [_]ir.Value{
        .{
            .id = parameterized_seed,
            .function = fixture.f_entry,
            .type = .function,
            .name_hint = "loop_seed",
            .origin = .{ .parameter = 0 },
        },
        .{
            .id = parameterized_header_parameter,
            .function = fixture.f_entry,
            .type = .function,
            .name_hint = "loop_carried",
            .origin = .{ .block_parameter = .{ .block = fixture.b_entry, .index = 0 } },
        },
        .{
            .id = parameterized_continue_parameter,
            .function = fixture.f_entry,
            .type = .function,
            .name_hint = "forwarded_loop_carried",
            .origin = .{ .block_parameter = .{ .block = unconditional_continue_block, .index = 0 } },
        },
    };
    const parameterized_preheader_block = ir.BlockId.fromIndex(unconditional_backedge_blocks.len);
    var parameterized_blocks = unconditional_backedge_blocks ++ [_]ir.Block{.{
        .id = parameterized_preheader_block,
        .function = fixture.f_entry,
        .terminator = .{ .jump = .{ .target = fixture.b_entry, .arguments = &.{parameterized_seed} } },
        .evidence = &fixture_evidence,
    }};
    parameterized_blocks[fixture.b_entry.index()].parameters = &.{parameterized_header_parameter};
    parameterized_blocks[unconditional_continue_block.index()].parameters = &.{parameterized_continue_parameter};
    parameterized_blocks[unconditional_continue_block.index()].terminator.jump.arguments = &.{parameterized_continue_parameter};
    parameterized_blocks[forwarding_block.index()].terminator.branch.then_edge.arguments = &.{parameterized_seed};
    parameterized_blocks[consumer_block.index()].terminator.branch.else_edge.arguments = &.{parameterized_seed};
    const parameterized_function_parameters = [_]ir.ValueId{parameterized_seed};
    const parameterized_function_blocks = [_]ir.BlockId{
        parameterized_preheader_block,
        fixture.b_entry,
        forwarding_block,
        consumer_block,
        reentry_return_block,
        unconditional_continue_block,
    };
    var parameterized_functions = unconditional_functions;
    parameterized_functions[fixture.f_entry.index()].parameters = &parameterized_function_parameters;
    parameterized_functions[fixture.f_entry.index()].blocks = &parameterized_function_blocks;
    parameterized_functions[fixture.f_entry.index()].entry_block = parameterized_preheader_block;
    var parameterized_program = unconditional_backedge_program;
    parameterized_program.functions = &parameterized_functions;
    parameterized_program.blocks = &parameterized_blocks;
    parameterized_program.values = &parameterized_values;
    var parameterized_core_report = try validation.validate(std.testing.allocator, &parameterized_program, .core);
    defer parameterized_core_report.deinit();
    try std.testing.expect(parameterized_core_report.isClean());
    var parameterized_plan = try pack_plan.Plan.init(std.testing.allocator, &parameterized_program);
    defer parameterized_plan.deinit();
    try std.testing.expect(parameterized_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, parameterized_plan.role(fixture.i_adjust).stored_adjustment);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        parameterized_plan.terminatorRole(reentry_return_block),
    );
    var parameterized_report = try validation.validate(std.testing.allocator, &parameterized_program, .readable_luau);
    defer parameterized_report.deinit();
    try std.testing.expect(parameterized_report.isClean());
    const parameterized_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &parameterized_program);
    defer std.testing.allocator.free(parameterized_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, parameterized_source, "producer()"));

    const continue_copy_id = ir.InstructionId.fromIndex(instructions.len);
    const continue_copy_result = ir.ValueId.fromIndex(parameterized_values.len);
    const copy_values = parameterized_values ++ [_]ir.Value{.{
        .id = continue_copy_result,
        .function = fixture.f_entry,
        .type = .function,
        .name_hint = "copied_loop_carried",
        .origin = .{ .instruction_result = .{ .instruction = continue_copy_id, .index = 0 } },
    }};
    const copy_instructions = instructions ++ [_]ir.Instruction{.{
        .id = continue_copy_id,
        .block = unconditional_continue_block,
        .operation = .{ .copy = parameterized_continue_parameter },
        .results = &.{continue_copy_result},
        .effects = .pure,
        .evidence = &fixture_evidence,
    }};
    var copy_blocks = parameterized_blocks;
    copy_blocks[unconditional_continue_block.index()].instructions = &.{continue_copy_id};
    copy_blocks[unconditional_continue_block.index()].terminator.jump.arguments = &.{continue_copy_result};
    var copy_program = parameterized_program;
    copy_program.blocks = &copy_blocks;
    copy_program.instructions = &copy_instructions;
    copy_program.values = &copy_values;
    var copy_core_report = try validation.validate(std.testing.allocator, &copy_program, .core);
    defer copy_core_report.deinit();
    try std.testing.expect(copy_core_report.isClean());
    var copy_plan = try pack_plan.Plan.init(std.testing.allocator, &copy_program);
    defer copy_plan.deinit();
    try std.testing.expect(copy_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, copy_plan.role(fixture.i_adjust).stored_adjustment);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        copy_plan.terminatorRole(reentry_return_block),
    );
    var copy_report = try validation.validate(std.testing.allocator, &copy_program, .readable_luau);
    defer copy_report.deinit();
    try std.testing.expect(copy_report.isClean());
    const copy_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &copy_program);
    defer std.testing.allocator.free(copy_source);
    try std.testing.expectEqualStrings(parameterized_source, copy_source);

    const second_continue_copy_id = ir.InstructionId.fromIndex(copy_instructions.len);
    const second_continue_copy_result = ir.ValueId.fromIndex(copy_values.len);
    const chained_copy_values = copy_values ++ [_]ir.Value{.{
        .id = second_continue_copy_result,
        .function = fixture.f_entry,
        .type = .function,
        .name_hint = "twice_copied_loop_carried",
        .origin = .{ .instruction_result = .{ .instruction = second_continue_copy_id, .index = 0 } },
    }};
    const chained_copy_instructions = copy_instructions ++ [_]ir.Instruction{.{
        .id = second_continue_copy_id,
        .block = unconditional_continue_block,
        .operation = .{ .copy = continue_copy_result },
        .results = &.{second_continue_copy_result},
        .effects = .pure,
        .evidence = &fixture_evidence,
    }};
    const chained_copy_ids = [_]ir.InstructionId{ continue_copy_id, second_continue_copy_id };
    var chained_copy_blocks = copy_blocks;
    chained_copy_blocks[unconditional_continue_block.index()].instructions = &chained_copy_ids;
    chained_copy_blocks[unconditional_continue_block.index()].terminator.jump.arguments = &.{second_continue_copy_result};
    var chained_copy_program = copy_program;
    chained_copy_program.blocks = &chained_copy_blocks;
    chained_copy_program.instructions = &chained_copy_instructions;
    chained_copy_program.values = &chained_copy_values;
    var chained_copy_core_report = try validation.validate(std.testing.allocator, &chained_copy_program, .core);
    defer chained_copy_core_report.deinit();
    try std.testing.expect(chained_copy_core_report.isClean());
    var chained_copy_plan = try pack_plan.Plan.init(std.testing.allocator, &chained_copy_program);
    defer chained_copy_plan.deinit();
    try std.testing.expect(chained_copy_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, chained_copy_plan.role(fixture.i_adjust).stored_adjustment);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        chained_copy_plan.terminatorRole(reentry_return_block),
    );
    var chained_copy_report = try validation.validate(std.testing.allocator, &chained_copy_program, .readable_luau);
    defer chained_copy_report.deinit();
    try std.testing.expect(chained_copy_report.isClean());
    const chained_copy_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &chained_copy_program);
    defer std.testing.allocator.free(chained_copy_source);
    try std.testing.expectEqualStrings(parameterized_source, chained_copy_source);

    const relay_block = ir.BlockId.fromIndex(chained_copy_blocks.len);
    const relay_parameter = ir.ValueId.fromIndex(chained_copy_values.len);
    const relay_copy_result = ir.ValueId.fromIndex(chained_copy_values.len + 1);
    const relay_copy_id = ir.InstructionId.fromIndex(chained_copy_instructions.len);
    const relay_values = chained_copy_values ++ [_]ir.Value{
        .{
            .id = relay_parameter,
            .function = fixture.f_entry,
            .type = .function,
            .name_hint = "relayed_loop_carried",
            .origin = .{ .block_parameter = .{ .block = relay_block, .index = 0 } },
        },
        .{
            .id = relay_copy_result,
            .function = fixture.f_entry,
            .type = .function,
            .name_hint = "copied_relayed_loop_carried",
            .origin = .{ .instruction_result = .{ .instruction = relay_copy_id, .index = 0 } },
        },
    };
    const relay_instructions = chained_copy_instructions ++ [_]ir.Instruction{.{
        .id = relay_copy_id,
        .block = relay_block,
        .operation = .{ .copy = relay_parameter },
        .results = &.{relay_copy_result},
        .effects = .pure,
        .evidence = &fixture_evidence,
    }};
    var relay_blocks = chained_copy_blocks ++ [_]ir.Block{.{
        .id = relay_block,
        .function = fixture.f_entry,
        .parameters = &.{relay_parameter},
        .instructions = &.{relay_copy_id},
        .terminator = .{ .jump = .{ .target = fixture.b_entry, .arguments = &.{relay_copy_result} } },
        .evidence = &fixture_evidence,
    }};
    relay_blocks[unconditional_continue_block.index()].terminator.jump = .{
        .target = relay_block,
        .arguments = &.{second_continue_copy_result},
    };
    const relay_function_blocks = parameterized_function_blocks ++ [_]ir.BlockId{relay_block};
    var relay_functions = parameterized_functions;
    relay_functions[fixture.f_entry.index()].blocks = &relay_function_blocks;
    var relay_program = chained_copy_program;
    relay_program.functions = &relay_functions;
    relay_program.blocks = &relay_blocks;
    relay_program.instructions = &relay_instructions;
    relay_program.values = &relay_values;
    var relay_core_report = try validation.validate(std.testing.allocator, &relay_program, .core);
    defer relay_core_report.deinit();
    try std.testing.expect(relay_core_report.isClean());
    var relay_plan = try pack_plan.Plan.init(std.testing.allocator, &relay_program);
    defer relay_plan.deinit();
    try std.testing.expect(relay_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, relay_plan.role(fixture.i_adjust).stored_adjustment);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        relay_plan.terminatorRole(reentry_return_block),
    );
    var relay_report = try validation.validate(std.testing.allocator, &relay_program, .readable_luau);
    defer relay_report.deinit();
    try std.testing.expect(relay_report.isClean());
    const relay_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &relay_program);
    defer std.testing.allocator.free(relay_source);
    try std.testing.expectEqualStrings(parameterized_source, relay_source);

    var effectful_relay_instructions = relay_instructions;
    effectful_relay_instructions[relay_copy_id.index()].effects = .semantic_environment_write;
    var effectful_relay_program = relay_program;
    effectful_relay_program.instructions = &effectful_relay_instructions;
    var effectful_relay_core_report = try validation.validate(std.testing.allocator, &effectful_relay_program, .core);
    defer effectful_relay_core_report.deinit();
    try std.testing.expect(effectful_relay_core_report.isClean());
    var effectful_relay_plan = try pack_plan.Plan.init(std.testing.allocator, &effectful_relay_program);
    defer effectful_relay_plan.deinit();
    try std.testing.expect(effectful_relay_plan.role(fixture.i_call) == .ordinary);
    try std.testing.expect(effectful_relay_plan.role(fixture.i_adjust) == .ordinary);
    try std.testing.expect(effectful_relay_plan.terminatorRole(reentry_return_block) == .ordinary);
    var effectful_relay_report = try validation.validate(std.testing.allocator, &effectful_relay_program, .readable_luau);
    defer effectful_relay_report.deinit();
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&effectful_relay_report, .variadic_result_arity));
    try std.testing.expectEqual(@as(usize, 2), diagnosticCount(&effectful_relay_report, .unsupported_readable_pack_operation));

    const extra_predecessor = ir.BlockId.fromIndex(relay_blocks.len);
    var second_predecessor_blocks = relay_blocks ++ [_]ir.Block{.{
        .id = extra_predecessor,
        .function = fixture.f_entry,
        .terminator = .{ .branch = .{
            .condition = fixture.v_callee,
            .then_edge = .{ .target = consumer_block },
            .else_edge = .{ .target = relay_block, .arguments = &.{parameterized_header_parameter} },
        } },
        .evidence = &fixture_evidence,
    }};
    second_predecessor_blocks[forwarding_block.index()].terminator.branch.else_edge = .{ .target = extra_predecessor };
    const second_predecessor_function_blocks = relay_function_blocks ++ [_]ir.BlockId{extra_predecessor};
    var second_predecessor_functions = relay_functions;
    second_predecessor_functions[fixture.f_entry.index()].blocks = &second_predecessor_function_blocks;
    var second_predecessor_program = relay_program;
    second_predecessor_program.functions = &second_predecessor_functions;
    second_predecessor_program.blocks = &second_predecessor_blocks;
    var second_predecessor_core_report = try validation.validate(std.testing.allocator, &second_predecessor_program, .core);
    defer second_predecessor_core_report.deinit();
    try std.testing.expect(second_predecessor_core_report.isClean());
    var second_predecessor_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &second_predecessor_program,
        second_predecessor_functions[fixture.f_entry.index()],
    );
    defer second_predecessor_analysis.deinit();
    var second_predecessor_structure = try structure.Plan.init(std.testing.allocator, &second_predecessor_analysis);
    defer second_predecessor_structure.deinit();
    const shared_reentries = second_predecessor_structure.root.nodes[1].latch_loop.shared_reentries.?;
    try std.testing.expectEqualSlices(ir.BlockId, &.{ unconditional_continue_block, relay_block }, shared_reentries.blocks);
    try std.testing.expectEqual(@as(usize, 2), shared_reentries.entries.len);
    try std.testing.expectEqualSlices(u32, &.{ 0, 1, 1 }, shared_reentries.route_indices);
    try std.testing.expectEqualSlices(ir.ValueId, &.{parameterized_seed}, shared_reentries.entries[0].edge.arguments);
    try std.testing.expectEqualSlices(ir.ValueId, &.{parameterized_header_parameter}, shared_reentries.entries[1].edge.arguments);
    var second_predecessor_plan = try pack_plan.Plan.init(std.testing.allocator, &second_predecessor_program);
    defer second_predecessor_plan.deinit();
    try std.testing.expect(second_predecessor_plan.role(fixture.i_call) == .stored_invocation_producer);
    try std.testing.expectEqual(fixture.i_call, second_predecessor_plan.role(fixture.i_adjust).stored_adjustment);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = fixture.i_call },
        second_predecessor_plan.terminatorRole(reentry_return_block),
    );
    var second_predecessor_report = try validation.validate(std.testing.allocator, &second_predecessor_program, .readable_luau);
    defer second_predecessor_report.deinit();
    try std.testing.expect(second_predecessor_report.isClean());
    const second_predecessor_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &second_predecessor_program);
    defer std.testing.allocator.free(second_predecessor_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, second_predecessor_source, "producer()"));

    const external_predecessor = ir.BlockId.fromIndex(second_predecessor_blocks.len);
    const external_predecessor_blocks = second_predecessor_blocks ++ [_]ir.Block{.{
        .id = external_predecessor,
        .function = fixture.f_entry,
        .terminator = .{ .jump = .{ .target = relay_block, .arguments = &.{parameterized_seed} } },
        .evidence = &fixture_evidence,
    }};
    const external_predecessor_function_blocks = second_predecessor_function_blocks ++ [_]ir.BlockId{external_predecessor};
    var dead_external_functions = second_predecessor_functions;
    dead_external_functions[fixture.f_entry.index()].blocks = &external_predecessor_function_blocks;
    var dead_external_program = second_predecessor_program;
    dead_external_program.functions = &dead_external_functions;
    dead_external_program.blocks = &external_predecessor_blocks;
    try expectStoredReentry(&dead_external_program, fixture.i_call, fixture.i_adjust, reentry_return_block);

    var reachable_external_blocks = external_predecessor_blocks;
    reachable_external_blocks[parameterized_preheader_block.index()].terminator = .{ .branch = .{
        .condition = parameterized_seed,
        .then_edge = .{ .target = fixture.b_entry, .arguments = &.{parameterized_seed} },
        .else_edge = .{ .target = external_predecessor },
    } };
    var reachable_external_program = dead_external_program;
    reachable_external_program.blocks = &reachable_external_blocks;
    var reachable_external_core_report = try validation.validate(std.testing.allocator, &reachable_external_program, .core);
    defer reachable_external_core_report.deinit();
    try std.testing.expect(reachable_external_core_report.isClean());
    var reachable_external_plan = try pack_plan.Plan.init(std.testing.allocator, &reachable_external_program);
    defer reachable_external_plan.deinit();
    try std.testing.expect(reachable_external_plan.role(fixture.i_call) == .ordinary);
    try std.testing.expect(reachable_external_plan.role(fixture.i_adjust) == .ordinary);
    try std.testing.expect(reachable_external_plan.terminatorRole(reentry_return_block) == .ordinary);
    var reachable_external_report = try validation.validate(std.testing.allocator, &reachable_external_program, .readable_luau);
    defer reachable_external_report.deinit();
    try std.testing.expect(!reachable_external_report.isClean());

    {
        const first_shared_arguments = shared_reentries.entries[0].edge.arguments;
        shared_reentries.entries[0].edge.arguments = shared_reentries.entries[1].edge.arguments;
        defer shared_reentries.entries[0].edge.arguments = first_shared_arguments;
        try std.testing.expectError(
            error.UnsupportedControlFlow,
            emit_luau_branch_stmt.validateSharedPathsAlloc(std.testing.allocator, &second_predecessor_program, shared_reentries),
        );
    }

    var effectful_shared_instructions = relay_instructions;
    effectful_shared_instructions[relay_copy_id.index()].effects = .semantic_environment_write;
    var effectful_shared_program = second_predecessor_program;
    effectful_shared_program.instructions = &effectful_shared_instructions;
    var effectful_shared_core_report = try validation.validate(std.testing.allocator, &effectful_shared_program, .core);
    defer effectful_shared_core_report.deinit();
    try std.testing.expect(effectful_shared_core_report.isClean());
    var effectful_shared_plan = try pack_plan.Plan.init(std.testing.allocator, &effectful_shared_program);
    defer effectful_shared_plan.deinit();
    try std.testing.expect(effectful_shared_plan.role(fixture.i_call) == .ordinary);
    try std.testing.expect(effectful_shared_plan.role(fixture.i_adjust) == .ordinary);
    try std.testing.expect(effectful_shared_plan.terminatorRole(reentry_return_block) == .ordinary);

    var non_copy_shared_instructions = relay_instructions;
    non_copy_shared_instructions[relay_copy_id.index()].operation = .{ .function_ref = fixture.f_entry };
    var non_copy_shared_program = second_predecessor_program;
    non_copy_shared_program.instructions = &non_copy_shared_instructions;
    var non_copy_shared_core_report = try validation.validate(std.testing.allocator, &non_copy_shared_program, .core);
    defer non_copy_shared_core_report.deinit();
    try std.testing.expect(non_copy_shared_core_report.isClean());
    var non_copy_shared_plan = try pack_plan.Plan.init(std.testing.allocator, &non_copy_shared_program);
    defer non_copy_shared_plan.deinit();
    try std.testing.expect(non_copy_shared_plan.role(fixture.i_call) == .ordinary);
    try std.testing.expect(non_copy_shared_plan.role(fixture.i_adjust) == .ordinary);
    try std.testing.expect(non_copy_shared_plan.terminatorRole(reentry_return_block) == .ordinary);

    var duplicate_shared_entry_blocks = second_predecessor_blocks;
    duplicate_shared_entry_blocks[extra_predecessor.index()].terminator.branch.then_edge = .{
        .target = relay_block,
        .arguments = &.{parameterized_seed},
    };
    var duplicate_shared_entry_program = second_predecessor_program;
    duplicate_shared_entry_program.blocks = &duplicate_shared_entry_blocks;
    var duplicate_shared_entry_core_report = try validation.validate(std.testing.allocator, &duplicate_shared_entry_program, .core);
    defer duplicate_shared_entry_core_report.deinit();
    try std.testing.expect(duplicate_shared_entry_core_report.isClean());
    var duplicate_shared_entry_plan = try pack_plan.Plan.init(std.testing.allocator, &duplicate_shared_entry_program);
    defer duplicate_shared_entry_plan.deinit();
    try std.testing.expect(duplicate_shared_entry_plan.role(fixture.i_call) == .ordinary);
    try std.testing.expect(duplicate_shared_entry_plan.role(fixture.i_adjust) == .ordinary);
    try std.testing.expect(duplicate_shared_entry_plan.terminatorRole(reentry_return_block) == .ordinary);
    var duplicate_shared_entry_report = try validation.validate(std.testing.allocator, &duplicate_shared_entry_program, .readable_luau);
    defer duplicate_shared_entry_report.deinit();
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&duplicate_shared_entry_report, .variadic_result_arity));
    try std.testing.expectEqual(@as(usize, 0), diagnosticCount(&duplicate_shared_entry_report, .unsupported_readable_pack_operation));

    var pure_non_copy_instructions = chained_copy_instructions;
    pure_non_copy_instructions[second_continue_copy_id.index()].operation = .{ .function_ref = fixture.f_entry };
    var pure_non_copy_program = chained_copy_program;
    pure_non_copy_program.instructions = &pure_non_copy_instructions;
    var pure_non_copy_core_report = try validation.validate(std.testing.allocator, &pure_non_copy_program, .core);
    defer pure_non_copy_core_report.deinit();
    try std.testing.expect(pure_non_copy_core_report.isClean());
    var pure_non_copy_plan = try pack_plan.Plan.init(std.testing.allocator, &pure_non_copy_program);
    defer pure_non_copy_plan.deinit();
    try std.testing.expect(pure_non_copy_plan.role(fixture.i_call) == .ordinary);
    try std.testing.expect(pure_non_copy_plan.role(fixture.i_adjust) == .ordinary);
    try std.testing.expect(pure_non_copy_plan.terminatorRole(reentry_return_block) == .ordinary);
    var pure_non_copy_report = try validation.validate(std.testing.allocator, &pure_non_copy_program, .readable_luau);
    defer pure_non_copy_report.deinit();
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&pure_non_copy_report, .variadic_result_arity));
    try std.testing.expectEqual(@as(usize, 2), diagnosticCount(&pure_non_copy_report, .unsupported_readable_pack_operation));

    var effectful_copy_instructions = copy_instructions;
    effectful_copy_instructions[continue_copy_id.index()].effects = .semantic_environment_write;
    var effectful_copy_program = copy_program;
    effectful_copy_program.instructions = &effectful_copy_instructions;
    var effectful_copy_core_report = try validation.validate(std.testing.allocator, &effectful_copy_program, .core);
    defer effectful_copy_core_report.deinit();
    try std.testing.expect(effectful_copy_core_report.isClean());
    var effectful_copy_plan = try pack_plan.Plan.init(std.testing.allocator, &effectful_copy_program);
    defer effectful_copy_plan.deinit();
    try std.testing.expect(effectful_copy_plan.role(fixture.i_call) == .ordinary);
    try std.testing.expect(effectful_copy_plan.role(fixture.i_adjust) == .ordinary);
    try std.testing.expect(effectful_copy_plan.terminatorRole(reentry_return_block) == .ordinary);
    var effectful_copy_report = try validation.validate(std.testing.allocator, &effectful_copy_program, .readable_luau);
    defer effectful_copy_report.deinit();
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&effectful_copy_report, .variadic_result_arity));
    try std.testing.expectEqual(@as(usize, 2), diagnosticCount(&effectful_copy_report, .unsupported_readable_pack_operation));

    var multiple_early_continue_blocks = unconditional_backedge_blocks;
    multiple_early_continue_blocks[forwarding_block.index()].terminator = .{ .branch = .{
        .condition = fixture.v_callee,
        .then_edge = .{ .target = fixture.b_entry },
        .else_edge = .{ .target = unconditional_continue_block },
    } };
    multiple_early_continue_blocks[unconditional_continue_block.index()].terminator = .{ .branch = .{
        .condition = fixture.v_callee,
        .then_edge = .{ .target = fixture.b_entry },
        .else_edge = .{ .target = consumer_block },
    } };
    var multiple_early_continue_program = unconditional_backedge_program;
    multiple_early_continue_program.blocks = &multiple_early_continue_blocks;
    var multiple_early_continue_core_report = try validation.validate(std.testing.allocator, &multiple_early_continue_program, .core);
    defer multiple_early_continue_core_report.deinit();
    try std.testing.expect(multiple_early_continue_core_report.isClean());
    try expectStoredReentry(&multiple_early_continue_program, fixture.i_call, fixture.i_adjust, reentry_return_block);

    const second_unconditional_continue_block = ir.BlockId.fromIndex(unconditional_backedge_blocks.len);
    const second_unconditional_split_block = ir.BlockId.fromIndex(unconditional_backedge_blocks.len + 1);
    var multiple_unconditional_blocks = unconditional_backedge_blocks ++ [_]ir.Block{
        .{
            .id = second_unconditional_continue_block,
            .function = fixture.f_entry,
            .terminator = .{ .jump = .{ .target = fixture.b_entry } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = second_unconditional_split_block,
            .function = fixture.f_entry,
            .terminator = .{ .branch = .{
                .condition = fixture.v_callee,
                .then_edge = .{ .target = second_unconditional_continue_block },
                .else_edge = .{ .target = consumer_block },
            } },
            .evidence = &fixture_evidence,
        },
    };
    multiple_unconditional_blocks[forwarding_block.index()].terminator = .{ .branch = .{
        .condition = fixture.v_callee,
        .then_edge = .{ .target = unconditional_continue_block },
        .else_edge = .{ .target = second_unconditional_split_block },
    } };
    const multiple_unconditional_function_blocks = [_]ir.BlockId{
        fixture.b_entry,
        forwarding_block,
        consumer_block,
        reentry_return_block,
        unconditional_continue_block,
        second_unconditional_continue_block,
        second_unconditional_split_block,
    };
    var multiple_unconditional_functions = unconditional_functions;
    multiple_unconditional_functions[fixture.f_entry.index()].blocks = &multiple_unconditional_function_blocks;
    var multiple_unconditional_program = unconditional_backedge_program;
    multiple_unconditional_program.functions = &multiple_unconditional_functions;
    multiple_unconditional_program.blocks = &multiple_unconditional_blocks;
    var multiple_unconditional_core_report = try validation.validate(std.testing.allocator, &multiple_unconditional_program, .core);
    defer multiple_unconditional_core_report.deinit();
    try std.testing.expect(multiple_unconditional_core_report.isClean());
    try expectStoredReentry(&multiple_unconditional_program, fixture.i_call, fixture.i_adjust, reentry_return_block);

    var mixed_continue_blocks = multiple_unconditional_blocks;
    mixed_continue_blocks[forwarding_block.index()].terminator.branch.then_edge = .{ .target = fixture.b_entry };
    var mixed_continue_program = multiple_unconditional_program;
    mixed_continue_program.blocks = &mixed_continue_blocks;
    var mixed_continue_core_report = try validation.validate(std.testing.allocator, &mixed_continue_program, .core);
    defer mixed_continue_core_report.deinit();
    try std.testing.expect(mixed_continue_core_report.isClean());
    try expectStoredReentry(&mixed_continue_program, fixture.i_call, fixture.i_adjust, reentry_return_block);

    cross_blocks[consumer_block.index()].terminator = .{ .return_values = &.{fixture.v_first} };
    var cross_block_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer cross_block_core_report.deinit();
    try std.testing.expect(cross_block_core_report.isClean());
    var cross_block_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer cross_block_report.deinit();
    try std.testing.expect(cross_block_report.isClean());
    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const producer_offset = std.mem.indexOf(u8, source, "materialized = producer()") orelse return error.TestUnexpectedResult;
    const gap_offset = std.mem.indexOf(u8, source, "observed = producer") orelse return error.TestUnexpectedResult;
    const return_offset = std.mem.indexOf(u8, source, "return materialized") orelse return error.TestUnexpectedResult;
    try std.testing.expect(producer_offset < gap_offset and gap_offset < return_offset);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "producer()"));

    const dead_block = ir.BlockId.fromIndex(cross_blocks.len);
    const blocks_with_dead = cross_blocks ++ [_]ir.Block{.{
        .id = dead_block,
        .function = fixture.f_entry,
        .terminator = .{ .jump = .{ .target = consumer_block } },
        .evidence = &fixture_evidence,
    }};
    const blocks_with_dead_ids = [_]ir.BlockId{ fixture.b_entry, forwarding_block, consumer_block, dead_block };
    var functions_with_dead = functions;
    functions_with_dead[fixture.f_entry.index()].blocks = &blocks_with_dead_ids;
    var program_with_dead = program;
    program_with_dead.functions = &functions_with_dead;
    program_with_dead.blocks = &blocks_with_dead;
    var dead_predecessor_report = try validation.validate(std.testing.allocator, &program_with_dead, .readable_luau);
    defer dead_predecessor_report.deinit();
    try std.testing.expect(dead_predecessor_report.isClean());

    cross_blocks[consumer_block.index()].terminator = .{ .jump = .{ .target = consumer_block } };
    var cyclic_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer cyclic_core_report.deinit();
    try std.testing.expect(cyclic_core_report.isClean());
    var cyclic_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer cyclic_report.deinit();
    try std.testing.expect(cyclic_report.isClean());
    const cyclic_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(cyclic_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, cyclic_source, "producer()"));
}
