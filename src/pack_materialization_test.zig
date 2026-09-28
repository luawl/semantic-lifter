const std = @import("std");
const diagnostics = @import("diagnostics.zig");
const ir = @import("ir.zig");
const fixtures = @import("fixtures.zig");
const validation = @import("validate.zig");
const emit_luau = @import("emit_luau.zig");
const pack_plan = @import("pack_plan.zig");
const _pack_multi_latch_tests = @import("pack_multi_latch_test.zig");
const _open_pack_storage_tests = @import("open_pack_storage_test.zig");

comptime {
    _ = _pack_multi_latch_tests;
    _ = _open_pack_storage_tests;
}

const fixture_evidence = [_]ir.EvidenceId{fixtures.open_pack_adjust_module.proof};

const OpenInvocationRow = struct {
    operation: ir.Operation,
    effects: ir.EffectSummary,
    callee_type: ir.ValueType = .dynamic,
    callee_name: []const u8,
    result_type: ir.ValueType = .dynamic,
    result_name: []const u8,
    status_prefix: bool = false,
    expected_assignment: []const u8,
    invocation_marker: []const u8,
};

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

test "nonadjacent pack adjustment emits at the producer across an observable gap" {
    const fixture = fixtures.open_pack_adjust_module;
    const gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    var instructions = fixture.instructions ++ [_]ir.Instruction{
        observableGap(gap_id, fixture.b_entry, fixture.v_callee),
    };
    const instruction_ids = [_]ir.InstructionId{ fixture.i_get, fixture.i_call, gap_id, fixture.i_adjust };
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].instructions = &instruction_ids;
    var values = fixture.values;
    values[fixture.v_callee.index()].name_hint = "producer";
    values[fixture.v_first.index()].name_hint = "materialized";
    var program = fixture.program;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;

    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const repeated_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(repeated_source);
    try std.testing.expectEqualStrings(source, repeated_source);
    const producer_offset = std.mem.indexOf(u8, source, "local materialized = producer()") orelse return error.TestUnexpectedResult;
    const gap_offset = std.mem.indexOf(u8, source, "observed = producer") orelse return error.TestUnexpectedResult;
    const return_offset = std.mem.indexOf(u8, source, "return materialized") orelse return error.TestUnexpectedResult;
    try std.testing.expect(producer_offset < gap_offset and gap_offset < return_offset);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "producer()"));

    const boolean_prefix = [_]ir.ValueType{.boolean};
    const rows = [_]OpenInvocationRow{
        .{
            .operation = .{ .protected_call = .{ .callee = fixture.v_callee, .arguments = &.{}, .result_arity = .{ .variadic = {} } } },
            .effects = .protected_invocation,
            .callee_name = "producer",
            .result_type = .boolean,
            .result_name = "protected_ok",
            .status_prefix = true,
            .expected_assignment = "local protected_ok = __lifter_pcall(producer)",
            .invocation_marker = "__lifter_pcall(",
        },
        .{
            .operation = .{ .coroutine_resume = .{ .thread = fixture.v_callee, .arguments = &.{}, .result_arity = .{ .variadic = {} } } },
            .effects = .coroutine_resume,
            .callee_type = .{ .kind = .thread },
            .callee_name = "resume_thread",
            .result_type = .boolean,
            .result_name = "resume_ok",
            .status_prefix = true,
            .expected_assignment = "local resume_ok = __lifter_coroutine_resume(resume_thread)",
            .invocation_marker = "__lifter_coroutine_resume(",
        },
        .{
            .operation = .{ .namecall = .{ .receiver = fixture.v_callee, .method = "produce", .arguments = &.{}, .result_arity = .{ .variadic = {} } } },
            .effects = .namecall,
            .callee_type = .{ .kind = .table },
            .callee_name = "namecall_receiver",
            .result_name = "namecall_first",
            .expected_assignment = "local namecall_first = namecall_receiver:produce()",
            .invocation_marker = ":produce(",
        },
        .{
            .operation = .{ .coroutine_yield = .{ .arguments = &.{fixture.v_callee}, .result_arity = .{ .variadic = {} } } },
            .effects = .coroutine_yield,
            .callee_name = "yielded_outbound",
            .result_name = "resumed_first",
            .expected_assignment = "local resumed_first = __lifter_coroutine_yield(yielded_outbound)",
            .invocation_marker = "__lifter_coroutine_yield(",
        },
    };
    for (rows) |row| {
        var row_instructions = instructions;
        row_instructions[fixture.i_call.index()].operation = row.operation;
        row_instructions[fixture.i_call.index()].effects = row.effects;
        var row_values = values;
        row_values[fixture.v_callee.index()].type = row.callee_type;
        row_values[fixture.v_callee.index()].name_hint = row.callee_name;
        row_values[fixture.v_first.index()].type = row.result_type;
        row_values[fixture.v_first.index()].name_hint = row.result_name;
        var row_packs = fixture.value_packs;
        if (row.status_prefix) row_packs[fixture.p_results.index()].shape = .{ .prefix = &boolean_prefix, .tail = .open };
        var row_program = program;
        row_program.instructions = &row_instructions;
        row_program.values = &row_values;
        row_program.value_packs = &row_packs;

        var row_report = try validation.validate(std.testing.allocator, &row_program, .readable_luau);
        defer row_report.deinit();
        try std.testing.expect(row_report.isClean());
        const row_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &row_program);
        defer std.testing.allocator.free(row_source);
        const repeated_row_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &row_program);
        defer std.testing.allocator.free(repeated_row_source);
        try std.testing.expectEqualStrings(row_source, repeated_row_source);
        const invocation_offset = std.mem.indexOf(u8, row_source, row.expected_assignment) orelse return error.TestUnexpectedResult;
        const gap_marker = try std.fmt.allocPrint(std.testing.allocator, "observed = {s}", .{row.callee_name});
        defer std.testing.allocator.free(gap_marker);
        const row_gap_offset = std.mem.indexOf(u8, row_source, gap_marker) orelse return error.TestUnexpectedResult;
        try std.testing.expect(invocation_offset < row_gap_offset);
        try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, row_source, row.invocation_marker));
    }

    instructions[fixture.i_adjust.index()].results = &.{};
    blocks[fixture.b_entry.index()].terminator = .{ .return_values = &.{} };
    program.values = values[0..1];
    const discarded = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(discarded);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, discarded, "producer()"));
    try std.testing.expect(std.mem.indexOf(u8, discarded, "materialized") == null);
    try std.testing.expect(std.mem.indexOf(u8, discarded, "observed = producer") != null);
}

test "multiple fixed adjustments reuse a canonical same-block prefix" {
    const fixture = fixtures.open_pack_adjust_module;
    const gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const secondary_id = ir.InstructionId.fromIndex(fixture.instructions.len + 1);
    const canonical_second = ir.ValueId.fromIndex(fixture.values.len);
    const repeated_first = ir.ValueId.fromIndex(fixture.values.len + 1);
    var values = fixture.values ++ [_]ir.Value{
        .{
            .id = canonical_second,
            .function = fixture.f_entry,
            .name_hint = "canonical_second",
            .origin = .{ .instruction_result = .{ .instruction = fixture.i_adjust, .index = 1 } },
        },
        .{
            .id = repeated_first,
            .function = fixture.f_entry,
            .name_hint = "repeated_first",
            .origin = .{ .instruction_result = .{ .instruction = secondary_id, .index = 0 } },
        },
    };
    values[fixture.v_callee.index()].name_hint = "producer";
    values[fixture.v_first.index()].name_hint = "canonical_first";
    var instructions = fixture.instructions ++ [_]ir.Instruction{
        observableGap(gap_id, fixture.b_entry, fixture.v_callee),
        .{
            .id = secondary_id,
            .block = fixture.b_entry,
            .operation = .{ .adjust_pack = fixture.p_results },
            .results = &.{repeated_first},
            .effects = .pure,
            .evidence = &fixture_evidence,
        },
    };
    instructions[fixture.i_adjust.index()].results = &.{ fixture.v_first, canonical_second };
    const instruction_ids = [_]ir.InstructionId{ fixture.i_get, fixture.i_call, fixture.i_adjust, gap_id, secondary_id };
    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].instructions = &instruction_ids;
    blocks[fixture.b_entry.index()].terminator = .{ .return_values = &.{ fixture.v_first, canonical_second, repeated_first } };
    var program = fixture.program;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());
    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const producer_offset = std.mem.indexOf(u8, source, "local canonical_first, canonical_second = producer()") orelse return error.TestUnexpectedResult;
    const gap_offset = std.mem.indexOf(u8, source, "observed = producer") orelse return error.TestUnexpectedResult;
    const copy_offset = std.mem.indexOf(u8, source, "local repeated_first = canonical_first") orelse return error.TestUnexpectedResult;
    try std.testing.expect(producer_offset < gap_offset and gap_offset < copy_offset);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "producer()"));

    instructions[secondary_id.index()].results = &.{};
    blocks[fixture.b_entry.index()].terminator = .{ .return_values = &.{ fixture.v_first, canonical_second } };
    program.values = values[0..3];
    const zero_copy = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(zero_copy);
    try std.testing.expect(std.mem.indexOf(u8, zero_copy, "repeated_first") == null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, zero_copy, "producer()"));

    instructions[fixture.i_adjust.index()].results = &.{fixture.v_first};
    instructions[secondary_id.index()].results = &.{ repeated_first, canonical_second };
    values[canonical_second.index()].origin = .{ .instruction_result = .{ .instruction = secondary_id, .index = 1 } };
    blocks[fixture.b_entry.index()].terminator = .{ .return_values = &.{ fixture.v_first, repeated_first, canonical_second } };
    program.values = &values;
    var wider_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer wider_core_report.deinit();
    try std.testing.expect(wider_core_report.isClean());
    var wider_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer wider_report.deinit();
    try std.testing.expect(wider_report.isClean());
    const wider_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(wider_source);
    const wider_producer_offset = std.mem.indexOf(u8, wider_source, "local repeated_first, canonical_second = producer()") orelse return error.TestUnexpectedResult;
    const earlier_copy_offset = std.mem.indexOf(u8, wider_source, "local canonical_first = repeated_first") orelse return error.TestUnexpectedResult;
    const wider_gap_offset = std.mem.indexOf(u8, wider_source, "observed = producer") orelse return error.TestUnexpectedResult;
    try std.testing.expect(wider_producer_offset < earlier_copy_offset and earlier_copy_offset < wider_gap_offset);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, wider_source, "producer()"));
}

test "multiple fixed adjustments follow acyclic and stable closure cyclic chains" {
    const fixture = fixtures.open_pack_adjust_module;
    const child_function = ir.FunctionId.fromIndex(fixture.functions.len);
    const middle_block = ir.BlockId.fromIndex(fixture.blocks.len);
    const copy_block = ir.BlockId.fromIndex(fixture.blocks.len + 1);
    const child_block = ir.BlockId.fromIndex(fixture.blocks.len + 2);
    const preheader_block = ir.BlockId.fromIndex(fixture.blocks.len + 3);
    const setup_block = ir.BlockId.fromIndex(fixture.blocks.len + 4);
    const gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const secondary_id = ir.InstructionId.fromIndex(fixture.instructions.len + 1);
    const closure_id = ir.InstructionId.fromIndex(fixture.instructions.len + 2);
    const invoke_id = ir.InstructionId.fromIndex(fixture.instructions.len + 3);
    const invariant_id = ir.InstructionId.fromIndex(fixture.instructions.len + 4);
    const initialize_place_id = ir.InstructionId.fromIndex(fixture.instructions.len + 5);
    const read_shared_id = ir.InstructionId.fromIndex(fixture.instructions.len + 6);
    const repeated = ir.ValueId.fromIndex(fixture.values.len);
    const stable_root = ir.ValueId.fromIndex(fixture.values.len + 1);
    const root_bound = ir.ValueId.fromIndex(fixture.values.len + 2);
    const captured_root = ir.ValueId.fromIndex(fixture.values.len + 3);
    const loop_invariant = ir.ValueId.fromIndex(fixture.values.len + 4);
    const captured_invariant = ir.ValueId.fromIndex(fixture.values.len + 5);
    const invariant_seed = ir.ValueId.fromIndex(fixture.values.len + 6);
    const shared_value = ir.ValueId.fromIndex(fixture.values.len + 7);
    const shared_root = ir.PlaceId.fromIndex(0);
    const captured_shared = ir.PlaceId.fromIndex(1);
    const capture_id = ir.CaptureId.fromIndex(0);
    const invariant_capture_id = ir.CaptureId.fromIndex(1);
    const shared_capture_id = ir.CaptureId.fromIndex(2);

    var values = fixture.values ++ [_]ir.Value{
        .{
            .id = repeated,
            .function = fixture.f_entry,
            .name_hint = "repeated",
            .origin = .{ .instruction_result = .{ .instruction = secondary_id, .index = 0 } },
        },
        .{
            .id = stable_root,
            .function = fixture.f_entry,
            .type = .integer,
            .name_hint = "stable_root",
            .origin = .{ .parameter = 0 },
        },
        .{
            .id = root_bound,
            .function = fixture.f_entry,
            .type = .function,
            .name_hint = "root_bound",
            .origin = .{ .instruction_result = .{ .instruction = closure_id, .index = 0 } },
        },
        .{
            .id = captured_root,
            .function = child_function,
            .type = .integer,
            .name_hint = "captured_root",
            .origin = .{ .capture = capture_id },
        },
        .{
            .id = loop_invariant,
            .function = fixture.f_entry,
            .type = .integer,
            .name_hint = "loop_invariant",
            .origin = .{ .block_parameter = .{ .block = preheader_block, .index = 0 } },
        },
        .{
            .id = captured_invariant,
            .function = child_function,
            .type = .integer,
            .name_hint = "captured_invariant",
            .origin = .{ .capture = invariant_capture_id },
        },
        .{
            .id = invariant_seed,
            .function = fixture.f_entry,
            .type = .integer,
            .name_hint = "invariant_seed",
            .origin = .{ .instruction_result = .{ .instruction = invariant_id, .index = 0 } },
        },
        .{
            .id = shared_value,
            .function = child_function,
            .type = .integer,
            .name_hint = "shared_value",
            .origin = .{ .instruction_result = .{ .instruction = read_shared_id, .index = 0 } },
        },
    };
    var places = [_]ir.Place{
        .{
            .id = shared_root,
            .function = fixture.f_entry,
            .type = .integer,
            .name_hint = "shared_root",
            .origin = .{ .local = 0 },
            .evidence = &fixture_evidence,
        },
        .{
            .id = captured_shared,
            .function = child_function,
            .type = .integer,
            .name_hint = "captured_shared",
            .origin = .{ .capture = shared_capture_id },
            .evidence = &fixture_evidence,
        },
    };
    values[fixture.v_callee.index()].name_hint = "producer";
    values[fixture.v_first.index()].name_hint = "canonical";
    var instructions = fixture.instructions ++ [_]ir.Instruction{
        observableGap(gap_id, middle_block, fixture.v_callee),
        .{
            .id = secondary_id,
            .block = copy_block,
            .operation = .{ .adjust_pack = fixture.p_results },
            .results = &.{repeated},
            .effects = .pure,
            .evidence = &fixture_evidence,
        },
        .{
            .id = closure_id,
            .block = middle_block,
            .operation = .{ .make_closure = .{
                .function = child_function,
                .bindings = &.{ .{ .value = stable_root }, .{ .value = loop_invariant }, .{ .place = shared_root } },
            } },
            .results = &.{root_bound},
            .effects = .pure,
            .evidence = &fixture_evidence,
        },
        .{
            .id = invoke_id,
            .block = middle_block,
            .operation = .{ .call = .{
                .callee = root_bound,
                .arguments = &.{},
                .result_arity = .{ .fixed = 0 },
            } },
            .results = &.{},
            .effects = .dynamic_call,
            .evidence = &fixture_evidence,
        },
        .{
            .id = invariant_id,
            .block = setup_block,
            .operation = .{ .constant = .{ .integer = "42" } },
            .results = &.{invariant_seed},
            .effects = .pure,
            .evidence = &fixture_evidence,
        },
        .{
            .id = initialize_place_id,
            .block = preheader_block,
            .operation = .{ .place_write = .{ .place = shared_root, .value = invariant_seed } },
            .results = &.{},
            .effects = .place_write,
            .evidence = &fixture_evidence,
        },
        .{
            .id = read_shared_id,
            .block = child_block,
            .operation = .{ .place_read = captured_shared },
            .results = &.{shared_value},
            .effects = .place_read,
            .evidence = &fixture_evidence,
        },
    };
    instructions[fixture.i_adjust.index()].block = middle_block;
    const entry_instructions = [_]ir.InstructionId{ fixture.i_get, fixture.i_call };
    const middle_instructions = [_]ir.InstructionId{ fixture.i_adjust, gap_id, closure_id, invoke_id };
    const copy_instructions = [_]ir.InstructionId{secondary_id};
    const child_blocks = [_]ir.BlockId{child_block};
    const child_instructions = [_]ir.InstructionId{read_shared_id};
    const preheader_instructions = [_]ir.InstructionId{initialize_place_id};
    const setup_instructions = [_]ir.InstructionId{invariant_id};
    const captures = [_]ir.Capture{
        .{
            .id = capture_id,
            .function = child_function,
            .kind = .{ .immutable_value = captured_root },
            .evidence = &fixture_evidence,
        },
        .{
            .id = invariant_capture_id,
            .function = child_function,
            .kind = .{ .immutable_value = captured_invariant },
            .evidence = &fixture_evidence,
        },
        .{
            .id = shared_capture_id,
            .function = child_function,
            .kind = .{ .shared_place = captured_shared },
            .evidence = &fixture_evidence,
        },
    };
    var blocks = [_]ir.Block{
        .{
            .id = fixture.b_entry,
            .function = fixture.f_entry,
            .instructions = &entry_instructions,
            .terminator = .{ .jump = .{ .target = middle_block } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = middle_block,
            .function = fixture.f_entry,
            .instructions = &middle_instructions,
            .terminator = .{ .jump = .{ .target = copy_block } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = copy_block,
            .function = fixture.f_entry,
            .instructions = &copy_instructions,
            .terminator = .{ .return_values = &.{ fixture.v_first, repeated } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = child_block,
            .function = child_function,
            .instructions = &child_instructions,
            .terminator = .{ .return_values = &.{ captured_root, captured_invariant, shared_value } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = preheader_block,
            .function = fixture.f_entry,
            .parameters = &.{loop_invariant},
            .instructions = &preheader_instructions,
            .terminator = .{ .jump = .{ .target = fixture.b_entry } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = setup_block,
            .function = fixture.f_entry,
            .instructions = &setup_instructions,
            .terminator = .{ .jump = .{ .target = preheader_block, .arguments = &.{invariant_seed} } },
            .evidence = &fixture_evidence,
        },
    };
    const function_blocks = [_]ir.BlockId{ setup_block, preheader_block, fixture.b_entry, middle_block, copy_block };
    var functions = fixture.functions ++ [_]ir.Function{.{
        .id = child_function,
        .name_hint = "stable_context_body",
        .lexical_parent = fixture.f_entry,
        .captures = &.{ capture_id, invariant_capture_id, shared_capture_id },
        .entry_block = child_block,
        .blocks = &child_blocks,
        .evidence = &fixture_evidence,
    }};
    functions[fixture.f_entry.index()].blocks = &function_blocks;
    functions[fixture.f_entry.index()].entry_block = setup_block;
    functions[fixture.f_entry.index()].parameters = &.{stable_root};
    functions[fixture.f_entry.index()].local_places = &.{shared_root};
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;
    program.places = &places;
    program.captures = &captures;

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());
    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const producer_offset = std.mem.indexOf(u8, source, "local canonical = producer()") orelse return error.TestUnexpectedResult;
    const gap_offset = std.mem.indexOf(u8, source, "observed = producer") orelse return error.TestUnexpectedResult;
    const copy_offset = std.mem.indexOf(u8, source, "local repeated = canonical") orelse return error.TestUnexpectedResult;
    try std.testing.expect(producer_offset < gap_offset and gap_offset < copy_offset);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "producer()"));

    blocks[copy_block.index()].terminator = .{ .jump = .{ .target = fixture.b_entry } };
    var cyclic_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer cyclic_core_report.deinit();
    try std.testing.expect(cyclic_core_report.isClean());
    var cyclic_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer cyclic_report.deinit();
    try std.testing.expect(cyclic_report.isClean());
    const cyclic_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(cyclic_source);
    try std.testing.expect(std.mem.indexOf(u8, cyclic_source, "while true do") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, cyclic_source, "producer()"));

    places[shared_root.index()].origin = .{ .instruction = initialize_place_id };
    var allocated_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer allocated_core_report.deinit();
    try std.testing.expect(allocated_core_report.isClean());
    var allocated_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer allocated_report.deinit();
    try std.testing.expect(allocated_report.isClean());
    const allocated_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(allocated_source);
    try std.testing.expect(std.mem.indexOf(u8, allocated_source, "while true do") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, allocated_source, "producer()"));

    instructions[closure_id.index()].operation = .{ .make_closure = .{
        .function = child_function,
        .bindings = &.{ .{ .value = stable_root }, .{ .value = stable_root }, .{ .place = shared_root } },
    } };
    blocks[copy_block.index()].terminator = .{ .jump = .{ .target = preheader_block, .arguments = &.{loop_invariant} } };
    var reentered_allocation_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer reentered_allocation_core_report.deinit();
    try std.testing.expect(reentered_allocation_core_report.isClean());
    var reentered_allocation_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer reentered_allocation_report.deinit();
    try std.testing.expect(reentered_allocation_report.isClean());
    const reentered_allocation_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(reentered_allocation_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, reentered_allocation_source, "producer()"));

    instructions[invoke_id.index()].operation = .{ .environment_set = .{
        .target = .{ .ambient = {} },
        .name = "escaped",
        .value = root_bound,
    } };
    instructions[invoke_id.index()].effects = .semantic_environment_write;
    var escaping_allocation_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer escaping_allocation_report.deinit();
    try std.testing.expectEqual(@as(usize, 3), escaping_allocation_report.diagnostics.items.len);
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&escaping_allocation_report, .variadic_result_arity));
    try std.testing.expectEqual(@as(usize, 2), diagnosticCount(&escaping_allocation_report, .unsupported_readable_pack_operation));

    places[shared_root.index()].origin = .{ .local = 0 };
    instructions[closure_id.index()].operation = .{ .make_closure = .{
        .function = child_function,
        .bindings = &.{ .{ .value = stable_root }, .{ .value = loop_invariant }, .{ .place = shared_root } },
    } };
    blocks[copy_block.index()].terminator = .{ .jump = .{ .target = preheader_block, .arguments = &.{loop_invariant} } };
    var reentered_preheader_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer reentered_preheader_report.deinit();
    try std.testing.expectEqual(@as(usize, 3), reentered_preheader_report.diagnostics.items.len);
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&reentered_preheader_report, .variadic_result_arity));
    try std.testing.expectEqual(@as(usize, 2), diagnosticCount(&reentered_preheader_report, .unsupported_readable_pack_operation));
}

test "same-block producer reentry materializes through one explicit carrier" {
    const fixture = fixtures.open_pack_adjust_module;
    const exit_block = ir.BlockId.fromIndex(fixture.blocks.len);
    const gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const repeat_loop = ir.ValueId.fromIndex(fixture.values.len);

    var values = fixture.values ++ [_]ir.Value{.{
        .id = repeat_loop,
        .function = fixture.f_entry,
        .type = .boolean,
        .name_hint = "repeat_loop",
        .origin = .{ .parameter = 0 },
    }};
    values[fixture.v_callee.index()].name_hint = "producer";
    values[fixture.v_first.index()].name_hint = "materialized";
    const instructions = fixture.instructions ++ [_]ir.Instruction{
        observableGap(gap_id, fixture.b_entry, fixture.v_callee),
    };
    const loop_instructions = [_]ir.InstructionId{ fixture.i_get, fixture.i_call, gap_id, fixture.i_adjust };
    var blocks = fixture.blocks ++ [_]ir.Block{.{
        .id = exit_block,
        .function = fixture.f_entry,
        .terminator = .{ .return_values = &.{fixture.v_first} },
        .evidence = &fixture_evidence,
    }};
    blocks[fixture.b_entry.index()].instructions = &loop_instructions;
    blocks[fixture.b_entry.index()].terminator = .{ .branch = .{
        .condition = repeat_loop,
        .then_edge = .{ .target = fixture.b_entry },
        .else_edge = .{ .target = exit_block },
    } };
    const function_blocks = [_]ir.BlockId{ fixture.b_entry, exit_block };
    var functions = fixture.functions;
    functions[fixture.f_entry.index()].parameters = &.{repeat_loop};
    functions[fixture.f_entry.index()].blocks = &function_blocks;
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;

    var plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expectEqual(
        fixture.i_adjust,
        plan.role(fixture.i_call).materialized_invocation_producer,
    );
    try std.testing.expectEqual(
        fixture.i_call,
        plan.role(fixture.i_adjust).materialized_adjustment,
    );

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());
    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const declaration = std.mem.indexOf(u8, source, "local materialized") orelse return error.TestUnexpectedResult;
    const loop = std.mem.indexOf(u8, source, "while true do") orelse return error.TestUnexpectedResult;
    const assignment = std.mem.indexOf(u8, source, "materialized = producer()") orelse return error.TestUnexpectedResult;
    try std.testing.expect(declaration < loop and loop < assignment);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "producer()"));
}

test "cyclic materialization admits downstream closure aliases but refuses escape" {
    const parent_function = ir.FunctionId.fromIndex(0);
    const child_function = ir.FunctionId.fromIndex(1);
    const producer_block = ir.BlockId.fromIndex(0);
    const adjustment_block = ir.BlockId.fromIndex(1);
    const downstream_block = ir.BlockId.fromIndex(2);
    const child_block = ir.BlockId.fromIndex(3);
    const get_id = ir.InstructionId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(1);
    const adjustment_id = ir.InstructionId.fromIndex(2);
    const closure_id = ir.InstructionId.fromIndex(3);
    const store_id = ir.InstructionId.fromIndex(4);
    const second_call_id = ir.InstructionId.fromIndex(5);
    const callee = ir.ValueId.fromIndex(0);
    const adjusted = ir.ValueId.fromIndex(1);
    const closure = ir.ValueId.fromIndex(2);
    const captured = ir.ValueId.fromIndex(3);
    const protected_ok = ir.ValueId.fromIndex(4);
    const protected_value = ir.ValueId.fromIndex(5);
    const closure_alias = ir.ValueId.fromIndex(6);
    const closure_parameter = ir.ValueId.fromIndex(7);
    const route = ir.ValueId.fromIndex(8);
    const results_pack = ir.ValuePackId.fromIndex(0);
    const capture_id = ir.CaptureId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);
    const evidence_ids = [_]ir.EvidenceId{proof};
    const values = [_]ir.Value{
        .{ .id = callee, .function = parent_function, .type = .function, .origin = .{ .instruction_result = .{ .instruction = get_id, .index = 0 } } },
        .{ .id = adjusted, .function = parent_function, .name_hint = "adjusted", .origin = .{ .instruction_result = .{ .instruction = adjustment_id, .index = 0 } } },
        .{ .id = closure, .function = parent_function, .type = .function, .name_hint = "escaped", .origin = .{ .instruction_result = .{ .instruction = closure_id, .index = 0 } } },
        .{ .id = captured, .function = child_function, .name_hint = "captured", .origin = .{ .capture = capture_id } },
        .{ .id = protected_ok, .function = parent_function, .type = .boolean, .name_hint = "protected_ok", .origin = .{ .instruction_result = .{ .instruction = second_call_id, .index = 0 } } },
        .{ .id = protected_value, .function = parent_function, .name_hint = "protected_value", .origin = .{ .instruction_result = .{ .instruction = second_call_id, .index = 1 } } },
    };
    var extended_values = values ++ [_]ir.Value{
        .{
            .id = closure_alias,
            .function = parent_function,
            .type = .function,
            .name_hint = "closure_alias",
            .origin = .{ .instruction_result = .{ .instruction = store_id, .index = 0 } },
        },
        .{
            .id = closure_parameter,
            .function = parent_function,
            .type = .function,
            .name_hint = "closure_parameter",
            .origin = .{ .block_parameter = .{ .block = downstream_block, .index = 0 } },
        },
        .{
            .id = route,
            .function = parent_function,
            .type = .boolean,
            .name_hint = "route",
            .origin = .{ .parameter = 0 },
        },
    };
    const packs = [_]ir.ValuePack{.{
        .id = results_pack,
        .function = parent_function,
        .origin = .{ .instruction_result = call_id },
        .evidence = &evidence_ids,
    }};
    const captures = [_]ir.Capture{.{
        .id = capture_id,
        .function = child_function,
        .kind = .{ .immutable_value = captured },
        .evidence = &evidence_ids,
    }};
    var instructions = [_]ir.Instruction{
        .{ .id = get_id, .block = producer_block, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "produce" } }, .results = &.{callee}, .effects = .semantic_environment_read, .evidence = &evidence_ids },
        .{ .id = call_id, .block = producer_block, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .variadic = {} } } }, .results = &.{}, .pack_result = results_pack, .effects = .dynamic_call, .evidence = &evidence_ids },
        .{ .id = adjustment_id, .block = adjustment_block, .operation = .{ .adjust_pack = results_pack }, .results = &.{adjusted}, .effects = .pure, .evidence = &evidence_ids },
        .{ .id = closure_id, .block = adjustment_block, .operation = .{ .make_closure = .{ .function = child_function, .bindings = &.{.{ .value = adjusted }} } }, .results = &.{closure}, .effects = .pure, .evidence = &evidence_ids },
        .{ .id = store_id, .block = downstream_block, .operation = .{ .environment_set = .{ .target = .{ .ambient = {} }, .name = "escaped", .value = closure } }, .results = &.{}, .effects = .semantic_environment_write, .evidence = &evidence_ids },
        .{ .id = second_call_id, .block = downstream_block, .operation = .{ .protected_call = .{ .callee = closure, .arguments = &.{}, .result_arity = .{ .fixed = 2 } } }, .results = &.{ protected_ok, protected_value }, .effects = .protected_invocation, .evidence = &evidence_ids },
    };
    const blocks = [_]ir.Block{
        .{ .id = producer_block, .function = parent_function, .instructions = &.{ get_id, call_id }, .terminator = .{ .jump = .{ .target = adjustment_block } }, .evidence = &evidence_ids },
        .{ .id = adjustment_block, .function = parent_function, .instructions = &.{ adjustment_id, closure_id }, .terminator = .{ .jump = .{ .target = downstream_block } }, .evidence = &evidence_ids },
        .{ .id = downstream_block, .function = parent_function, .instructions = &.{ store_id, second_call_id }, .terminator = .{ .jump = .{ .target = producer_block } }, .evidence = &evidence_ids },
        .{ .id = child_block, .function = child_function, .terminator = .{ .return_values = &.{captured} }, .evidence = &evidence_ids },
    };
    const functions = [_]ir.Function{
        .{ .id = parent_function, .name_hint = "chunk", .blocks = &.{ producer_block, adjustment_block, downstream_block }, .entry_block = producer_block, .evidence = &evidence_ids },
        .{ .id = child_function, .name_hint = "capture", .lexical_parent = parent_function, .captures = &.{capture_id}, .blocks = &.{child_block}, .entry_block = child_block, .evidence = &evidence_ids },
    };
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:cyclic-pack-closure-refusal" }};
    var program: ir.Program = .{
        .program_id = "cyclic-pack-closure-refusal",
        .entry_function = parent_function,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
        .captures = &captures,
        .evidence = &evidence,
    };

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expect(plan.role(call_id) == .ordinary);
    try std.testing.expect(plan.role(adjustment_id) == .ordinary);
    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expectEqual(@as(usize, 2), readable_report.diagnostics.items.len);
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&readable_report, .variadic_result_arity));
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&readable_report, .unsupported_readable_pack_operation));

    instructions[store_id.index()].operation = .{ .call = .{
        .callee = closure,
        .arguments = &.{},
        .result_arity = .{ .fixed = 0 },
    } };
    instructions[store_id.index()].effects = .dynamic_call;
    var direct_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer direct_plan.deinit();
    try std.testing.expectEqual(adjustment_id, direct_plan.role(call_id).materialized_invocation_producer);
    try std.testing.expectEqual(call_id, direct_plan.role(adjustment_id).materialized_adjustment);
    var direct_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer direct_report.deinit();
    try std.testing.expect(direct_report.isClean());
    const direct_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(direct_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, direct_source, "produce()"));
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, direct_source, "escaped()"));
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, direct_source, "__lifter_pcall(escaped)"));

    instructions[store_id.index()].operation = .{ .copy = closure };
    instructions[store_id.index()].results = &.{closure_alias};
    instructions[store_id.index()].effects = .pure;
    instructions[second_call_id.index()].operation.protected_call.callee = closure_alias;
    program.values = extended_values[0..7];
    var alias_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer alias_core_report.deinit();
    try std.testing.expect(alias_core_report.isClean());
    var alias_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer alias_plan.deinit();
    try std.testing.expectEqual(adjustment_id, alias_plan.role(call_id).materialized_invocation_producer);
    try std.testing.expectEqual(call_id, alias_plan.role(adjustment_id).materialized_adjustment);
    var alias_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer alias_report.deinit();
    try std.testing.expect(alias_report.isClean());
    const alias_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(alias_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, alias_source, "produce()"));
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, alias_source, "__lifter_pcall(escaped)"));
    try std.testing.expect(std.mem.indexOf(u8, alias_source, "closure_alias") == null);

    var transfer_instructions = instructions;
    transfer_instructions[store_id.index()].block = adjustment_block;
    transfer_instructions[second_call_id.index()].operation.protected_call.callee = closure_parameter;
    var transfer_blocks = blocks;
    transfer_blocks[adjustment_block.index()].instructions = &.{ adjustment_id, closure_id, store_id };
    transfer_blocks[adjustment_block.index()].terminator = .{ .jump = .{
        .target = downstream_block,
        .arguments = &.{closure_alias},
    } };
    transfer_blocks[downstream_block.index()].parameters = &.{closure_parameter};
    transfer_blocks[downstream_block.index()].instructions = &.{second_call_id};
    var transfer_program = program;
    transfer_program.blocks = &transfer_blocks;
    transfer_program.instructions = &transfer_instructions;
    transfer_program.values = extended_values[0..8];
    var transfer_core_report = try validation.validate(std.testing.allocator, &transfer_program, .core);
    defer transfer_core_report.deinit();
    try std.testing.expect(transfer_core_report.isClean());
    var transfer_plan = try pack_plan.Plan.init(std.testing.allocator, &transfer_program);
    defer transfer_plan.deinit();
    try std.testing.expectEqual(adjustment_id, transfer_plan.role(call_id).materialized_invocation_producer);
    try std.testing.expectEqual(call_id, transfer_plan.role(adjustment_id).materialized_adjustment);
    var transfer_report = try validation.validate(std.testing.allocator, &transfer_program, .readable_luau);
    defer transfer_report.deinit();
    try std.testing.expect(transfer_report.isClean());
    const transfer_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &transfer_program);
    defer std.testing.allocator.free(transfer_source);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, transfer_source, "produce()"));
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, transfer_source, "__lifter_pcall(escaped)"));
    try std.testing.expect(std.mem.indexOf(u8, transfer_source, "closure_alias") == null);
    try std.testing.expect(std.mem.indexOf(u8, transfer_source, "closure_parameter") == null);

    var merge_blocks = transfer_blocks;
    merge_blocks[producer_block.index()].terminator = .{ .branch = .{
        .condition = route,
        .then_edge = .{ .target = adjustment_block },
        .else_edge = .{ .target = downstream_block, .arguments = &.{callee} },
    } };
    var routed_functions = functions;
    routed_functions[parent_function.index()].parameters = &.{route};
    var merge_program = transfer_program;
    merge_program.functions = &routed_functions;
    merge_program.blocks = &merge_blocks;
    merge_program.values = &extended_values;
    var merge_core_report = try validation.validate(std.testing.allocator, &merge_program, .core);
    defer merge_core_report.deinit();
    try std.testing.expect(merge_core_report.isClean());
    var merge_plan = try pack_plan.Plan.init(std.testing.allocator, &merge_program);
    defer merge_plan.deinit();
    try std.testing.expect(merge_plan.role(call_id) == .ordinary);
    try std.testing.expect(merge_plan.role(adjustment_id) == .ordinary);

    var self_blocks = transfer_blocks;
    self_blocks[downstream_block.index()].terminator = .{ .branch = .{
        .condition = route,
        .then_edge = .{ .target = downstream_block, .arguments = &.{closure_parameter} },
        .else_edge = .{ .target = producer_block },
    } };
    var self_program = transfer_program;
    self_program.functions = &routed_functions;
    self_program.blocks = &self_blocks;
    self_program.values = &extended_values;
    var self_core_report = try validation.validate(std.testing.allocator, &self_program, .core);
    defer self_core_report.deinit();
    try std.testing.expect(self_core_report.isClean());
    var self_plan = try pack_plan.Plan.init(std.testing.allocator, &self_program);
    defer self_plan.deinit();
    try std.testing.expect(self_plan.role(call_id) == .ordinary);
    try std.testing.expect(self_plan.role(adjustment_id) == .ordinary);

    extended_values[closure_parameter.index()].origin.block_parameter.index = 1;
    var parameter_plan = try pack_plan.Plan.init(std.testing.allocator, &transfer_program);
    defer parameter_plan.deinit();
    try std.testing.expect(parameter_plan.role(call_id) == .ordinary);
    try std.testing.expect(parameter_plan.role(adjustment_id) == .ordinary);
    extended_values[closure_parameter.index()].origin.block_parameter.index = 0;

    instructions[store_id.index()].effects = .dynamic_call;
    var effect_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer effect_plan.deinit();
    try std.testing.expect(effect_plan.role(call_id) == .ordinary);
    try std.testing.expect(effect_plan.role(adjustment_id) == .ordinary);
    var effect_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer effect_report.deinit();
    try std.testing.expectEqual(@as(usize, 2), effect_report.diagnostics.items.len);
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&effect_report, .variadic_result_arity));
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&effect_report, .unsupported_readable_pack_operation));

    instructions[store_id.index()].effects = .pure;
    extended_values[closure_alias.index()].origin.instruction_result.index = 1;
    var provenance_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer provenance_plan.deinit();
    try std.testing.expect(provenance_plan.role(call_id) == .ordinary);
    try std.testing.expect(provenance_plan.role(adjustment_id) == .ordinary);

    extended_values[closure_alias.index()].origin.instruction_result.index = 0;
    instructions[second_call_id.index()].operation.protected_call.error_handler = closure;
    var alias_handler_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer alias_handler_plan.deinit();
    try std.testing.expectEqual(adjustment_id, alias_handler_plan.role(call_id).materialized_invocation_producer);
    try std.testing.expectEqual(call_id, alias_handler_plan.role(adjustment_id).materialized_adjustment);
    var alias_handler_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer alias_handler_report.deinit();
    try std.testing.expect(alias_handler_report.isClean());
    const alias_handler_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(alias_handler_source);
    try std.testing.expect(std.mem.indexOf(u8, alias_handler_source, "__lifter_xpcall(escaped, escaped)") != null);

    instructions[store_id.index()].operation = .{ .call = .{
        .callee = closure,
        .arguments = &.{},
        .result_arity = .{ .fixed = 0 },
    } };
    instructions[store_id.index()].results = &.{};
    instructions[store_id.index()].effects = .dynamic_call;
    instructions[second_call_id.index()].operation.protected_call.callee = closure;
    instructions[second_call_id.index()].operation.protected_call.error_handler = null;
    program.values = &values;

    instructions[store_id.index()].operation.call.arguments = &.{closure};
    var argument_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer argument_plan.deinit();
    try std.testing.expect(argument_plan.role(call_id) == .ordinary);
    try std.testing.expect(argument_plan.role(adjustment_id) == .ordinary);
    var argument_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer argument_report.deinit();
    try std.testing.expectEqual(@as(usize, 2), argument_report.diagnostics.items.len);
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&argument_report, .variadic_result_arity));
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&argument_report, .unsupported_readable_pack_operation));

    instructions[store_id.index()].operation.call.arguments = &.{};
    instructions[second_call_id.index()].operation.protected_call.callee = callee;
    instructions[second_call_id.index()].operation.protected_call.error_handler = closure;
    var handler_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer handler_plan.deinit();
    try std.testing.expectEqual(adjustment_id, handler_plan.role(call_id).materialized_invocation_producer);
    try std.testing.expectEqual(call_id, handler_plan.role(adjustment_id).materialized_adjustment);
    var handler_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer handler_report.deinit();
    try std.testing.expect(handler_report.isClean());
    const handler_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(handler_source);
    try std.testing.expect(std.mem.indexOf(u8, handler_source, "__lifter_xpcall(") != null);
    try std.testing.expect(std.mem.indexOf(u8, handler_source, ", escaped)") != null);

    instructions[second_call_id.index()].operation.protected_call.callee = closure;
    var dual_role_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer dual_role_plan.deinit();
    try std.testing.expectEqual(adjustment_id, dual_role_plan.role(call_id).materialized_invocation_producer);
    try std.testing.expectEqual(call_id, dual_role_plan.role(adjustment_id).materialized_adjustment);
    var dual_role_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer dual_role_report.deinit();
    try std.testing.expect(dual_role_report.isClean());

    const protected_pack = ir.ValuePackId.fromIndex(1);
    const boolean_prefix = [_]ir.ValueType{.boolean};
    const open_packs = packs ++ [_]ir.ValuePack{.{
        .id = protected_pack,
        .function = parent_function,
        .origin = .{ .instruction_result = second_call_id },
        .shape = .{ .prefix = &boolean_prefix, .tail = .open },
        .evidence = &evidence_ids,
    }};
    instructions[second_call_id.index()].operation.protected_call.callee = closure;
    instructions[second_call_id.index()].operation.protected_call.error_handler = null;
    instructions[second_call_id.index()].operation.protected_call.result_arity = .{ .variadic = {} };
    instructions[second_call_id.index()].results = &.{};
    instructions[second_call_id.index()].pack_result = protected_pack;
    program.values = values[0..4];
    program.value_packs = &open_packs;
    var open_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer open_core_report.deinit();
    try std.testing.expect(open_core_report.isClean());
    var open_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer open_plan.deinit();
    try std.testing.expect(open_plan.role(call_id) == .ordinary);
    try std.testing.expect(open_plan.role(adjustment_id) == .ordinary);
    try std.testing.expect(open_plan.role(second_call_id) == .ordinary);
    var open_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer open_report.deinit();
    try std.testing.expectEqual(@as(usize, 3), open_report.diagnostics.items.len);
    try std.testing.expectEqual(@as(usize, 2), diagnosticCount(&open_report, .variadic_result_arity));
    try std.testing.expectEqual(@as(usize, 1), diagnosticCount(&open_report, .unsupported_readable_pack_operation));

    const open_adjust_id = ir.InstructionId.fromIndex(instructions.len);
    var open_instructions: [instructions.len + 1]ir.Instruction = undefined;
    @memcpy(open_instructions[0..instructions.len], instructions[0..]);
    open_instructions[open_adjust_id.index()] = .{
        .id = open_adjust_id,
        .block = downstream_block,
        .operation = .{ .adjust_pack = protected_pack },
        .results = &.{ protected_ok, protected_value },
        .effects = .pure,
        .evidence = &evidence_ids,
    };
    var open_values = values;
    open_values[protected_ok.index()].origin = .{ .instruction_result = .{ .instruction = open_adjust_id, .index = 0 } };
    open_values[protected_value.index()].origin = .{ .instruction_result = .{ .instruction = open_adjust_id, .index = 1 } };
    var open_blocks = blocks;
    open_blocks[downstream_block.index()].instructions = &.{ store_id, second_call_id, open_adjust_id };
    var fused_open_program = program;
    fused_open_program.blocks = &open_blocks;
    fused_open_program.instructions = &open_instructions;
    fused_open_program.values = &open_values;

    open_instructions[second_call_id.index()].operation.protected_call.callee = callee;
    open_instructions[second_call_id.index()].operation.protected_call.error_handler = closure;
    var open_handler_core_report = try validation.validate(std.testing.allocator, &fused_open_program, .core);
    defer open_handler_core_report.deinit();
    try std.testing.expect(open_handler_core_report.isClean());
    var open_handler_plan = try pack_plan.Plan.init(std.testing.allocator, &fused_open_program);
    defer open_handler_plan.deinit();
    try std.testing.expectEqual(adjustment_id, open_handler_plan.role(call_id).materialized_invocation_producer);
    try std.testing.expectEqual(open_adjust_id, open_handler_plan.role(second_call_id).fused_invocation_producer);
    try std.testing.expectEqual(second_call_id, open_handler_plan.role(open_adjust_id).fused_adjustment);
    var open_handler_report = try validation.validate(std.testing.allocator, &fused_open_program, .readable_luau);
    defer open_handler_report.deinit();
    try std.testing.expect(open_handler_report.isClean());
    open_instructions[second_call_id.index()].operation = .{ .call = .{
        .callee = closure,
        .arguments = &.{},
        .result_arity = .{ .variadic = {} },
    } };
    open_instructions[second_call_id.index()].effects = .dynamic_call;
    var ordinary_open_plan = try pack_plan.Plan.init(std.testing.allocator, &fused_open_program);
    defer ordinary_open_plan.deinit();
    try std.testing.expectEqual(adjustment_id, ordinary_open_plan.role(call_id).materialized_invocation_producer);
    try std.testing.expectEqual(open_adjust_id, ordinary_open_plan.role(second_call_id).fused_invocation_producer);
    var ordinary_open_report = try validation.validate(std.testing.allocator, &fused_open_program, .readable_luau);
    defer ordinary_open_report.deinit();
    try std.testing.expect(ordinary_open_report.isClean());
}

test "pack materialization admits branch merges with producer reentry" {
    const fixture = fixtures.open_pack_adjust_module;
    const then_block = ir.BlockId.fromIndex(1);
    const else_block = ir.BlockId.fromIndex(2);
    const join_block = ir.BlockId.fromIndex(3);
    const gap_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const condition_id = ir.InstructionId.fromIndex(fixture.instructions.len + 1);
    const condition = ir.ValueId.fromIndex(fixture.values.len);

    var values = fixture.values ++ [_]ir.Value{.{
        .id = condition,
        .function = fixture.f_entry,
        .type = .boolean,
        .origin = .{ .instruction_result = .{ .instruction = condition_id, .index = 0 } },
    }};
    values[fixture.v_callee.index()].name_hint = "producer";
    values[fixture.v_first.index()].name_hint = "materialized";
    var instructions = fixture.instructions ++ [_]ir.Instruction{
        observableGap(gap_id, fixture.b_entry, fixture.v_callee),
        .{
            .id = condition_id,
            .block = fixture.b_entry,
            .operation = .{ .constant = .{ .boolean = true } },
            .results = &.{condition},
            .effects = .pure,
            .evidence = &fixture_evidence,
        },
    };
    instructions[fixture.i_adjust.index()].block = join_block;
    const entry_instructions = [_]ir.InstructionId{ fixture.i_get, condition_id, fixture.i_call, gap_id };
    const join_instructions = [_]ir.InstructionId{fixture.i_adjust};
    var blocks = [_]ir.Block{
        .{
            .id = fixture.b_entry,
            .function = fixture.f_entry,
            .instructions = &entry_instructions,
            .terminator = .{ .branch = .{
                .condition = condition,
                .then_edge = .{ .target = then_block },
                .else_edge = .{ .target = else_block },
            } },
            .evidence = &fixture_evidence,
        },
        .{ .id = then_block, .function = fixture.f_entry, .terminator = .{ .jump = .{ .target = join_block } }, .evidence = &fixture_evidence },
        .{ .id = else_block, .function = fixture.f_entry, .terminator = .{ .jump = .{ .target = join_block } }, .evidence = &fixture_evidence },
        .{
            .id = join_block,
            .function = fixture.f_entry,
            .instructions = &join_instructions,
            .terminator = .{ .return_values = &.{fixture.v_first} },
            .evidence = &fixture_evidence,
        },
    };
    const function_blocks = [_]ir.BlockId{ fixture.b_entry, then_block, else_block, join_block };
    var functions = fixture.functions;
    functions[fixture.f_entry.index()].blocks = &function_blocks;
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());
    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const producer_offset = std.mem.indexOf(u8, source, "local materialized = producer()") orelse return error.TestUnexpectedResult;
    const gap_offset = std.mem.indexOf(u8, source, "observed = producer") orelse return error.TestUnexpectedResult;
    const return_offset = std.mem.indexOf(u8, source, "return materialized") orelse return error.TestUnexpectedResult;
    try std.testing.expect(producer_offset < gap_offset and gap_offset < return_offset);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "producer()"));

    blocks[join_block.index()].terminator = .{ .jump = .{ .target = fixture.b_entry } };
    var cyclic_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer cyclic_core_report.deinit();
    try std.testing.expect(cyclic_core_report.isClean());
    var cyclic_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer cyclic_report.deinit();
    try std.testing.expect(cyclic_report.isClean());
    const cyclic_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(cyclic_source);
    try std.testing.expect(std.mem.indexOf(u8, cyclic_source, "while true do") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, cyclic_source, "producer()"));
}

test "multiple fixed adjustments materialize across dominated branch arms" {
    const fixture = fixtures.open_pack_adjust_module;
    const then_block = ir.BlockId.fromIndex(fixture.blocks.len);
    const else_block = ir.BlockId.fromIndex(fixture.blocks.len + 1);
    const wide_id = ir.InstructionId.fromIndex(fixture.instructions.len);
    const selector = ir.ValueId.fromIndex(fixture.values.len);
    const wide_first = ir.ValueId.fromIndex(fixture.values.len + 1);
    const wide_second = ir.ValueId.fromIndex(fixture.values.len + 2);

    var values = fixture.values ++ [_]ir.Value{
        .{ .id = selector, .function = fixture.f_entry, .type = .boolean, .name_hint = "selector", .origin = .{ .parameter = 0 } },
        .{ .id = wide_first, .function = fixture.f_entry, .name_hint = "wide_first", .origin = .{ .instruction_result = .{ .instruction = wide_id, .index = 0 } } },
        .{ .id = wide_second, .function = fixture.f_entry, .name_hint = "wide_second", .origin = .{ .instruction_result = .{ .instruction = wide_id, .index = 1 } } },
    };
    values[fixture.v_callee.index()].name_hint = "producer";
    values[fixture.v_first.index()].name_hint = "narrow";
    var instructions = fixture.instructions ++ [_]ir.Instruction{.{
        .id = wide_id,
        .block = else_block,
        .operation = .{ .adjust_pack = fixture.p_results },
        .results = &.{ wide_first, wide_second },
        .effects = .pure,
        .evidence = &fixture_evidence,
    }};
    instructions[fixture.i_adjust.index()].block = then_block;
    const entry_instructions = [_]ir.InstructionId{ fixture.i_get, fixture.i_call };
    const then_instructions = [_]ir.InstructionId{fixture.i_adjust};
    const else_instructions = [_]ir.InstructionId{wide_id};
    var blocks = [_]ir.Block{
        .{
            .id = fixture.b_entry,
            .function = fixture.f_entry,
            .instructions = &entry_instructions,
            .terminator = .{ .branch = .{
                .condition = selector,
                .then_edge = .{ .target = then_block },
                .else_edge = .{ .target = else_block },
            } },
            .evidence = &fixture_evidence,
        },
        .{
            .id = then_block,
            .function = fixture.f_entry,
            .instructions = &then_instructions,
            .terminator = .{ .return_values = &.{fixture.v_first} },
            .evidence = &fixture_evidence,
        },
        .{
            .id = else_block,
            .function = fixture.f_entry,
            .instructions = &else_instructions,
            .terminator = .{ .return_values = &.{ wide_first, wide_second } },
            .evidence = &fixture_evidence,
        },
    };
    const function_blocks = [_]ir.BlockId{ fixture.b_entry, then_block, else_block };
    var functions = fixture.functions;
    functions[fixture.f_entry.index()].parameters = &.{selector};
    functions[fixture.f_entry.index()].blocks = &function_blocks;
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;

    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());
    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.indexOf(u8, source, "local wide_first, wide_second = produce()") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "local narrow = wide_first") != null);
    try std.testing.expect(std.mem.indexOf(u8, source, "return wide_first, wide_second") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "produce()"));

    blocks[then_block.index()].terminator = .{ .jump = .{ .target = fixture.b_entry } };
    var cyclic_core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer cyclic_core_report.deinit();
    try std.testing.expect(cyclic_core_report.isClean());
    var cyclic_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer cyclic_report.deinit();
    try std.testing.expect(cyclic_report.isClean());
    const cyclic_source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(cyclic_source);
    try std.testing.expect(std.mem.indexOf(u8, cyclic_source, "while true do") != null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, cyclic_source, "produce()"));
}

test "canonical pack prefixes hoist for copies across long-block emission segments" {
    const fixture = fixtures.open_pack_adjust_module;
    const gap_count = 33;
    const secondary_id = ir.InstructionId.fromIndex(fixture.instructions.len + gap_count);
    const repeated = ir.ValueId.fromIndex(fixture.values.len);
    const instructions = try std.testing.allocator.alloc(ir.Instruction, fixture.instructions.len + gap_count + 1);
    defer std.testing.allocator.free(instructions);
    @memcpy(instructions[0..fixture.instructions.len], fixture.instructions[0..]);
    for (0..gap_count) |index| {
        const gap_id = ir.InstructionId.fromIndex(fixture.instructions.len + index);
        instructions[gap_id.index()] = observableGap(gap_id, fixture.b_entry, fixture.v_callee);
    }
    instructions[secondary_id.index()] = .{
        .id = secondary_id,
        .block = fixture.b_entry,
        .operation = .{ .adjust_pack = fixture.p_results },
        .results = &.{repeated},
        .effects = .pure,
        .evidence = &fixture_evidence,
    };

    const instruction_ids = try std.testing.allocator.alloc(ir.InstructionId, fixture.instructions.len + gap_count + 1);
    defer std.testing.allocator.free(instruction_ids);
    instruction_ids[0] = fixture.i_get;
    instruction_ids[1] = fixture.i_call;
    instruction_ids[2] = fixture.i_adjust;
    for (0..gap_count) |index| instruction_ids[3 + index] = ir.InstructionId.fromIndex(fixture.instructions.len + index);
    instruction_ids[instruction_ids.len - 1] = secondary_id;

    var blocks = fixture.blocks;
    blocks[fixture.b_entry.index()].instructions = instruction_ids;
    blocks[fixture.b_entry.index()].terminator = .{ .return_values = &.{repeated} };
    var values = fixture.values ++ [_]ir.Value{.{
        .id = repeated,
        .function = fixture.f_entry,
        .name_hint = "repeated",
        .origin = .{ .instruction_result = .{ .instruction = secondary_id, .index = 0 } },
    }};
    values[fixture.v_callee.index()].name_hint = "producer";
    values[fixture.v_first.index()].name_hint = "canonical";
    var program = fixture.program;
    program.blocks = &blocks;
    program.instructions = instructions;
    program.values = &values;

    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const declaration_offset = std.mem.indexOf(u8, source, "canonical") orelse return error.TestUnexpectedResult;
    const assignment_offset = std.mem.indexOf(u8, source, "canonical = producer()") orelse return error.TestUnexpectedResult;
    const copy_offset = std.mem.indexOf(u8, source, "repeated = canonical") orelse return error.TestUnexpectedResult;
    try std.testing.expect(declaration_offset < assignment_offset and assignment_offset < copy_offset);
    try std.testing.expect(std.mem.indexOf(u8, source, "local canonical = producer()") == null);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "producer()"));
    try std.testing.expectEqual(gap_count, std.mem.count(u8, source, "observed = producer"));
}

test "readable invocation admission enforces the hard Luau result ceiling" {
    const allocator = std.testing.allocator;
    const boundary_count = 200;
    const excessive_count = boundary_count + 1;
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const get_id = ir.InstructionId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(1);
    const callee_id = ir.ValueId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);
    const evidence_ids = [_]ir.EvidenceId{proof};

    const values = try allocator.alloc(ir.Value, excessive_count + 1);
    defer allocator.free(values);
    const result_ids = try allocator.alloc(ir.ValueId, excessive_count);
    defer allocator.free(result_ids);
    values[0] = .{
        .id = callee_id,
        .function = function_id,
        .type = .function,
        .name_hint = "produce",
        .origin = .{ .instruction_result = .{ .instruction = get_id, .index = 0 } },
    };
    for (result_ids, 0..) |*result_id, index| {
        result_id.* = ir.ValueId.fromIndex(index + 1);
        values[index + 1] = .{
            .id = result_id.*,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = call_id, .index = @intCast(index) } },
        };
    }

    var instructions = [_]ir.Instruction{
        .{
            .id = get_id,
            .block = block_id,
            .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "produce" } },
            .results = &.{callee_id},
            .effects = .semantic_environment_read,
            .evidence = &evidence_ids,
        },
        .{
            .id = call_id,
            .block = block_id,
            .operation = .{ .call = .{
                .callee = callee_id,
                .arguments = &.{},
                .result_arity = .{ .fixed = boundary_count },
            } },
            .results = result_ids[0..boundary_count],
            .effects = .dynamic_call,
            .evidence = &evidence_ids,
        },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ get_id, call_id },
        .terminator = .{ .return_values = result_ids[0..boundary_count] },
        .evidence = &evidence_ids,
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &evidence_ids,
    }};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:readable-invocation-result-limit",
    }};
    var program: ir.Program = .{
        .program_id = "readable-invocation-result-limit",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = values[0 .. boundary_count + 1],
        .evidence = &evidence,
    };

    var boundary_report = try validation.validateForTarget(
        allocator,
        &program,
        .readable_luau,
        .direct_locals_luau,
    );
    defer boundary_report.deinit();
    try std.testing.expect(boundary_report.isClean());
    const boundary_source = try emit_luau.emitAllocForTarget(allocator, &program, .direct_locals_luau);
    defer allocator.free(boundary_source);
    const repeated_source = try emit_luau.emitAllocForTarget(allocator, &program, .direct_locals_luau);
    defer allocator.free(repeated_source);
    try std.testing.expectEqualStrings(boundary_source, repeated_source);

    instructions[call_id.index()].operation = .{ .protected_call = .{
        .callee = callee_id,
        .arguments = &.{},
        .result_arity = .{ .fixed = boundary_count },
    } };
    instructions[call_id.index()].effects = .protected_invocation;
    values[1].type = .boolean;
    var contextual_report = try validation.validateForTarget(
        allocator,
        &program,
        .readable_luau,
        .direct_locals_luau,
    );
    defer contextual_report.deinit();
    try std.testing.expectEqual(@as(usize, 1), contextual_report.diagnostics.items.len);
    try std.testing.expect(contextual_report.contains(.unsupported_readable_register_pressure));
    try std.testing.expectError(
        error.InvalidIr,
        emit_luau.emitAllocForTarget(allocator, &program, .direct_locals_luau),
    );

    instructions[call_id.index()].operation = .{ .call = .{
        .callee = callee_id,
        .arguments = &.{},
        .result_arity = .{ .fixed = excessive_count },
    } };
    instructions[call_id.index()].effects = .dynamic_call;
    values[1].type = .dynamic;

    instructions[call_id.index()].results = result_ids;
    program.values = values;
    var core_report = try validation.validate(allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var excessive_report = try validation.validateForTarget(
        allocator,
        &program,
        .readable_luau,
        .direct_locals_luau,
    );
    defer excessive_report.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive_report.diagnostics.items.len);
    try std.testing.expect(excessive_report.contains(.unsupported_readable_result_arity));
    try std.testing.expectError(
        error.InvalidIr,
        emit_luau.emitAllocForTarget(allocator, &program, .direct_locals_luau),
    );
}
