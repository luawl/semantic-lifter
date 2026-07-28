const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const structure = @import("structure.zig");
const diagnostics = @import("diagnostics.zig");
const lexical_transfer = @import("lexical_transfer.zig");

pub fn validateFunction(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    plan: *const structure.Plan,
) !void {
    var transfers = try lexical_transfer.Plan.init(allocator, program, analysis.function, analysis, plan);
    defer transfers.deinit();
    for (transfers.unsupported_values) |value_id| {
        try report.add(.loop_local_value_requires_transfer, value_id.index());
    }
}

test "ordinary loop-local direct escape has a backend lexical transfer" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const exit_block = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const escaped = ir.ValueId.fromIndex(1);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = escaped, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = body,
        .operation = .{ .constant = .{ .integer = "7" } },
        .results = &.{escaped},
        .effects = .pure,
    }};
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = body } } },
        .{ .id = body, .function = function_id, .instructions = &.{instruction_id}, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = exit_block },
            .else_edge = .{ .target = header },
        } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{escaped} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ exit_block, body, entry, header },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "loop-local-direct-escape",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var plan = try structure.Plan.init(std.testing.allocator, &analysis);
    defer plan.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &plan);
    try std.testing.expect(!report.contains(.loop_local_value_requires_transfer));

    var protocol_instructions = instructions;
    protocol_instructions[0].operation = .{ .numeric_for_next = .{
        .control = condition,
        .limit = condition,
        .step = condition,
        .initial = condition,
    } };
    var protocol_program = program;
    protocol_program.instructions = &protocol_instructions;
    var protocol_report = diagnostics.Report.init(std.testing.allocator);
    defer protocol_report.deinit();
    try validateFunction(std.testing.allocator, &protocol_report, &protocol_program, &analysis, &plan);
    try std.testing.expect(protocol_report.contains(.loop_local_value_requires_transfer));

    const has_value = ir.ValueId.fromIndex(2);
    const normalized_limit = ir.ValueId.fromIndex(3);
    const normalized_step = ir.ValueId.fromIndex(4);
    const semantic_values = [_]ir.Value{
        values[0],
        .{ .id = escaped, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 2 } } },
    };
    var semantic_instructions = instructions;
    semantic_instructions[0].operation = .{ .numeric_for_next = .{
        .control = condition,
        .limit = condition,
        .step = condition,
        .initial = condition,
        .mode = .semantic_normalized,
    } };
    semantic_instructions[0].results = &.{ has_value, normalized_limit, normalized_step, escaped };
    var semantic_program = program;
    semantic_program.program_id = "standalone-semantic-numeric-transfer";
    semantic_program.instructions = &semantic_instructions;
    semantic_program.values = &semantic_values;

    var semantic_report = diagnostics.Report.init(std.testing.allocator);
    defer semantic_report.deinit();
    try validateFunction(std.testing.allocator, &semantic_report, &semantic_program, &analysis, &plan);
    try std.testing.expect(!semantic_report.contains(.loop_local_value_requires_transfer));

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const prepared = try lexical_transfer.prepareInArena(arena.allocator(), &semantic_program);
    try std.testing.expectEqual(@as(usize, 1), prepared.places.len);
    try std.testing.expectEqual(@as(usize, 3), prepared.instructions.len);
    const transfer_write = prepared.instructions[prepared.blocks[body.index()].instructions[1].index()];
    try std.testing.expect(transfer_write.operation == .place_write);
    try std.testing.expectEqual(escaped, transfer_write.operation.place_write.value);
    const transfer_read = prepared.instructions[prepared.blocks[exit_block.index()].instructions[0].index()];
    try std.testing.expect(transfer_read.operation == .place_read);
    try std.testing.expectEqual(transfer_read.results[0], prepared.blocks[exit_block.index()].terminator.return_values[0]);
}

test "loop-body parameter transfer writes at entry and rewrites outside uses" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const exit_block = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const initial = ir.ValueId.fromIndex(1);
    const escaped = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = initial, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = escaped, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = body, .index = 0 } } },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .terminator = .{ .jump = .{ .target = body, .arguments = &.{initial} } } },
        .{ .id = body, .function = function_id, .parameters = &.{escaped}, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = exit_block },
            .else_edge = .{ .target = header },
        } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{escaped} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ condition, initial },
        .blocks = &.{ entry, header, body, exit_block },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "loop-body-parameter-transfer",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var structured = try structure.Plan.init(std.testing.allocator, &analysis);
    defer structured.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    defer report.deinit();
    try validateFunction(std.testing.allocator, &report, &program, &analysis, &structured);
    try std.testing.expect(!report.contains(.loop_local_value_requires_transfer));

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const prepared = try lexical_transfer.prepareInArena(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 1), prepared.places.len);
    try std.testing.expectEqual(@as(usize, 2), prepared.instructions.len);
    const write = prepared.instructions[prepared.blocks[body.index()].instructions[0].index()];
    try std.testing.expect(write.operation == .place_write);
    try std.testing.expectEqual(escaped, write.operation.place_write.value);
    const read = prepared.instructions[prepared.blocks[exit_block.index()].instructions[0].index()];
    try std.testing.expect(read.operation == .place_read);
    const returned = prepared.blocks[exit_block.index()].terminator.return_values;
    try std.testing.expectEqual(read.results[0], returned[0]);
}

test "numeric normalized state escapes through emission-only aliases" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const exit_block = ir.BlockId.fromIndex(3);
    const i_true = ir.InstructionId.fromIndex(0);
    const i_false = ir.InstructionId.fromIndex(1);
    const i_next = ir.InstructionId.fromIndex(2);
    const control = ir.ValueId.fromIndex(0);
    const limit = ir.ValueId.fromIndex(1);
    const step = ir.ValueId.fromIndex(2);
    const first = ir.ValueId.fromIndex(3);
    const later = ir.ValueId.fromIndex(4);
    const header_control = ir.ValueId.fromIndex(5);
    const header_limit = ir.ValueId.fromIndex(6);
    const header_step = ir.ValueId.fromIndex(7);
    const header_initial = ir.ValueId.fromIndex(8);
    const has_value = ir.ValueId.fromIndex(9);
    const normalized_limit = ir.ValueId.fromIndex(10);
    const normalized_step = ir.ValueId.fromIndex(11);
    const index = ir.ValueId.fromIndex(12);
    const body_index = ir.ValueId.fromIndex(13);
    const values = [_]ir.Value{
        .{ .id = control, .function = function_id, .type = .number, .origin = .{ .parameter = 0 } },
        .{ .id = limit, .function = function_id, .type = .number, .origin = .{ .parameter = 1 } },
        .{ .id = step, .function = function_id, .type = .number, .origin = .{ .parameter = 2 } },
        .{ .id = first, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_true, .index = 0 } } },
        .{ .id = later, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_false, .index = 0 } } },
        .{ .id = header_control, .function = function_id, .type = .number, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = header_limit, .function = function_id, .type = .number, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
        .{ .id = header_step, .function = function_id, .type = .number, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
        .{ .id = header_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 2 } } },
        .{ .id = index, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = i_next, .index = 3 } } },
        .{ .id = body_index, .function = function_id, .type = .number, .origin = .{ .block_parameter = .{ .block = body, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = i_true, .block = entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{first}, .effects = .pure },
        .{ .id = i_false, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{later}, .effects = .pure },
        .{ .id = i_next, .block = header, .operation = .{ .numeric_for_next = .{
            .control = header_control,
            .limit = header_limit,
            .step = header_step,
            .initial = header_initial,
        } }, .results = &.{ has_value, normalized_limit, normalized_step, index }, .effects = .numeric_for_next },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{ i_true, i_false }, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &.{ control, limit, step, first },
        } } },
        .{ .id = header, .function = function_id, .parameters = &.{ header_control, header_limit, header_step, header_initial }, .instructions = &.{i_next}, .terminator = .{ .branch = .{
            .condition = has_value,
            .then_edge = .{ .target = body, .arguments = &.{index} },
            .else_edge = .{ .target = exit_block },
        } } },
        .{ .id = body, .function = function_id, .parameters = &.{body_index}, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &.{ index, normalized_limit, normalized_step, later },
        } } },
        .{ .id = exit_block, .function = function_id, .terminator = .{ .return_values = &.{ normalized_limit, normalized_step } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ control, limit, step },
        .blocks = &.{ entry, header, body, exit_block },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "numeric-normalized-state-escape",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var structured = try structure.Plan.init(std.testing.allocator, &analysis);
    defer structured.deinit();
    var transfers = try lexical_transfer.Plan.init(std.testing.allocator, &program, functions[0], &analysis, &structured);
    defer transfers.deinit();
    try std.testing.expectEqual(@as(usize, 0), transfers.transfers.len);
    try std.testing.expectEqual(@as(usize, 2), transfers.aliases.len);
    try std.testing.expectEqual(normalized_limit, transfers.aliases[0].value);
    try std.testing.expectEqual(limit, transfers.aliases[0].replacement);
    try std.testing.expectEqual(normalized_step, transfers.aliases[1].value);
    try std.testing.expectEqual(step, transfers.aliases[1].replacement);

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const prepared = try lexical_transfer.prepareInArena(arena.allocator(), &program);
    try std.testing.expectEqual(program.values.len, prepared.values.len);
    try std.testing.expectEqual(program.places.len, prepared.places.len);
    try std.testing.expectEqual(program.instructions.len, prepared.instructions.len);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ limit, step }, prepared.blocks[exit_block.index()].terminator.return_values);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ normalized_limit, normalized_step }, program.blocks[exit_block.index()].terminator.return_values);
}
