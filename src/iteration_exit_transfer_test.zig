const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const exit_transfer = @import("iteration_exit_transfer.zig");

test "native iteration exit arguments require values stable before the header" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const stable_instruction = ir.InstructionId.fromIndex(0);
    const header_instruction = ir.InstructionId.fromIndex(1);
    const body_instruction = ir.InstructionId.fromIndex(2);
    const parameter = ir.ValueId.fromIndex(0);
    const stable_value = ir.ValueId.fromIndex(1);
    const header_value = ir.ValueId.fromIndex(2);
    const body_value = ir.ValueId.fromIndex(3);
    const first_exit_parameter = ir.ValueId.fromIndex(4);
    const second_exit_parameter = ir.ValueId.fromIndex(5);

    const values = [_]ir.Value{
        .{ .id = parameter, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = stable_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = stable_instruction, .index = 0 } } },
        .{ .id = header_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = header_instruction, .index = 0 } } },
        .{ .id = body_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = body_instruction, .index = 0 } } },
        .{ .id = first_exit_parameter, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = exit, .index = 0 } } },
        .{ .id = second_exit_parameter, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = exit, .index = 1 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = stable_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{stable_value}, .effects = .pure },
        .{ .id = header_instruction, .block = header, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{header_value}, .effects = .pure },
        .{ .id = body_instruction, .block = body, .operation = .{ .constant = .{ .boolean = true } }, .results = &.{body_value}, .effects = .pure },
    };
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{stable_instruction}, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .instructions = &.{header_instruction}, .terminator = .{ .branch = .{ .condition = header_value, .then_edge = .{ .target = body }, .else_edge = .{ .target = exit, .arguments = &.{ parameter, stable_value } } } } },
        .{ .id = body, .function = function_id, .instructions = &.{body_instruction}, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = exit, .function = function_id, .parameters = &.{ first_exit_parameter, second_exit_parameter }, .terminator = .{ .return_values = &.{ first_exit_parameter, second_exit_parameter } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{parameter},
        .blocks = &.{ entry, header, body, exit },
        .entry_block = entry,
    }};
    var program: ir.Program = .{
        .program_id = "iteration-exit-transfer-test",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const exit_edge = blocks[header.index()].terminator.branch.else_edge;
    try std.testing.expect(try exit_transfer.supportsInvariantArguments(&program, &analysis, header, exit_edge));

    blocks[header.index()].terminator.branch.else_edge.arguments = &.{ parameter, header_value };
    try std.testing.expect(!try exit_transfer.supportsInvariantArguments(
        &program,
        &analysis,
        header,
        blocks[header.index()].terminator.branch.else_edge,
    ));
    blocks[header.index()].terminator.branch.else_edge.arguments = &.{ parameter, body_value };
    try std.testing.expect(!try exit_transfer.supportsInvariantArguments(
        &program,
        &analysis,
        header,
        blocks[header.index()].terminator.branch.else_edge,
    ));

    blocks[header.index()].terminator.branch.else_edge.arguments = &.{ parameter, stable_value };
    blocks[body.index()].terminator = .{ .jump = .{ .target = entry } };
    var reentered_analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer reentered_analysis.deinit();
    try std.testing.expect(!try exit_transfer.supportsInvariantArguments(
        &program,
        &reentered_analysis,
        header,
        blocks[header.index()].terminator.branch.else_edge,
    ));
}

test "native iteration exit arguments accept only canonical immutable captures" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const condition_instruction = ir.InstructionId.fromIndex(0);
    const capture_id = ir.CaptureId.fromIndex(0);
    const captured = ir.ValueId.fromIndex(0);
    const condition = ir.ValueId.fromIndex(1);
    const exit_parameter = ir.ValueId.fromIndex(2);

    const values = [_]ir.Value{
        .{ .id = captured, .function = function_id, .origin = .{ .capture = capture_id } },
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = condition_instruction, .index = 0 } } },
        .{ .id = exit_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = exit, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = condition_instruction,
        .block = header,
        .operation = .{ .constant = .{ .boolean = true } },
        .results = &.{condition},
        .effects = .pure,
    }};
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = header, .function = function_id, .instructions = &.{condition_instruction}, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit, .arguments = &.{captured} },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = header } } },
        .{ .id = exit, .function = function_id, .parameters = &.{exit_parameter}, .terminator = .{ .return_values = &.{exit_parameter} } },
    };
    var captures = [_]ir.Capture{.{
        .id = capture_id,
        .function = function_id,
        .kind = .{ .immutable_value = captured },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .captures = &.{capture_id},
        .blocks = &.{ entry, header, body, exit },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "iteration-exit-capture-test",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .captures = &captures,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const exit_edge = blocks[header.index()].terminator.branch.else_edge;
    try std.testing.expect(try exit_transfer.supportsInvariantArguments(&program, &analysis, header, exit_edge));

    captures[0].kind = .{ .shared_place = ir.PlaceId.fromIndex(0) };
    try std.testing.expect(!try exit_transfer.supportsInvariantArguments(&program, &analysis, header, exit_edge));
    captures[0].kind = .{ .immutable_value = condition };
    try std.testing.expect(!try exit_transfer.supportsInvariantArguments(&program, &analysis, header, exit_edge));
}

test "native iteration exit arguments may use enclosing-loop definitions until direct reentry" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const outer_header = ir.BlockId.fromIndex(1);
    const definition = ir.BlockId.fromIndex(2);
    const inner_header = ir.BlockId.fromIndex(3);
    const inner_body = ir.BlockId.fromIndex(4);
    const inner_exit = ir.BlockId.fromIndex(5);
    const function_exit = ir.BlockId.fromIndex(6);
    const stable_instruction = ir.InstructionId.fromIndex(0);
    const condition = ir.ValueId.fromIndex(0);
    const stable_value = ir.ValueId.fromIndex(1);
    const exit_parameter = ir.ValueId.fromIndex(2);

    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = stable_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = stable_instruction, .index = 0 } } },
        .{ .id = exit_parameter, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = inner_exit, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = stable_instruction,
        .block = definition,
        .operation = .{ .constant = .{ .boolean = true } },
        .results = &.{stable_value},
        .effects = .pure,
    }};
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = outer_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = definition },
            .else_edge = .{ .target = function_exit },
        } } },
        .{ .id = definition, .function = function_id, .instructions = &.{stable_instruction}, .terminator = .{ .jump = .{ .target = inner_header } } },
        .{ .id = inner_header, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = inner_body },
            .else_edge = .{ .target = inner_exit, .arguments = &.{stable_value} },
        } } },
        .{ .id = inner_body, .function = function_id, .terminator = .{ .jump = .{ .target = inner_header } } },
        .{ .id = inner_exit, .function = function_id, .parameters = &.{exit_parameter}, .terminator = .{ .jump = .{ .target = outer_header } } },
        .{ .id = function_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, outer_header, definition, inner_header, inner_body, inner_exit, function_exit },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "iteration-nested-exit-transfer-test",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    const exit_edge = blocks[inner_header.index()].terminator.branch.else_edge;

    {
        var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
        defer analysis.deinit();
        try std.testing.expect(try analysis.canReach(inner_header, definition));
        try std.testing.expect(!try analysis.canReachAvoiding(inner_header, definition, inner_exit));
        try std.testing.expect(try exit_transfer.supportsInvariantArguments(&program, &analysis, inner_header, exit_edge));
    }

    blocks[inner_body.index()].terminator = .{ .jump = .{ .target = definition } };
    var reentered_analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer reentered_analysis.deinit();
    try std.testing.expect(try reentered_analysis.canReachAvoiding(inner_header, definition, inner_exit));
    try std.testing.expect(!try exit_transfer.supportsInvariantArguments(
        &program,
        &reentered_analysis,
        inner_header,
        exit_edge,
    ));
}
