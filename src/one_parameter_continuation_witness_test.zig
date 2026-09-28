const std = @import("std");
const cfg = @import("cfg.zig");
const ir = @import("ir.zig");
const structural_overlap = @import("structural_overlap.zig");

const fixture = struct {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const source = ir.BlockId.fromIndex(2);
    const source_successor = ir.BlockId.fromIndex(3);
    const clone = ir.BlockId.fromIndex(4);
    const clone_successor = ir.BlockId.fromIndex(5);
    const exit = ir.BlockId.fromIndex(6);

    const function_parameter_0 = ir.ValueId.fromIndex(0);
    const function_parameter_1 = ir.ValueId.fromIndex(1);
    const function_parameter_2 = ir.ValueId.fromIndex(2);
    const function_parameter_3 = ir.ValueId.fromIndex(3);
    const header_parameter_0 = ir.ValueId.fromIndex(4);
    const header_parameter_1 = ir.ValueId.fromIndex(5);
    const header_parameter_2 = ir.ValueId.fromIndex(6);
    const header_parameter_3 = ir.ValueId.fromIndex(7);
    const has_value = ir.ValueId.fromIndex(8);
    const normalized_limit = ir.ValueId.fromIndex(9);
    const normalized_step = ir.ValueId.fromIndex(10);
    const next_control = ir.ValueId.fromIndex(11);
    const source_parameter = ir.ValueId.fromIndex(12);
    const clone_parameter = ir.ValueId.fromIndex(13);

    const transition_instruction = ir.InstructionId.fromIndex(0);
    const source_write_instruction = ir.InstructionId.fromIndex(1);
    const clone_write_instruction = ir.InstructionId.fromIndex(2);
    const place = ir.PlaceId.fromIndex(0);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const wrong_group = ir.NodeSplitGroupId.fromIndex(1);

    const entry_arguments = [_]ir.ValueId{
        function_parameter_0,
        function_parameter_1,
        function_parameter_2,
        function_parameter_3,
    };
    const incoming_arguments = [_]ir.ValueId{next_control};
    const reentry_arguments = [_]ir.ValueId{
        next_control,
        normalized_limit,
        normalized_step,
        function_parameter_3,
    };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = function_parameter_0,
            .then_edge = .{ .target = header, .arguments = entry_arguments[0..] },
            .else_edge = .{ .target = source, .arguments = incoming_arguments[0..] },
        } } },
        .{ .id = header, .function = function_id, .parameters = &.{
            header_parameter_0,
            header_parameter_1,
            header_parameter_2,
            header_parameter_3,
        }, .instructions = &.{transition_instruction}, .terminator = .{ .branch = .{
            .condition = has_value,
            .then_edge = .{ .target = clone, .arguments = incoming_arguments[0..] },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = source, .function = function_id, .parameters = &.{source_parameter}, .instructions = &.{source_write_instruction}, .terminator = .{ .jump = .{
            .target = source_successor,
        } } },
        .{ .id = source_successor, .function = function_id, .terminator = .{ .jump = .{
            .target = header,
            .arguments = reentry_arguments[0..],
        } } },
        .{ .id = clone, .function = function_id, .parameters = &.{clone_parameter}, .instructions = &.{clone_write_instruction}, .terminator = .{ .jump = .{
            .target = clone_successor,
        } } },
        .{ .id = clone_successor, .function = function_id, .terminator = .{ .jump = .{
            .target = header,
            .arguments = reentry_arguments[0..],
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };

    const values = [_]ir.Value{
        .{ .id = function_parameter_0, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = function_parameter_1, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = function_parameter_2, .function = function_id, .origin = .{ .parameter = 2 } },
        .{ .id = function_parameter_3, .function = function_id, .origin = .{ .parameter = 3 } },
        .{ .id = header_parameter_0, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = header_parameter_1, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
        .{ .id = header_parameter_2, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
        .{ .id = header_parameter_3, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 3 } } },
        .{ .id = source_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = source, .index = 0 } } },
        .{ .id = clone_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = clone, .index = 0 } } },
    };

    const instructions = [_]ir.Instruction{
        .{ .id = transition_instruction, .block = header, .operation = .{ .numeric_for_next = .{
            .control = header_parameter_0,
            .limit = header_parameter_1,
            .step = header_parameter_2,
            .initial = header_parameter_3,
            .mode = .semantic_normalized,
        } }, .results = &.{ has_value, normalized_limit, normalized_step, next_control }, .effects = .numeric_for_next },
        .{ .id = source_write_instruction, .block = source, .operation = .{ .place_write = .{
            .place = place,
            .value = source_parameter,
        } }, .results = &.{}, .effects = .place_write },
        .{ .id = clone_write_instruction, .block = clone, .operation = .{ .place_write = .{
            .place = place,
            .value = clone_parameter,
        } }, .results = &.{}, .effects = .place_write },
    };

    const places = [_]ir.Place{.{
        .id = place,
        .function = function_id,
        .origin = .{ .local = 0 },
    }};

    const function = ir.Function{
        .id = function_id,
        .parameters = &.{
            function_parameter_0,
            function_parameter_1,
            function_parameter_2,
            function_parameter_3,
        },
        .local_places = &.{place},
        .blocks = &.{ entry, header, source, source_successor, clone, clone_successor, exit },
        .entry_block = entry,
    };

    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = header,
            .kind = .branch_then,
            .from = .{ .target = source, .arguments = incoming_arguments[0..] },
            .to = .{ .target = clone, .arguments = incoming_arguments[0..] },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = clone,
            .kind = .jump,
            .from = .{ .target = source_successor },
            .to = .{ .target = clone_successor },
            .rule = .node_split,
            .node_split_group = group,
        },
    };

    const program = ir.Program{
        .program_id = "one-parameter-continuation-witness",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
        .edge_rewrites = &rewrites,
    };
};

fn accepts(program: *const ir.Program, expected: ir.ValueId) !bool {
    var analysis = try cfg.Analysis.init(std.testing.allocator, program, program.functions[0]);
    defer analysis.deinit();
    var replay = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        program,
        fixture.function_id,
    );
    defer replay.deinit();
    return replay.hasAuthenticatedOneParameterContinuationForEdge(
        &analysis,
        .{ .source = fixture.header, .kind = .branch_then, .target = fixture.clone },
        &.{expected},
    );
}

test "one-parameter continuation witness authenticates replayed numeric reentry" {
    try std.testing.expect(try accepts(&fixture.program, fixture.next_control));
}

test "one-parameter continuation witness accepts a replayed terminal exit" {
    var blocks = fixture.blocks;
    blocks[fixture.source_successor.index()].terminator = .{ .return_values = &.{} };
    blocks[fixture.clone_successor.index()].terminator = .{ .return_values = &.{} };
    var program = fixture.program;
    program.blocks = &blocks;
    try std.testing.expect(try accepts(&program, fixture.next_control));
}

test "one-parameter continuation witness accepts an unreachable historical successor" {
    var blocks = fixture.blocks;
    blocks[fixture.entry.index()].terminator = .{ .branch = .{
        .condition = fixture.function_parameter_0,
        .then_edge = .{ .target = fixture.header, .arguments = fixture.entry_arguments[0..] },
        .else_edge = .{ .target = fixture.header, .arguments = fixture.entry_arguments[0..] },
    } };
    var program = fixture.program;
    program.blocks = &blocks;
    try std.testing.expect(try accepts(&program, fixture.next_control));
}

test "one-parameter continuation witness rejects altered proof dimensions" {
    var changed_effects = fixture.instructions;
    changed_effects[fixture.clone_write_instruction.index()].effects = .pure;
    var changed_effect_program = fixture.program;
    changed_effect_program.instructions = &changed_effects;
    try std.testing.expect(!(try accepts(&changed_effect_program, fixture.next_control)));

    var changed_successor_blocks = fixture.blocks;
    changed_successor_blocks[fixture.clone.index()].terminator = .{ .jump = .{ .target = fixture.exit } };
    var changed_successor_program = fixture.program;
    changed_successor_program.blocks = &changed_successor_blocks;
    try std.testing.expect(!(try accepts(&changed_successor_program, fixture.next_control)));

    var changed_arguments = fixture.blocks;
    changed_arguments[fixture.header.index()].terminator.branch.then_edge.arguments = &.{fixture.function_parameter_0};
    var changed_arguments_program = fixture.program;
    changed_arguments_program.blocks = &changed_arguments;
    try std.testing.expect(!(try accepts(&changed_arguments_program, fixture.next_control)));

    var changed_group = fixture.rewrites;
    changed_group[fixture.rewrites.len - 1].node_split_group = fixture.wrong_group;
    var changed_group_program = fixture.program;
    changed_group_program.edge_rewrites = &changed_group;
    try std.testing.expect(!(try accepts(&changed_group_program, fixture.next_control)));

    var changed_topology = fixture.blocks;
    changed_topology[fixture.clone_successor.index()].terminator = .{ .jump = .{ .target = fixture.exit } };
    var changed_topology_program = fixture.program;
    changed_topology_program.blocks = &changed_topology;
    try std.testing.expect(!(try accepts(&changed_topology_program, fixture.next_control)));
}
