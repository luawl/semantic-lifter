const std = @import("std");
const cfg = @import("cfg.zig");
const ir = @import("ir.zig");
const structural_overlap = @import("structural_overlap.zig");

const fixture = struct {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const incoming = ir.BlockId.fromIndex(2);
    const compound = ir.BlockId.fromIndex(3);
    const forwarding = ir.BlockId.fromIndex(4);
    const transition = ir.BlockId.fromIndex(5);
    const exit = ir.BlockId.fromIndex(6);

    const selector = ir.ValueId.fromIndex(0);
    const owner_control = ir.ValueId.fromIndex(1);
    const owner_limit = ir.ValueId.fromIndex(2);
    const owner_step = ir.ValueId.fromIndex(3);
    const owner_initial = ir.ValueId.fromIndex(4);
    const actual_seed_control = ir.ValueId.fromIndex(5);
    const actual_seed_limit = ir.ValueId.fromIndex(6);
    const actual_seed_step = ir.ValueId.fromIndex(7);
    const actual_seed_initial = ir.ValueId.fromIndex(8);
    const false_value = ir.ValueId.fromIndex(9);
    const compound_control = ir.ValueId.fromIndex(10);
    const compound_limit = ir.ValueId.fromIndex(11);
    const compound_step = ir.ValueId.fromIndex(12);
    const compound_initial = ir.ValueId.fromIndex(13);
    const transition_control = ir.ValueId.fromIndex(14);
    const transition_limit = ir.ValueId.fromIndex(15);
    const transition_step = ir.ValueId.fromIndex(16);
    const transition_initial = ir.ValueId.fromIndex(17);
    const actual_control = ir.ValueId.fromIndex(18);
    const actual_limit = ir.ValueId.fromIndex(19);
    const actual_step = ir.ValueId.fromIndex(20);
    const actual_initial = ir.ValueId.fromIndex(21);
    const has_value = ir.ValueId.fromIndex(22);
    const normalized_limit = ir.ValueId.fromIndex(23);
    const normalized_step = ir.ValueId.fromIndex(24);
    const next_control = ir.ValueId.fromIndex(25);
    const compound_read = ir.ValueId.fromIndex(26);
    const compound_constant = ir.ValueId.fromIndex(27);
    const compound_product = ir.ValueId.fromIndex(28);
    const forwarding_read = ir.ValueId.fromIndex(29);
    const forwarding_constant = ir.ValueId.fromIndex(30);

    const false_instruction = ir.InstructionId.fromIndex(0);
    const compound_read_instruction = ir.InstructionId.fromIndex(1);
    const compound_constant_instruction = ir.InstructionId.fromIndex(2);
    const compound_multiply_instruction = ir.InstructionId.fromIndex(3);
    const compound_write_instruction = ir.InstructionId.fromIndex(4);
    const forwarding_read_instruction = ir.InstructionId.fromIndex(5);
    const forwarding_constant_instruction = ir.InstructionId.fromIndex(6);
    const forwarding_write_instruction = ir.InstructionId.fromIndex(7);
    const transition_instruction = ir.InstructionId.fromIndex(8);

    const place_a = ir.PlaceId.fromIndex(0);
    const place_b = ir.PlaceId.fromIndex(1);

    const owner_tuple = [_]ir.ValueId{
        owner_control,
        owner_limit,
        owner_step,
        owner_initial,
    };
    const actual_seed_tuple = [_]ir.ValueId{
        actual_seed_control,
        actual_seed_limit,
        actual_seed_step,
        actual_seed_initial,
    };
    const compound_tuple = [_]ir.ValueId{
        compound_control,
        compound_limit,
        compound_step,
        compound_initial,
    };
    const transition_tuple = [_]ir.ValueId{
        transition_control,
        transition_limit,
        transition_step,
        transition_initial,
    };
    const actual_tuple = [_]ir.ValueId{
        actual_control,
        actual_limit,
        actual_step,
        actual_initial,
    };
    const reentry_tuple = [_]ir.ValueId{
        next_control,
        normalized_limit,
        normalized_step,
        false_value,
    };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{false_instruction}, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = incoming, .arguments = actual_seed_tuple[0..] },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{
            .target = compound,
            .arguments = owner_tuple[0..],
        } } },
        .{ .id = incoming, .function = function_id, .parameters = actual_tuple[0..], .terminator = .{ .jump = .{
            .target = compound,
            .arguments = actual_tuple[0..],
        } } },
        .{ .id = compound, .function = function_id, .parameters = compound_tuple[0..], .instructions = &.{
            compound_read_instruction,
            compound_constant_instruction,
            compound_multiply_instruction,
            compound_write_instruction,
        }, .terminator = .{ .jump = .{ .target = forwarding } } },
        .{ .id = forwarding, .function = function_id, .instructions = &.{
            forwarding_read_instruction,
            forwarding_constant_instruction,
            forwarding_write_instruction,
        }, .terminator = .{ .jump = .{
            .target = transition,
            .arguments = compound_tuple[0..],
        } } },
        .{ .id = transition, .function = function_id, .parameters = transition_tuple[0..], .instructions = &.{transition_instruction}, .terminator = .{ .branch = .{
            .condition = has_value,
            .then_edge = .{ .target = incoming, .arguments = reentry_tuple[0..] },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };

    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = owner_control, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = owner_limit, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } },
        .{ .id = owner_step, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 3 } },
        .{ .id = owner_initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } },
        .{ .id = actual_seed_control, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 5 } },
        .{ .id = actual_seed_limit, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 6 } },
        .{ .id = actual_seed_step, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 7 } },
        .{ .id = actual_seed_initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 8 } },
        .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } },
        .{ .id = compound_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = compound, .index = 0 } } },
        .{ .id = compound_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = compound, .index = 1 } } },
        .{ .id = compound_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = compound, .index = 2 } } },
        .{ .id = compound_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = compound, .index = 3 } } },
        .{ .id = transition_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = transition, .index = 0 } } },
        .{ .id = transition_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = transition, .index = 1 } } },
        .{ .id = transition_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = transition, .index = 2 } } },
        .{ .id = transition_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = transition, .index = 3 } } },
        .{ .id = actual_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = incoming, .index = 0 } } },
        .{ .id = actual_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = incoming, .index = 1 } } },
        .{ .id = actual_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = incoming, .index = 2 } } },
        .{ .id = actual_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = incoming, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 3 } } },
        .{ .id = compound_read, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = compound_read_instruction, .index = 0 } } },
        .{ .id = compound_constant, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = compound_constant_instruction, .index = 0 } } },
        .{ .id = compound_product, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = compound_multiply_instruction, .index = 0 } } },
        .{ .id = forwarding_read, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = forwarding_read_instruction, .index = 0 } } },
        .{ .id = forwarding_constant, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = forwarding_constant_instruction, .index = 0 } } },
    };

    const instructions = [_]ir.Instruction{
        .{ .id = false_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = compound_read_instruction, .block = compound, .operation = .{ .place_read = place_a }, .results = &.{compound_read}, .effects = .place_read },
        .{ .id = compound_constant_instruction, .block = compound, .operation = .{ .constant = .{ .number = 7 } }, .results = &.{compound_constant}, .effects = .pure },
        .{ .id = compound_multiply_instruction, .block = compound, .operation = .{ .binary = .{ .operator = .multiply, .left = compound_read, .right = compound_constant, .mode = .semantic } }, .results = &.{compound_product}, .effects = .semantic_table_read },
        .{ .id = compound_write_instruction, .block = compound, .operation = .{ .place_write = .{ .place = place_a, .value = compound_product } }, .results = &.{}, .effects = .place_write },
        .{ .id = forwarding_read_instruction, .block = forwarding, .operation = .{ .place_read = place_a }, .results = &.{forwarding_read}, .effects = .place_read },
        .{ .id = forwarding_constant_instruction, .block = forwarding, .operation = .{ .constant = .{ .number = 11 } }, .results = &.{forwarding_constant}, .effects = .pure },
        .{ .id = forwarding_write_instruction, .block = forwarding, .operation = .{ .place_write = .{ .place = place_b, .value = forwarding_constant } }, .results = &.{}, .effects = .place_write },
        .{ .id = transition_instruction, .block = transition, .operation = .{ .numeric_for_next = .{
            .control = transition_control,
            .limit = transition_limit,
            .step = transition_step,
            .initial = transition_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ has_value, normalized_limit, normalized_step, next_control }, .effects = .numeric_for_next },
    };

    const places = [_]ir.Place{
        .{ .id = place_a, .function = function_id, .type = .dynamic, .origin = .{ .local = 0 } },
        .{ .id = place_b, .function = function_id, .type = .dynamic, .origin = .{ .local = 1 } },
    };

    const function = ir.Function{
        .id = function_id,
        .parameters = &.{
            selector,
            owner_control,
            owner_limit,
            owner_step,
            owner_initial,
            actual_seed_control,
            actual_seed_limit,
            actual_seed_step,
            actual_seed_initial,
        },
        .local_places = &.{ place_a, place_b },
        .blocks = &.{ entry, owner, incoming, compound, forwarding, transition, exit },
        .entry_block = entry,
    };

    const program = ir.Program{
        .program_id = "effectful-parameterized-compound-continuation",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };
};

fn compoundProjection(program: *const ir.Program) !bool {
    var analysis = try cfg.Analysis.init(std.testing.allocator, program, program.functions[0]);
    defer analysis.deinit();
    var replay = try structural_overlap.ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        program,
        fixture.function_id,
    );
    defer replay.deinit();
    const incoming: ir.CfgEdgeRef = .{ .source = fixture.incoming, .kind = .jump, .target = fixture.compound };
    return replay.hasAuthenticatedIterationContextualProjectionForEdge(
        &analysis,
        incoming,
        fixture.owner_tuple[0..],
    );
}

test "effectful compound continuation authenticates a parameterized reentry" {
    try std.testing.expect(try compoundProjection(&fixture.program));
}

test "effectful compound continuation rejects incomplete or altered proofs" {
    var changed_forward_blocks = fixture.blocks;
    changed_forward_blocks[fixture.forwarding.index()].terminator = .{ .jump = .{
        .target = fixture.transition,
        .arguments = fixture.transition_tuple[0..],
    } };
    var changed_forward_program = fixture.program;
    changed_forward_program.blocks = &changed_forward_blocks;
    try std.testing.expect(!try compoundProjection(&changed_forward_program));

    var branched_prefix_blocks = fixture.blocks;
    branched_prefix_blocks[fixture.compound.index()].terminator = .{ .branch = .{
        .condition = fixture.selector,
        .then_edge = .{ .target = fixture.forwarding },
        .else_edge = .{ .target = fixture.exit },
    } };
    var branched_prefix_program = fixture.program;
    branched_prefix_program.blocks = &branched_prefix_blocks;
    try std.testing.expect(!try compoundProjection(&branched_prefix_program));

    var removed_transition_header_blocks = fixture.blocks;
    removed_transition_header_blocks[fixture.transition.index()].terminator = .{ .return_values = &.{} };
    var removed_transition_header_program = fixture.program;
    removed_transition_header_program.blocks = &removed_transition_header_blocks;
    try std.testing.expect(!try compoundProjection(&removed_transition_header_program));

    var acyclic_blocks = fixture.blocks;
    acyclic_blocks[fixture.transition.index()].terminator = .{ .branch = .{
        .condition = fixture.has_value,
        .then_edge = .{ .target = fixture.exit },
        .else_edge = .{ .target = fixture.exit },
    } };
    var acyclic_program = fixture.program;
    acyclic_program.blocks = &acyclic_blocks;
    try std.testing.expect(try compoundProjection(&acyclic_program));

    var removed_owner_blocks = fixture.blocks;
    removed_owner_blocks[fixture.owner.index()].terminator = .{ .jump = .{ .target = fixture.exit } };
    var removed_owner_program = fixture.program;
    removed_owner_program.blocks = &removed_owner_blocks;
    try std.testing.expect(!try compoundProjection(&removed_owner_program));
}
