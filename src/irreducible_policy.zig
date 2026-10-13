const std = @import("std");
const ir = @import("ir.zig");
const cfg_edge = @import("cfg_edge.zig");
const irreducible_region = @import("irreducible_region.zig");
const node_split = @import("node_split.zig");
const iteration_protocol = @import("iteration_protocol.zig");

pub const Refusal = enum {
    entry_contract,
    instructions,
    parameter_contract,
    incoming_edge_contract,
    nonprimary_successor,
};

pub const PrimarySelection = struct {
    block: ir.BlockId,
    refusal: ?Refusal = null,
};

pub fn selectPrimary(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    region: irreducible_region.Region,
) std.mem.Allocator.Error!PrimarySelection {
    std.debug.assert(region.entries.len != 0);
    for (region.entries) |entry| {
        if (entry.is_function_entry) return .{
            .block = entry.block,
            .refusal = classifyPrimary(program, entry),
        };
    }

    const scores = try allocator.alloc(usize, region.entries.len);
    defer allocator.free(scores);
    @memset(scores, 0);
    for (region.entries) |entry| {
        if (baseRefusal(program, entry) != null) continue;
        const requirement = requiredPrimary(region.blocks, program.blocks[entry.block.index()].terminator);
        if (!requirement.compatible or requirement.target == null or requirement.target.? == entry.block) continue;
        const target_index = entryIndex(region.entries, requirement.target.?) orelse continue;
        if (classifyPrimary(program, region.entries[target_index]) != null) continue;
        scores[target_index] += 1;
    }

    var best_index: ?usize = null;
    for (region.entries, 0..) |entry, index| {
        if (classifyPrimary(program, entry) != null) continue;
        const self_successor = hasSelfSuccessor(program, entry.block);
        const best_self_successor = if (best_index) |best| hasSelfSuccessor(program, region.entries[best].block) else false;
        if (best_index == null or (best_self_successor and !self_successor) or
            (best_self_successor == self_successor and scores[index] > scores[best_index.?]) or
            (best_self_successor == self_successor and scores[index] == scores[best_index.?] and
                transitionHeaderPriority(program, entry.block) and
                !transitionHeaderPriority(program, region.entries[best_index.?].block)))
        {
            best_index = index;
        }
    }
    if (best_index) |index| return .{ .block = region.entries[index].block };

    const fallback = region.entries[0];
    return .{
        .block = fallback.block,
        .refusal = classifyPrimary(program, fallback) orelse .entry_contract,
    };
}

pub fn classifyPrimary(program: *const ir.Program, entry: irreducible_region.Entry) ?Refusal {
    if ((!entry.is_function_entry and entry.incoming.len == 0) or entry.block.index() >= program.blocks.len) return .entry_contract;
    const block = program.blocks[entry.block.index()];
    if (block.id != entry.block) return .entry_contract;
    if (!node_split.parametersAreCanonical(program.values, block)) return .parameter_contract;
    for (entry.incoming) |reference| {
        const edge = cfg_edge.value(program, reference) orelse return .incoming_edge_contract;
        if (edge.target != entry.block or edge.arguments.len != block.parameters.len) return .incoming_edge_contract;
    }
    return null;
}

// Diagnostic classification only: the splitter (`planRegion` in irreducible_normalize.zig)
// consults `classifySecondarySource`, not this function, and `cloneClosure` clones the
// secondary's whole in-region closure up to the primary, so a non-primary successor is
// cloned with it. `.nonprimary_successor` names the single-block repair shape for the
// `validate_cfg` UnsupportedShape report, which is currently unreachable for valid CFGs.
pub fn classifySecondary(
    program: *const ir.Program,
    region: irreducible_region.Region,
    primary: ir.BlockId,
    entry: irreducible_region.Entry,
) ?Refusal {
    if (entry.block == primary) return null;
    if (classifySecondarySource(program, entry)) |refusal| return refusal;
    const block = program.blocks[entry.block.index()];
    const outgoing = successorTargets(block.terminator);
    for (outgoing.ids[0..outgoing.len]) |target| {
        if (blockInRegion(region.blocks, target) and target != primary and target != entry.block) return .nonprimary_successor;
    }
    return null;
}

pub fn classifySecondarySource(program: *const ir.Program, entry: irreducible_region.Entry) ?Refusal {
    if (entry.is_function_entry) return .entry_contract;
    if (classifyPrimary(program, entry)) |refusal| return refusal;
    const block = program.blocks[entry.block.index()];
    if (!node_split.instructionStructureIsCloneable(program, block)) return .instructions;
    return null;
}

fn baseRefusal(program: *const ir.Program, entry: irreducible_region.Entry) ?Refusal {
    if (entry.is_function_entry) return .entry_contract;
    if (classifyPrimary(program, entry)) |refusal| return refusal;
    const block = program.blocks[entry.block.index()];
    if (!node_split.instructionStructureIsCloneable(program, block)) return .instructions;
    return null;
}

const PrimaryRequirement = struct {
    target: ?ir.BlockId = null,
    compatible: bool = true,
};

fn requiredPrimary(region_blocks: []const ir.BlockId, terminator: ir.Terminator) PrimaryRequirement {
    const outgoing = successorTargets(terminator);
    var result: PrimaryRequirement = .{};
    for (outgoing.ids[0..outgoing.len]) |target| {
        if (!blockInRegion(region_blocks, target)) continue;
        if (result.target) |existing| {
            if (existing != target) return .{ .compatible = false };
        } else {
            result.target = target;
        }
    }
    if (result.target == null) result.compatible = false;
    return result;
}

fn entryIndex(entries: []const irreducible_region.Entry, block: ir.BlockId) ?usize {
    var low: usize = 0;
    var high = entries.len;
    while (low < high) {
        const middle = low + (high - low) / 2;
        if (entries[middle].block == block) return middle;
        if (entries[middle].block.index() < block.index()) {
            low = middle + 1;
        } else {
            high = middle;
        }
    }
    return null;
}

fn blockInRegion(blocks: []const ir.BlockId, candidate: ir.BlockId) bool {
    for (blocks) |block| if (block == candidate) return true;
    return false;
}

fn transitionHeaderPriority(program: *const ir.Program, block_id: ir.BlockId) bool {
    if (block_id.index() >= program.blocks.len) return false;
    const block = program.blocks[block_id.index()];
    return block.id == block_id and iteration_protocol.transitionForHeader(program, block) != null;
}

fn hasSelfSuccessor(program: *const ir.Program, block_id: ir.BlockId) bool {
    if (block_id.index() >= program.blocks.len) return false;
    const block = program.blocks[block_id.index()];
    if (block.id != block_id) return false;
    const outgoing = successorTargets(block.terminator);
    for (outgoing.ids[0..outgoing.len]) |target| if (target == block_id) return true;
    return false;
}

const SuccessorTargets = struct {
    ids: [2]ir.BlockId = undefined,
    len: usize = 0,
};

fn successorTargets(terminator: ir.Terminator) SuccessorTargets {
    var result: SuccessorTargets = .{};
    switch (terminator) {
        .jump => |edge| {
            result.ids[0] = edge.target;
            result.len = 1;
        },
        .branch => |branch| {
            result.ids[0] = branch.then_edge.target;
            result.ids[1] = branch.else_edge.target;
            result.len = 2;
        },
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
    }
    return result;
}

test "secondary refusal reasons are isolated and deterministic" {
    const function_id = ir.FunctionId.fromIndex(0);
    const primary = ir.BlockId.fromIndex(0);
    const secondary = ir.BlockId.fromIndex(1);
    const external = ir.BlockId.fromIndex(2);
    const tertiary = ir.BlockId.fromIndex(3);
    const incoming_value = ir.ValueId.fromIndex(0);
    const parameter = ir.ValueId.fromIndex(1);
    const base_blocks = [_]ir.Block{
        .{ .id = primary, .function = function_id, .terminator = .{ .jump = .{ .target = secondary, .arguments = &.{incoming_value} } } },
        .{ .id = secondary, .function = function_id, .parameters = &.{parameter}, .terminator = .{ .jump = .{ .target = primary } } },
        .{ .id = external, .function = function_id, .terminator = .{ .jump = .{ .target = secondary, .arguments = &.{incoming_value} } } },
        .{ .id = tertiary, .function = function_id, .terminator = .{ .jump = .{ .target = primary } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{incoming_value},
        .blocks = &.{ primary, secondary, external, tertiary },
        .entry_block = external,
    }};
    const base_values = [_]ir.Value{
        .{ .id = incoming_value, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = secondary, .index = 0 } } },
    };
    var program: ir.Program = .{
        .program_id = "irreducible-policy-reasons",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &base_blocks,
        .instructions = &.{},
        .values = &base_values,
    };
    var primary_incoming = [_]ir.CfgEdgeRef{.{ .source = external, .kind = .jump, .target = primary }};
    var secondary_incoming = [_]ir.CfgEdgeRef{.{ .source = external, .kind = .jump, .target = secondary }};
    var entries = [_]irreducible_region.Entry{
        .{ .block = primary, .incoming = &primary_incoming, .is_function_entry = false },
        .{ .block = secondary, .incoming = &secondary_incoming, .is_function_entry = false },
    };
    var region_blocks = [_]ir.BlockId{ primary, secondary, tertiary };
    const region: irreducible_region.Region = .{ .blocks = &region_blocks, .entries = &entries };
    try std.testing.expect(classifySecondary(&program, region, primary, entries[1]) == null);

    var changed_blocks = base_blocks;
    changed_blocks[secondary.index()].instructions = &.{ir.InstructionId.fromIndex(0)};
    program.blocks = &changed_blocks;
    try std.testing.expectEqual(Refusal.instructions, classifySecondary(&program, region, primary, entries[1]).?);

    program.blocks = &base_blocks;
    var changed_values = base_values;
    changed_values[parameter.index()].origin = .{ .parameter = 1 };
    program.values = &changed_values;
    try std.testing.expectEqual(Refusal.parameter_contract, classifySecondary(&program, region, primary, entries[1]).?);

    program.values = &base_values;
    changed_blocks = base_blocks;
    changed_blocks[external.index()].terminator.jump.arguments = &.{};
    program.blocks = &changed_blocks;
    try std.testing.expectEqual(Refusal.incoming_edge_contract, classifySecondary(&program, region, primary, entries[1]).?);

    changed_blocks = base_blocks;
    changed_blocks[secondary.index()].terminator.jump.target = tertiary;
    program.blocks = &changed_blocks;
    try std.testing.expectEqual(Refusal.nonprimary_successor, classifySecondary(&program, region, primary, entries[1]).?);

    changed_blocks[secondary.index()].terminator.jump.target = secondary;
    try std.testing.expect(classifySecondary(&program, region, primary, entries[1]) == null);
}

test "primary selection prefers cloning a self-loop secondary" {
    const function_id = ir.FunctionId.fromIndex(0);
    const first = ir.BlockId.fromIndex(0);
    const second = ir.BlockId.fromIndex(1);
    const external = ir.BlockId.fromIndex(2);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = first, .function = function_id, .terminator = .{ .jump = .{ .target = second } } },
        .{ .id = second, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = second },
            .else_edge = .{ .target = first },
        } } },
        .{ .id = external, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = first },
            .else_edge = .{ .target = second },
        } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ first, second, external },
        .entry_block = external,
    }};
    const values = [_]ir.Value{.{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } }};
    const program: ir.Program = .{
        .program_id = "irreducible-primary-selection",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var first_incoming = [_]ir.CfgEdgeRef{.{ .source = external, .kind = .branch_then, .target = first }};
    var second_incoming = [_]ir.CfgEdgeRef{.{ .source = external, .kind = .branch_else, .target = second }};
    var entries = [_]irreducible_region.Entry{
        .{ .block = first, .incoming = &first_incoming, .is_function_entry = false },
        .{ .block = second, .incoming = &second_incoming, .is_function_entry = false },
    };
    var region_blocks = [_]ir.BlockId{ first, second };
    const region: irreducible_region.Region = .{ .blocks = &region_blocks, .entries = &entries };

    const selection = try selectPrimary(std.testing.allocator, &program, region);
    try std.testing.expectEqual(first, selection.block);
    try std.testing.expect(selection.refusal == null);
    try std.testing.expect(classifySecondary(&program, region, first, entries[1]) == null);

    var invalid_blocks = blocks;
    invalid_blocks[second.index()].id = external;
    var invalid_program = program;
    invalid_program.blocks = &invalid_blocks;
    const valid_fallback = try selectPrimary(std.testing.allocator, &invalid_program, region);
    try std.testing.expectEqual(first, valid_fallback.block);
    try std.testing.expect(valid_fallback.refusal == null);
}

test "primary selection preserves transition-shaped iteration headers on score ties" {
    const function_id = ir.FunctionId.fromIndex(0);
    const body = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const entry = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const transition_id = ir.InstructionId.fromIndex(0);
    const selector = ir.ValueId.fromIndex(0);
    const control = ir.ValueId.fromIndex(1);
    const limit = ir.ValueId.fromIndex(2);
    const step = ir.ValueId.fromIndex(3);
    const initial = ir.ValueId.fromIndex(4);
    const header_control = ir.ValueId.fromIndex(5);
    const header_limit = ir.ValueId.fromIndex(6);
    const header_step = ir.ValueId.fromIndex(7);
    const header_initial = ir.ValueId.fromIndex(8);
    const has_value = ir.ValueId.fromIndex(9);
    const normalized_limit = ir.ValueId.fromIndex(10);
    const normalized_step = ir.ValueId.fromIndex(11);
    const next_control = ir.ValueId.fromIndex(12);
    const arguments = [_]ir.ValueId{ control, limit, step, initial };
    const parameters = [_]ir.ValueId{ header_control, header_limit, header_step, header_initial };
    const blocks = [_]ir.Block{
        .{
            .id = body,
            .function = function_id,
            .terminator = .{ .jump = .{ .target = header, .arguments = &arguments } },
        },
        .{
            .id = header,
            .function = function_id,
            .parameters = &parameters,
            .instructions = &.{transition_id},
            .terminator = .{ .branch = .{
                .condition = has_value,
                .then_edge = .{ .target = body },
                .else_edge = .{ .target = exit },
            } },
        },
        .{
            .id = entry,
            .function = function_id,
            .terminator = .{ .branch = .{
                .condition = selector,
                .then_edge = .{ .target = body },
                .else_edge = .{ .target = header, .arguments = &arguments },
            } },
        },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, control, limit, step, initial },
        .blocks = &.{ body, header, entry, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = control, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = limit, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } },
        .{ .id = step, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 3 } },
        .{ .id = initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } },
        .{ .id = header_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = header_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
        .{ .id = header_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
        .{ .id = header_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 3 } } },
    };
    const base_instructions = [_]ir.Instruction{.{
        .id = transition_id,
        .block = header,
        .operation = .{ .numeric_for_next = .{
            .control = header_control,
            .limit = header_limit,
            .step = header_step,
            .initial = header_initial,
        } },
        .results = &.{ has_value, normalized_limit, normalized_step, next_control },
        .effects = .numeric_for_next,
    }};
    var program: ir.Program = .{
        .program_id = "iteration-header-primary-priority",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &base_instructions,
        .values = &values,
    };
    var body_incoming = [_]ir.CfgEdgeRef{.{ .source = entry, .kind = .branch_then, .target = body }};
    var header_incoming = [_]ir.CfgEdgeRef{.{ .source = entry, .kind = .branch_else, .target = header }};
    var entries = [_]irreducible_region.Entry{
        .{ .block = body, .incoming = &body_incoming, .is_function_entry = false },
        .{ .block = header, .incoming = &header_incoming, .is_function_entry = false },
    };
    var region_blocks = [_]ir.BlockId{ body, header };
    const region: irreducible_region.Region = .{ .blocks = &region_blocks, .entries = &entries };

    const numeric_selection = try selectPrimary(std.testing.allocator, &program, region);
    try std.testing.expectEqual(header, numeric_selection.block);

    var generic_instructions = base_instructions;
    generic_instructions[0].operation = .{ .generic_for_next = .{
        .iterator = header_control,
        .state = header_limit,
        .control = header_step,
        .initial = header_initial,
        .variable_count = 1,
    } };
    generic_instructions[0].effects = .generic_for_next;
    program.instructions = &generic_instructions;
    const generic_selection = try selectPrimary(std.testing.allocator, &program, region);
    try std.testing.expectEqual(header, generic_selection.block);
}
