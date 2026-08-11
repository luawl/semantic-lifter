const std = @import("std");
const ir = @import("ir.zig");

/// A literal boolean is trusted only when its value identity points at the
/// single pure constant instruction that produces it.
pub fn isBooleanLiteral(program: *const ir.Program, value_id: ir.ValueId, expected: bool) bool {
    if (value_id.index() >= program.values.len) return false;
    const origin = switch (program.values[value_id.index()].origin) {
        .instruction_result => |value| value,
        else => return false,
    };
    if (origin.index != 0 or origin.instruction.index() >= program.instructions.len) return false;
    const instruction = program.instructions[origin.instruction.index()];
    if (instruction.id != origin.instruction or instruction.results.len != 1 or
        instruction.results[0] != value_id or instruction.pack_result != null or
        !std.meta.eql(instruction.effects, ir.EffectSummary.pure))
    {
        return false;
    }
    return switch (instruction.operation) {
        .constant => |literal| switch (literal) {
            .boolean => |value| value == expected,
            else => false,
        },
        else => false,
    };
}

/// The internal state of a proven iteration transition is ordered as
/// `[next_control, normalized_limit, normalized_step, false]`.
pub fn transitionStateMatches(
    program: *const ir.Program,
    transition: ir.Instruction,
    arguments: []const ir.ValueId,
) bool {
    if (arguments.len != 4 or !isBooleanLiteral(program, arguments[3], false)) return false;
    return switch (transition.operation) {
        .numeric_for_next => transition.results.len == 4 and
            arguments[0] == transition.results[3] and
            arguments[1] == transition.results[1] and
            arguments[2] == transition.results[2],
        .generic_for_next => transition.results.len >= 4 and
            arguments[0] == transition.results[1] and
            arguments[1] == transition.results[2] and
            arguments[2] == transition.results[3],
        else => false,
    };
}

pub const NumericHeaderReentryCandidate = struct {
    ancestor: ir.BlockId,
    has_direct_incoming: bool,
};

/// Validate the semantic part of a loop re-entry without comparing the
/// iteration's changing SSA identities.  The caller owns authentication of
/// any node-split edge that may have replaced the direct incoming edge.
pub fn numericHeaderReentryCandidate(
    program: *const ir.Program,
    block: ir.Block,
    expected: []const ir.ValueId,
    arguments: []const ir.ValueId,
) ?NumericHeaderReentryCandidate {
    if (block.parameters.len != 4 or block.instructions.len != 1 or
        expected.len != 4 or arguments.len != 4)
    {
        return null;
    }
    const transition_id = block.instructions[0];
    if (transition_id.index() >= program.instructions.len) return null;
    const transition = program.instructions[transition_id.index()];
    if (transition.id != transition_id or transition.block != block.id or transition.results.len != 4) return null;
    const operation = switch (transition.operation) {
        .numeric_for_next => |value| value,
        else => return null,
    };
    if (operation.control != block.parameters[0] or operation.limit != block.parameters[1] or
        operation.step != block.parameters[2] or operation.initial != block.parameters[3])
    {
        return null;
    }
    if (!transitionStateMatches(program, transition, arguments)) return null;

    if (std.mem.eql(ir.ValueId, expected, arguments)) {
        return .{ .ancestor = block.id, .has_direct_incoming = true };
    }

    const ancestor_id = numericHeaderAncestor(program, block.id) orelse return null;
    const ancestor = program.blocks[ancestor_id.index()];
    const ancestor_transition = numericHeaderTransition(program, ancestor) orelse return null;
    const ancestor_operation = ancestor_transition.operation.numeric_for_next;
    if (ancestor_operation.mode != operation.mode) return null;
    return .{
        .ancestor = ancestor_id,
        .has_direct_incoming = hasIncomingEdgeWithArguments(program, ancestor, expected),
    };
}

/// Recognize a loop re-entry without comparing the iteration's changing SSA
/// identities. The header contract, the transition's own result tuple, and
/// the forwarding edge that connects the two entry tuples are all required.
/// This direct form is retained for small standalone callers; structured
/// callers use `numericHeaderReentryCandidate` plus their rewrite-history
/// proof.
pub fn numericHeaderReentryMatches(
    program: *const ir.Program,
    block: ir.Block,
    expected: []const ir.ValueId,
    arguments: []const ir.ValueId,
) bool {
    const candidate = numericHeaderReentryCandidate(program, block, expected, arguments) orelse return false;
    return candidate.has_direct_incoming;
}

fn numericHeaderAncestor(
    program: *const ir.Program,
    target_id: ir.BlockId,
) ?ir.BlockId {
    if (target_id.index() >= program.blocks.len or program.blocks[target_id.index()].id != target_id) return null;
    var current = target_id;
    var depth: usize = 0;
    while (depth <= program.blocks.len) : (depth += 1) {
        var parent: ?ir.BlockId = null;
        const current_block = program.blocks[current.index()];
        for (program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.to.target != current or rewrite.from.target == current) continue;
            if (rewrite.from.target.index() >= program.blocks.len) return null;
            const source = program.blocks[rewrite.from.target.index()];
            if (source.id != rewrite.from.target or source.function != current_block.function) return null;
            if (parent) |existing| {
                if (existing != rewrite.from.target) return null;
            } else {
                parent = rewrite.from.target;
            }
        }
        if (parent == null) return current;
        current = parent.?;
    }
    return null;
}

fn numericHeaderTransition(program: *const ir.Program, block: ir.Block) ?ir.Instruction {
    if (block.id.index() >= program.blocks.len or block.parameters.len != 4 or block.instructions.len != 1) return null;
    const transition_id = block.instructions[0];
    if (transition_id.index() >= program.instructions.len) return null;
    const transition = program.instructions[transition_id.index()];
    if (transition.id != transition_id or transition.block != block.id or transition.results.len != 4) return null;
    const operation = switch (transition.operation) {
        .numeric_for_next => |value| value,
        else => return null,
    };
    if (operation.control != block.parameters[0] or operation.limit != block.parameters[1] or
        operation.step != block.parameters[2] or operation.initial != block.parameters[3])
    {
        return null;
    }
    return transition;
}

fn hasIncomingEdgeWithArguments(
    program: *const ir.Program,
    target: ir.Block,
    arguments: []const ir.ValueId,
) bool {
    for (program.blocks) |source| {
        if (source.function != target.function) continue;
        const edges: [2]?ir.Edge = switch (source.terminator) {
            .jump => |edge| .{ edge, null },
            .branch => |branch| .{ branch.then_edge, branch.else_edge },
            else => .{ null, null },
        };
        for (edges) |maybe_edge| {
            const edge = maybe_edge orelse continue;
            if (edge.target == target.id and std.mem.eql(ir.ValueId, edge.arguments, arguments)) return true;
        }
    }
    return false;
}

const test_fixture = struct {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const header_id = ir.BlockId.fromIndex(1);
    const false_instruction = ir.InstructionId.fromIndex(0);
    const transition_instruction = ir.InstructionId.fromIndex(1);
    const forwarding_id = ir.BlockId.fromIndex(2);
    const control = ir.ValueId.fromIndex(0);
    const limit = ir.ValueId.fromIndex(1);
    const step = ir.ValueId.fromIndex(2);
    const initial = ir.ValueId.fromIndex(3);
    const false_value = ir.ValueId.fromIndex(4);
    const has_value = ir.ValueId.fromIndex(5);
    const normalized_limit = ir.ValueId.fromIndex(6);
    const normalized_step = ir.ValueId.fromIndex(7);
    const next_control = ir.ValueId.fromIndex(8);
    const forwarded_control = ir.ValueId.fromIndex(9);
    const forwarded_limit = ir.ValueId.fromIndex(10);
    const forwarded_step = ir.ValueId.fromIndex(11);
    const forwarded_initial = ir.ValueId.fromIndex(12);

    const values = [_]ir.Value{
        .{ .id = control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header_id, .index = 0 } } },
        .{ .id = limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header_id, .index = 1 } } },
        .{ .id = step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header_id, .index = 2 } } },
        .{ .id = initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = header_id, .index = 3 } } },
        .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 3 } } },
        .{ .id = forwarded_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = forwarding_id, .index = 0 } } },
        .{ .id = forwarded_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = forwarding_id, .index = 1 } } },
        .{ .id = forwarded_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = forwarding_id, .index = 2 } } },
        .{ .id = forwarded_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = forwarding_id, .index = 3 } } },
    };

    const instructions = [_]ir.Instruction{
        .{ .id = false_instruction, .block = entry_id, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = transition_instruction, .block = header_id, .operation = .{ .numeric_for_next = .{
            .control = control,
            .limit = limit,
            .step = step,
            .initial = initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ has_value, normalized_limit, normalized_step, next_control }, .effects = .numeric_for_next },
    };

    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .instructions = &.{false_instruction}, .terminator = .{ .jump = .{ .target = forwarding_id, .arguments = &.{ next_control, normalized_limit, normalized_step, false_value } } } },
        .{ .id = header_id, .function = function_id, .parameters = &.{ control, limit, step, initial }, .instructions = &.{transition_instruction}, .terminator = .{ .return_values = &.{} } },
        .{ .id = forwarding_id, .function = function_id, .parameters = &.{ forwarded_control, forwarded_limit, forwarded_step, forwarded_initial }, .terminator = .{ .jump = .{ .target = header_id, .arguments = &.{ forwarded_control, forwarded_limit, forwarded_step, forwarded_initial } } } },
    };

    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ entry_id, header_id, forwarding_id },
        .entry_block = entry_id,
    }};

    const program: ir.Program = .{
        .program_id = "iteration-state-projection",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
};

test "numeric header accepts its authenticated normalized reentry" {
    try std.testing.expect(numericHeaderReentryMatches(
        &test_fixture.program,
        test_fixture.blocks[test_fixture.header_id.index()],
        &.{ test_fixture.forwarded_control, test_fixture.forwarded_limit, test_fixture.forwarded_step, test_fixture.forwarded_initial },
        &.{ test_fixture.next_control, test_fixture.normalized_limit, test_fixture.normalized_step, test_fixture.false_value },
    ));
}

test "numeric header rejects arbitrary or mismatched reentry state" {
    const header = test_fixture.blocks[test_fixture.header_id.index()];
    try std.testing.expect(!numericHeaderReentryMatches(
        &test_fixture.program,
        header,
        &.{ test_fixture.forwarded_control, test_fixture.forwarded_limit, test_fixture.forwarded_step, test_fixture.forwarded_initial },
        &.{ test_fixture.control, test_fixture.normalized_limit, test_fixture.normalized_step, test_fixture.false_value },
    ));

    var changed_header = header;
    changed_header.parameters = &.{ test_fixture.limit, test_fixture.control, test_fixture.step, test_fixture.initial };
    try std.testing.expect(!numericHeaderReentryMatches(
        &test_fixture.program,
        changed_header,
        &.{ test_fixture.forwarded_control, test_fixture.forwarded_limit, test_fixture.forwarded_step, test_fixture.forwarded_initial },
        &.{ test_fixture.next_control, test_fixture.normalized_limit, test_fixture.normalized_step, test_fixture.false_value },
    ));

    var changed_instructions = test_fixture.instructions;
    changed_instructions[test_fixture.transition_instruction.index()].operation = .{ .copy = test_fixture.control };
    var changed_program = test_fixture.program;
    changed_program.instructions = &changed_instructions;
    try std.testing.expect(!numericHeaderReentryMatches(
        &changed_program,
        header,
        &.{ test_fixture.forwarded_control, test_fixture.forwarded_limit, test_fixture.forwarded_step, test_fixture.forwarded_initial },
        &.{ test_fixture.next_control, test_fixture.normalized_limit, test_fixture.normalized_step, test_fixture.false_value },
    ));

    var changed_blocks = test_fixture.blocks;
    changed_blocks[test_fixture.forwarding_id.index()].terminator = .{ .jump = .{ .target = test_fixture.header_id, .arguments = &.{
        test_fixture.control,
        test_fixture.normalized_limit,
        test_fixture.normalized_step,
        test_fixture.false_value,
    } } };
    var changed_edge_program = test_fixture.program;
    changed_edge_program.blocks = &changed_blocks;
    try std.testing.expect(!numericHeaderReentryMatches(
        &changed_edge_program,
        header,
        &.{ test_fixture.forwarded_control, test_fixture.forwarded_limit, test_fixture.forwarded_step, test_fixture.forwarded_initial },
        &.{ test_fixture.next_control, test_fixture.normalized_limit, test_fixture.normalized_step, test_fixture.false_value },
    ));
}
