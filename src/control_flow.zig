const std = @import("std");
const ir = @import("ir.zig");
const cfg_edge = @import("cfg_edge.zig");
const edge_path = @import("edge_path.zig");
const solver = @import("solver.zig");
const runtime_uses = @import("runtime_uses.zig");
const node_split = @import("node_split.zig");
const readable_scope = @import("readable_scope.zig");
const proof_digest = @import("proof_digest.zig");

pub const ApplyResult = struct {
    rewritten_blocks: usize = 0,
    specialized_edges: usize = 0,
    conflicting_certificate: ?usize = null,
};

pub const ForwardingPath = struct {
    edge: ir.Edge,
    blocks: []ir.BlockId,

    pub fn deinit(self: *ForwardingPath, allocator: std.mem.Allocator) void {
        if (self.edge.arguments.len != 0) allocator.free(self.edge.arguments);
        allocator.free(self.blocks);
        self.* = undefined;
    }
};

const EdgeDecision = struct {
    edge: ir.CfgEdgeRef,
    selection: union(enum) {
        proved: struct {
            truth: bool,
            certificate: ir.CertificateId,
        },
        inconsistent_context,
    },
};

const BranchDecision = struct {
    block: ir.BlockId,
    branch: ir.Branch,
    truth: bool,
    certificate: ir.CertificateId,
};

/// Return whether a solver-free readable program still needs the ordinary
/// proof/control pass for an exactly evaluable Boolean branch. This is only a
/// fast-path trigger. The resolver owns reachability, history, use safety,
/// and authenticated branch rewriting; doing those checks here would repeat
/// whole-program analysis once per candidate branch.
pub fn hasExactBranchTruth(program: *const ir.Program) bool {
    for (program.blocks) |block| {
        const branch = switch (block.terminator) {
            .branch => |value| value,
            else => continue,
        };
        if (branch.condition.index() >= program.values.len or
            program.values[branch.condition.index()].type.kind != .boolean)
        {
            continue;
        }
        switch (solver.evaluateValue(program, branch.condition)) {
            .boolean => return true,
            else => continue,
        }
    }
    return false;
}

pub fn applyProvedBranches(allocator: std.mem.Allocator, program: *ir.Program) !ApplyResult {
    const blocks = try allocator.alloc(ir.Block, program.blocks.len);
    var rewrites: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    try rewrites.appendSlice(allocator, program.edge_rewrites);
    const result = try applyProvedBranchesWithState(allocator, program, blocks, &rewrites);
    if (result.rewritten_blocks == 0 and result.specialized_edges == 0) {
        allocator.free(blocks);
        rewrites.deinit(allocator);
    }
    return result;
}

pub fn applyProvedBranchesWithState(
    allocator: std.mem.Allocator,
    program: *ir.Program,
    blocks: []ir.Block,
    rewrites: *std.ArrayList(ir.CfgEdgeRewrite),
) !ApplyResult {
    if (blocks.len != program.blocks.len) return error.InvalidBlockStorage;
    var scope = try readable_scope.Scope.init(allocator, program);
    defer scope.deinit();
    const global_value_facts = try allocator.alloc(?bool, program.values.len);
    defer allocator.free(global_value_facts);
    @memset(global_value_facts, null);
    var edge_decisions: std.ArrayList(EdgeDecision) = .empty;
    defer edge_decisions.deinit(allocator);
    var branch_decisions: std.ArrayList(BranchDecision) = .empty;
    defer branch_decisions.deinit(allocator);

    for (program.certificates, 0..) |certificate, certificate_index| {
        if (certificate.resolution != .proved or certificate.query.index() >= program.queries.len) continue;
        const query = program.queries[certificate.query.index()];
        direct_fact: {
            const fact = queryValueFact(program, query) orelse break :direct_fact;
            switch (edge_path.queryRoot(program, query)) {
                .one => |edge| {
                    const resolved_edge = edge_path.resolvedQueryEdge(program, query) orelse break :direct_fact;
                    const target_id = cfg_edge.target(program, resolved_edge) orelse break :direct_fact;
                    if (target_id.index() >= program.blocks.len) break :direct_fact;
                    const target = program.blocks[target_id.index()];
                    const branch = switch (target.terminator) {
                        .branch => |value| value,
                        else => break :direct_fact,
                    };
                    if (branch.condition != fact.value) break :direct_fact;
                    var duplicate = false;
                    for (edge_decisions.items) |*existing| {
                        if (!std.meta.eql(existing.edge, resolved_edge)) continue;
                        duplicate = true;
                        switch (existing.selection) {
                            .proved => |selection| if (selection.truth != fact.truth) {
                                existing.selection = .inconsistent_context;
                            },
                            .inconsistent_context => {},
                        }
                        break;
                    }
                    if (!duplicate) try edge_decisions.append(allocator, .{
                        .edge = resolved_edge,
                        .selection = .{ .proved = .{
                            .truth = fact.truth,
                            .certificate = certificate.id,
                        } },
                    });
                    _ = edge;
                    break :direct_fact;
                },
                .ambiguous => break :direct_fact,
                .none => if (recordValueFact(global_value_facts, fact)) return .{ .conflicting_certificate = certificate_index },
            }
        }

        for (program.obligations) |obligation| {
            const decision = provedControlBranchDecision(program, query, obligation, certificate) orelse continue;
            for (branch_decisions.items) |existing| {
                if (existing.block != decision.block or !sameBranch(existing.branch, decision.branch)) continue;
                if (existing.truth != decision.truth) return .{ .conflicting_certificate = certificate_index };
                break;
            } else try branch_decisions.append(allocator, decision);
        }
    }

    const original_rewrite_count = rewrites.items.len;
    var rewrite_count: usize = 0;
    var specialized_count: usize = 0;
    for (blocks, program.blocks) |*block, original| {
        block.* = original;
        if (!scope.block(original.id)) continue;
        switch (original.terminator) {
            .jump => |edge| {
                // A rewritten jump is still owned by its authenticated
                // lineage. Do not discover a new forwarding substitution on
                // that witness.
                if (isRewriteWitness(rewrites.items, original.id)) continue;
                const specialized = try specializeEdge(allocator, program, edge_decisions.items, rewrites.items, .{ .source = original.id, .kind = .jump, .target = edge.target }, edge);
                block.terminator = .{ .jump = specialized.edge };
                specialized_count += @intFromBool(specialized.changed);
                if (specialized.changed) try appendRewrite(allocator, rewrites, original.id, .jump, edge, specialized);
            },
            .branch => |branch| {
                if (branchDecisionFor(branch_decisions.items, original.id, branch)) |decision| {
                    block.terminator = .{ .jump = if (decision.truth) branch.then_edge else branch.else_edge };
                    rewrite_count += 1;
                    continue;
                }
                // An authenticated control decision is checked against the
                // historical branch above, so it may close a branch that is
                // also a split/fold witness. Only forwarding/edge discovery
                // remains prohibited for that lineage-owned block.
                if (isRewriteWitness(rewrites.items, original.id)) continue;
                var then_specialized = try specializeEdge(
                    allocator,
                    program,
                    edge_decisions.items,
                    rewrites.items,
                    .{ .source = original.id, .kind = .branch_then, .target = branch.then_edge.target },
                    branch.then_edge,
                );
                var else_specialized = try specializeEdge(
                    allocator,
                    program,
                    edge_decisions.items,
                    rewrites.items,
                    .{ .source = original.id, .kind = .branch_else, .target = branch.else_edge.target },
                    branch.else_edge,
                );
                retainIterationProtocolArm(allocator, program, original, branch, branch.then_edge, branch.else_edge, &then_specialized);
                retainIterationProtocolArm(allocator, program, original, branch, branch.else_edge, branch.then_edge, &else_specialized);
                specialized_count += @as(usize, @intFromBool(then_specialized.changed)) + @as(usize, @intFromBool(else_specialized.changed));
                if (then_specialized.changed) try appendRewrite(allocator, rewrites, original.id, .branch_then, branch.then_edge, then_specialized);
                if (else_specialized.changed) try appendRewrite(allocator, rewrites, original.id, .branch_else, branch.else_edge, else_specialized);
                block.terminator = .{ .branch = .{
                    .condition = branch.condition,
                    .then_edge = then_specialized.edge,
                    .else_edge = else_specialized.edge,
                } };
            },
            else => {},
        }
    }
    if (rewrite_count == 0 and specialized_count == 0) return .{};
    program.blocks = blocks;
    if (rewrites.items.len != original_rewrite_count) program.edge_rewrites = rewrites.items;
    return .{ .rewritten_blocks = rewrite_count, .specialized_edges = specialized_count };
}

fn retainIterationProtocolArm(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    header: ir.Block,
    branch: ir.Branch,
    incoming: ir.Edge,
    sibling: ir.Edge,
    specialized: *SpecializedEdge,
) void {
    if (!specialized.changed or specialized.rule != .forwarding_jump or
        specialized.edge.target != sibling.target or !isIterationProtocolBranch(program, header, branch)) return;
    if (specialized.edge.arguments.len != 0) allocator.free(specialized.edge.arguments);
    specialized.* = .{ .edge = incoming };
}

fn isIterationProtocolBranch(program: *const ir.Program, header: ir.Block, branch: ir.Branch) bool {
    if (header.instructions.len != 1) return false;
    const instruction_id = header.instructions[0];
    if (instruction_id.index() >= program.instructions.len) return false;
    const transition = program.instructions[instruction_id.index()];
    if (transition.id != instruction_id or transition.block != header.id or
        transition.results.len == 0 or transition.results[0] != branch.condition) return false;
    return switch (transition.operation) {
        .numeric_for_next, .generic_for_next => true,
        else => false,
    };
}

fn isRewriteWitness(rewrites: []const ir.CfgEdgeRewrite, block_id: ir.BlockId) bool {
    for (rewrites) |rewrite| {
        if (rewrite.from.target == block_id or
            ((rewrite.rule == .node_split or rewrite.rule == .clone_fold) and rewrite.to.target == block_id)) return true;
    }
    return false;
}

const SpecializedEdge = struct {
    edge: ir.Edge,
    changed: bool = false,
    rule: ir.EdgeRewriteRule = .proved_branch,
    certificate: ?ir.CertificateId = null,
};

fn specializeEdge(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    decisions: []const EdgeDecision,
    rewrites: []const ir.CfgEdgeRewrite,
    reference: ir.CfgEdgeRef,
    incoming: ir.Edge,
) !SpecializedEdge {
    const specialized = blk: {
        for (decisions) |decision| {
            if (!std.meta.eql(decision.edge, reference)) continue;
            switch (decision.selection) {
                .proved => |selection| {
                    var result = try specializeDispatchEdge(allocator, program, incoming, selection.truth);
                    if (result.changed) result.certificate = selection.certificate;
                    break :blk result;
                },
                .inconsistent_context => break :blk SpecializedEdge{ .edge = incoming },
            }
        }
        if (!try hasAuthenticatedPathConstraint(allocator, program, reference)) break :blk SpecializedEdge{ .edge = incoming };
        break :blk try specializeForwardingJump(allocator, program, incoming);
    };
    if (specialized.changed and targetWasVisited(rewrites, reference, specialized.edge.target)) {
        if (specialized.edge.arguments.len != 0) allocator.free(specialized.edge.arguments);
        return .{ .edge = incoming };
    }
    return specialized;
}

fn hasAuthenticatedPathConstraint(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    reference: ir.CfgEdgeRef,
) !bool {
    for (program.constraints) |constraint| {
        if (constraint.evidence.len == 0) continue;
        const path = try edge_path.pathForConstraintAlloc(allocator, program, constraint, reference) orelse continue;
        allocator.free(path);
        return true;
    }
    return false;
}

fn targetWasVisited(rewrites: []const ir.CfgEdgeRewrite, reference: ir.CfgEdgeRef, candidate: ir.BlockId) bool {
    if (candidate == reference.source or candidate == reference.target) return true;
    for (rewrites) |rewrite| {
        if (rewrite.source != reference.source or rewrite.kind != reference.kind) continue;
        if (rewrite.from.target == candidate or rewrite.to.target == candidate) return true;
    }
    return false;
}

fn specializeForwardingJump(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    incoming: ir.Edge,
) !SpecializedEdge {
    if (incoming.target.index() >= program.blocks.len) return .{ .edge = incoming };
    const forwarding = program.blocks[incoming.target.index()];
    if (incoming.arguments.len != forwarding.parameters.len) return .{ .edge = incoming };
    const outgoing = switch (forwarding.terminator) {
        .jump => |edge| edge,
        else => return .{ .edge = incoming },
    };
    if (outgoing.target == forwarding.id or outgoing.target.index() >= program.blocks.len) return .{ .edge = incoming };
    if (!try forwardingValuesAreLocal(allocator, program, forwarding)) return .{ .edge = incoming };

    const substitutions = try allocator.alloc(?ir.ValueId, program.values.len);
    defer allocator.free(substitutions);
    @memset(substitutions, null);
    for (program.values) |value| {
        if (value.id.index() >= substitutions.len or value.function != forwarding.function) continue;
        const available = switch (value.origin) {
            .parameter => true,
            .capture => |capture_id| capture_id.index() < program.captures.len and
                program.captures[capture_id.index()].function == forwarding.function and
                program.captures[capture_id.index()].kind == .immutable_value,
            else => false,
        };
        if (available) substitutions[value.id.index()] = value.id;
    }
    for (forwarding.parameters, incoming.arguments) |parameter, argument| {
        if (parameter.index() >= substitutions.len or argument.index() >= program.values.len) return .{ .edge = incoming };
        substitutions[parameter.index()] = argument;
    }
    for (forwarding.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return .{ .edge = incoming };
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or
            instruction.block != forwarding.id or
            instruction.results.len != 1 or
            instruction.pack_result != null or
            !solver.isExactPure(instruction.effects))
        {
            return .{ .edge = incoming };
        }
        const source = switch (instruction.operation) {
            .copy => |value_id| value_id,
            else => return .{ .edge = incoming },
        };
        const result = instruction.results[0];
        if (source.index() >= substitutions.len or result.index() >= substitutions.len) return .{ .edge = incoming };
        substitutions[result.index()] = substitutions[source.index()] orelse return .{ .edge = incoming };
    }
    if (outgoing.arguments.len == 0) return .{
        .edge = .{ .target = outgoing.target },
        .changed = true,
        .rule = .forwarding_jump,
    };

    const arguments = try allocator.alloc(ir.ValueId, outgoing.arguments.len);
    for (outgoing.arguments, 0..) |argument, index| {
        if (argument.index() >= substitutions.len) {
            allocator.free(arguments);
            return .{ .edge = incoming };
        }
        arguments[index] = substitutions[argument.index()] orelse {
            allocator.free(arguments);
            return .{ .edge = incoming };
        };
    }
    return .{
        .edge = .{ .target = outgoing.target, .arguments = arguments },
        .changed = true,
        .rule = .forwarding_jump,
    };
}

fn forwardingValuesAreLocal(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    forwarding: ir.Block,
) !bool {
    const aliases = try allocator.alloc(ir.ValueId, program.values.len);
    defer allocator.free(aliases);
    for (aliases, 0..) |*alias, index| alias.* = ir.ValueId.fromIndex(index);

    const excluded = try allocator.alloc(bool, program.instructions.len);
    defer allocator.free(excluded);
    @memset(excluded, false);
    var scope = try readable_scope.Scope.init(allocator, program);
    defer scope.deinit();
    var uses = try runtime_uses.Counts.initScopedIncludingBlock(
        allocator,
        program,
        &scope,
        aliases,
        excluded,
        forwarding.id,
    );
    defer uses.deinit();

    for (forwarding.parameters) |parameter| {
        if (parameter.index() >= uses.values.len or
            uses.values[parameter.index()] != blockValueUseCount(program, forwarding, parameter)) return false;
    }
    for (forwarding.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return false;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or instruction.block != forwarding.id) return false;
        for (instruction.results) |result| {
            if (result.index() >= uses.values.len or
                uses.values[result.index()] != blockValueUseCount(program, forwarding, result)) return false;
        }
    }
    return true;
}

fn blockValueUseCount(program: *const ir.Program, block: ir.Block, target: ir.ValueId) usize {
    var count: usize = 0;
    const visitor = ValueUseCounter{ .target = target, .count = &count };
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) continue;
        runtime_uses.visitOperationUses(program.instructions[instruction_id.index()].operation, visitor);
    }
    runtime_uses.visitTerminatorUses(block.terminator, visitor);
    return count;
}

fn specializeDispatchEdge(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    incoming: ir.Edge,
    truth: bool,
) !SpecializedEdge {
    if (incoming.target.index() >= program.blocks.len) return .{ .edge = incoming };
    const dispatch = program.blocks[incoming.target.index()];
    if (incoming.arguments.len != dispatch.parameters.len) return .{ .edge = incoming };
    const branch = switch (dispatch.terminator) {
        .branch => |value| value,
        else => return .{ .edge = incoming },
    };
    if (!try dispatcherInstructionsAreDroppable(allocator, program, dispatch, branch)) return .{ .edge = incoming };
    const selected = if (truth) branch.then_edge else branch.else_edge;
    if (selected.target == dispatch.id or selected.target.index() >= program.blocks.len) return .{ .edge = incoming };
    if (selected.arguments.len == 0) return .{ .edge = .{ .target = selected.target }, .changed = true };

    const arguments = try allocator.alloc(ir.ValueId, selected.arguments.len);
    for (selected.arguments, 0..) |argument, index| {
        const parameter_index = parameterIndex(dispatch.parameters, argument) orelse {
            allocator.free(arguments);
            return .{ .edge = incoming };
        };
        arguments[index] = incoming.arguments[parameter_index];
    }
    return .{ .edge = .{ .target = selected.target, .arguments = arguments }, .changed = true };
}

fn appendRewrite(
    allocator: std.mem.Allocator,
    rewrites: *std.ArrayList(ir.CfgEdgeRewrite),
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    incoming: ir.Edge,
    specialized: SpecializedEdge,
) !void {
    try rewrites.append(allocator, .{
        .id = ir.EdgeRewriteId.fromIndex(rewrites.items.len),
        .source = source,
        .kind = kind,
        .from = .{ .target = incoming.target, .arguments = try allocator.dupe(ir.ValueId, incoming.arguments) },
        .to = .{ .target = specialized.edge.target, .arguments = try allocator.dupe(ir.ValueId, specialized.edge.arguments) },
        .rule = specialized.rule,
        .certificate = specialized.certificate,
    });
}

pub fn replayQuerySpecialization(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    query: ir.SolverQuery,
    incoming: ir.Edge,
) !?ir.Edge {
    const reference = edge_path.resolvedQueryEdge(program, query) orelse return null;
    if (reference.target != incoming.target) return null;
    const fact = queryValueFact(program, query) orelse return null;
    if (incoming.target.index() >= program.blocks.len) return null;
    const branch = switch (program.blocks[incoming.target.index()].terminator) {
        .branch => |value| value,
        else => return null,
    };
    if (branch.condition != fact.value) return null;
    const specialized = try specializeDispatchEdge(allocator, program, incoming, fact.truth);
    return if (specialized.changed) specialized.edge else null;
}

pub fn replayForwardingJump(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    incoming: ir.Edge,
) !?ir.Edge {
    const specialized = try specializeForwardingJump(allocator, program, incoming);
    return if (specialized.changed) specialized.edge else null;
}

pub fn replayForwardingPathTo(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    incoming: ir.Edge,
    terminal: ir.BlockId,
) !?ForwardingPath {
    if (terminal.index() >= program.blocks.len or incoming.target == terminal) return null;

    const visited = try allocator.alloc(bool, program.blocks.len);
    defer allocator.free(visited);
    @memset(visited, false);
    var blocks: std.ArrayList(ir.BlockId) = .empty;
    defer blocks.deinit(allocator);

    var current = incoming;
    var owns_current = false;
    var completed = false;
    defer if (!completed and owns_current and current.arguments.len != 0) allocator.free(current.arguments);

    while (current.target != terminal) {
        if (current.target.index() >= program.blocks.len or visited[current.target.index()]) return null;
        visited[current.target.index()] = true;

        const specialized = try specializeForwardingJump(allocator, program, current);
        if (!specialized.changed) return null;
        blocks.append(allocator, current.target) catch |err| {
            if (specialized.edge.arguments.len != 0) allocator.free(specialized.edge.arguments);
            return err;
        };
        if (owns_current and current.arguments.len != 0) allocator.free(current.arguments);
        current = specialized.edge;
        owns_current = true;
    }

    const owned_blocks = try blocks.toOwnedSlice(allocator);
    completed = true;
    return .{ .edge = current, .blocks = owned_blocks };
}

pub fn replayNodeSplit(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    incoming: ir.Edge,
    clone_id: ir.BlockId,
    group: ?ir.NodeSplitGroupId,
) std.mem.Allocator.Error!?ir.Edge {
    if (group) |node_split_group| {
        return node_split.replayAllocForGroup(allocator, program, incoming, clone_id, node_split_group);
    }
    return node_split.replayAlloc(allocator, program, incoming, clone_id);
}

pub fn replayNodeSplitWithIndex(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    incoming: ir.Edge,
    clone_id: ir.BlockId,
    group: ?ir.NodeSplitGroupId,
    index: *const node_split.ReplayIndex,
) std.mem.Allocator.Error!?ir.Edge {
    if (group) |node_split_group| {
        return node_split.replayAllocForGroupWithIndex(
            allocator,
            program,
            incoming,
            clone_id,
            node_split_group,
            index,
        );
    }
    return node_split.replayAllocWithIndex(allocator, program, incoming, clone_id, index);
}

test "proof rewriting preserves node split source and clone witnesses" {
    const function_id = ir.FunctionId.fromIndex(0);
    const edge_source = ir.BlockId.fromIndex(0);
    const original = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = edge_source, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = clone },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = original, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = exit },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = clone, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = exit },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ edge_source, original, clone, exit },
        .entry_block = edge_source,
    }};
    const values = [_]ir.Value{.{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } }};
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = condition },
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    const certificates = [_]ir.SolverCertificate{.{
        .id = ir.CertificateId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .engine = .internal_facts,
        .resolution = .proved,
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = edge_source,
        .kind = .branch_then,
        .from = .{ .target = original },
        .to = .{ .target = clone },
        .rule = .node_split,
    }};
    var program: ir.Program = .{
        .program_id = "node-split-proof-witness",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
        .queries = &queries,
        .certificates = &certificates,
        .edge_rewrites = &rewrites,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const result = try applyProvedBranches(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 0), result.rewritten_blocks);
    try std.testing.expectEqual(std.meta.Tag(ir.Terminator).branch, std.meta.activeTag(program.blocks[edge_source.index()].terminator));
    try std.testing.expectEqual(std.meta.Tag(ir.Terminator).branch, std.meta.activeTag(program.blocks[original.index()].terminator));
    try std.testing.expectEqual(std.meta.Tag(ir.Terminator).branch, std.meta.activeTag(program.blocks[clone.index()].terminator));
}

fn dispatcherInstructionsAreDroppable(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    dispatch: ir.Block,
    branch: ir.Branch,
) !bool {
    const aliases = try allocator.alloc(ir.ValueId, program.values.len);
    defer allocator.free(aliases);
    for (aliases, 0..) |*alias, index| alias.* = ir.ValueId.fromIndex(index);

    const excluded = try allocator.alloc(bool, program.instructions.len);
    defer allocator.free(excluded);
    @memset(excluded, false);
    for (dispatch.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return false;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or
            instruction.block != dispatch.id or
            instruction.results.len != 1 or
            instruction.pack_result != null or
            !solver.isExactPure(instruction.effects))
        {
            return false;
        }
        excluded[instruction_id.index()] = true;
    }

    var scope = try readable_scope.Scope.init(allocator, program);
    defer scope.deinit();
    var uses = try runtime_uses.Counts.initScopedIncludingBlock(allocator, program, &scope, aliases, excluded, dispatch.id);
    defer uses.deinit();
    for (dispatch.parameters) |parameter| {
        if (parameter.index() >= uses.values.len) return false;
        if (uses.values[parameter.index()] != terminatorValueUseCount(dispatch.terminator, parameter)) return false;
    }
    for (dispatch.instructions) |instruction_id| {
        const result = program.instructions[instruction_id.index()].results[0];
        if (result.index() >= uses.values.len) return false;
        const allowed_uses: usize = @intFromBool(result == branch.condition);
        if (uses.values[result.index()] != allowed_uses) return false;
    }
    return true;
}

fn terminatorValueUseCount(terminator: ir.Terminator, target: ir.ValueId) usize {
    var count: usize = 0;
    runtime_uses.visitTerminatorUses(terminator, ValueUseCounter{ .target = target, .count = &count });
    return count;
}

const ValueUseCounter = struct {
    target: ir.ValueId,
    count: *usize,

    pub fn value(self: ValueUseCounter, value_id: ir.ValueId) void {
        self.count.* += @intFromBool(value_id == self.target);
    }

    pub fn pack(_: ValueUseCounter, _: ir.ValuePackId) void {}
    pub fn place(_: ValueUseCounter, _: ir.PlaceId) void {}
};

fn parameterIndex(parameters: []const ir.ValueId, value_id: ir.ValueId) ?usize {
    for (parameters, 0..) |parameter, index| if (parameter == value_id) return index;
    return null;
}

pub const ValueFact = struct {
    value: ir.ValueId,
    truth: bool,
};

pub fn queryValueFact(program: *const ir.Program, query: ir.SolverQuery) ?ValueFact {
    if (query.goal.index() >= program.solver_terms.len) return null;
    const asserted_truth = switch (query.kind) {
        .prove_true => true,
        .prove_false, .prove_unreachable => false,
        .prove_equivalent, .find_model => return null,
    };
    return switch (program.solver_terms[query.goal.index()].operation) {
        .logical_not => |operand| blk: {
            break :blk termValueFact(program, operand, !asserted_truth);
        },
        else => termValueFact(program, query.goal, asserted_truth),
    };
}

fn recordValueFact(value_facts: []?bool, fact: ValueFact) bool {
    if (fact.value.index() >= value_facts.len) return false;
    if (value_facts[fact.value.index()]) |existing| return existing != fact.truth;
    value_facts[fact.value.index()] = fact.truth;
    return false;
}

fn termValueFact(program: *const ir.Program, term_id: ir.SolverTermId, truth: bool) ?ValueFact {
    if (term_id.index() >= program.solver_terms.len) return null;
    return switch (program.solver_terms[term_id.index()].operation) {
        .value => |value_id| .{ .value = value_id, .truth = truth },
        .value_definition => |definition| .{ .value = definition.value, .truth = truth },
        .dynamic_truthiness => |operand| blk: {
            if (operand.index() >= program.solver_terms.len) break :blk null;
            break :blk switch (program.solver_terms[operand.index()].operation) {
                .value => |value_id| .{ .value = value_id, .truth = truth },
                else => null,
            };
        },
        else => null,
    };
}

fn provedControlBranchDecision(
    program: *const ir.Program,
    query: ir.SolverQuery,
    obligation: ir.Obligation,
    certificate: ir.SolverCertificate,
) ?BranchDecision {
    if (obligation.query == null or obligation.query.? != query.id or
        obligation.certificate == null or obligation.certificate.? != certificate.id) return null;
    const replay = replayControlBranchObligation(program, obligation) orelse return null;
    if (replay.certificate != certificate.id or replay.subject.block.index() >= program.blocks.len) return null;
    const live = switch (program.blocks[replay.subject.block.index()].terminator) {
        .branch => |branch| branch,
        else => return null,
    };
    if (!branchMatchesHistoricalSubject(program, replay.subject.block, live, replay.subject.branch)) return null;
    return .{
        .block = replay.subject.block,
        .branch = live,
        .truth = replay.truth,
        .certificate = replay.certificate,
    };
}

pub const ControlBranchReplay = struct {
    subject: ir.ControlBranchSubject,
    selected: ir.Edge,
    truth: bool,
    certificate: ir.CertificateId,
};

pub fn replayControlBranchObligation(program: *const ir.Program, obligation: ir.Obligation) ?ControlBranchReplay {
    if (obligation.kind != .control_structure or
        obligation.status != .discharged or
        obligation.query == null or
        obligation.certificate == null or
        obligation.evidence.len == 0 or
        obligation.query.?.index() >= program.queries.len or
        obligation.certificate.?.index() >= program.certificates.len)
    {
        return null;
    }
    const subject = switch (obligation.subject) {
        .control_branch => |value| value,
        else => return null,
    };
    if (subject.block.index() >= program.blocks.len or
        subject.branch.condition.index() >= program.values.len or
        program.blocks[subject.block.index()].id != subject.block or
        program.values[subject.branch.condition.index()].id != subject.branch.condition)
    {
        return null;
    }
    const query = program.queries[obligation.query.?.index()];
    const certificate = program.certificates[obligation.certificate.?.index()];
    if (query.id != obligation.query.? or
        certificate.id != obligation.certificate.? or
        certificate.query != query.id or
        certificate.resolution != .proved or
        certificate.certificate_digest == null or
        !proof_digest.isControlBranchDigest(certificate.certificate_digest.?) or
        !evidenceCovers(certificate.evidence, obligation.evidence) or
        query.goal.index() >= program.solver_terms.len)
    {
        return null;
    }
    switch (edge_path.queryRoot(program, query)) {
        .none => {},
        .one, .ambiguous => return null,
    }
    const asserted_truth = switch (query.kind) {
        .prove_true => true,
        .prove_false => false,
        .prove_equivalent, .prove_unreachable, .find_model => return null,
    };
    const semantic_truth = if (queryValueFact(program, query)) |fact| blk: {
        if (fact.value != subject.branch.condition) return null;
        break :blk fact.truth;
    } else blk: {
        const goal = program.solver_terms[query.goal.index()];
        if (goal.sort.kind != .boolean) return null;
        const literal_truth = switch (goal.operation) {
            .boolean_literal => |truth| truth,
            else => return null,
        };
        const known_truth = program.values[subject.branch.condition.index()].type.knownLuauTruthiness() orelse return null;
        if (literal_truth != asserted_truth or known_truth != asserted_truth) return null;
        break :blk known_truth;
    };
    if (semantic_truth != asserted_truth) return null;
    return .{
        .subject = subject,
        .selected = if (asserted_truth) subject.branch.then_edge else subject.branch.else_edge,
        .truth = asserted_truth,
        .certificate = certificate.id,
    };
}

fn branchDecisionFor(decisions: []const BranchDecision, block: ir.BlockId, branch: ir.Branch) ?BranchDecision {
    for (decisions) |decision| {
        if (decision.block == block and sameBranch(decision.branch, branch)) return decision;
    }
    return null;
}

fn branchMatchesHistoricalSubject(
    program: *const ir.Program,
    source: ir.BlockId,
    live: ir.Branch,
    historical: ir.Branch,
) bool {
    if (live.condition != historical.condition) return false;
    const historical_then = reverseEdgeHistory(program, source, .branch_then, live.then_edge) orelse return false;
    const historical_else = reverseEdgeHistory(program, source, .branch_else, live.else_edge) orelse return false;
    return edge_path.sameEdge(historical_then, historical.then_edge) and
        edge_path.sameEdge(historical_else, historical.else_edge);
}

fn reverseEdgeHistory(
    program: *const ir.Program,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    live: ir.Edge,
) ?ir.Edge {
    var current = live;
    var index = program.edge_rewrites.len;
    while (index != 0) {
        index -= 1;
        const rewrite = program.edge_rewrites[index];
        if (rewrite.source != source or rewrite.kind != kind) continue;
        if (!edge_path.sameEdge(rewrite.to, current)) return null;
        current = rewrite.from;
    }
    return current;
}

pub fn sameBranch(left: ir.Branch, right: ir.Branch) bool {
    return left.condition == right.condition and
        edge_path.sameEdge(left.then_edge, right.then_edge) and
        edge_path.sameEdge(left.else_edge, right.else_edge);
}

fn evidenceCovers(available: []const ir.EvidenceId, required: []const ir.EvidenceId) bool {
    for (required) |required_id| {
        for (available) |available_id| {
            if (available_id == required_id) break;
        } else return false;
    }
    return true;
}
