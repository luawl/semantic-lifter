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

test "authenticated branch decisions may close a split witness block" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const witness_id = ir.BlockId.fromIndex(1);
    const clone_id = ir.BlockId.fromIndex(2);
    const exit_id = ir.BlockId.fromIndex(3);
    const condition_id = ir.ValueId.fromIndex(0);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const query_id = ir.QueryId.fromIndex(0);
    const certificate_id = ir.CertificateId.fromIndex(0);
    const branch: ir.Branch = .{
        .condition = condition_id,
        .then_edge = .{ .target = exit_id },
        .else_edge = .{ .target = clone_id },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .jump = .{ .target = witness_id } } },
        .{ .id = witness_id, .function = function_id, .terminator = .{ .branch = branch } },
        .{ .id = clone_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = exit_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .parameters = &.{condition_id},
        .blocks = &.{ entry_id, witness_id, clone_id, exit_id },
        .entry_block = entry_id,
    };
    const values = [_]ir.Value{.{
        .id = condition_id,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .frontend_proof,
        .locator = "fixture:authenticated-branch-witness",
    }};
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = condition_id },
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = query_id,
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    const certificates = [_]ir.SolverCertificate{.{
        .id = certificate_id,
        .query = query_id,
        .engine = .internal_facts,
        .resolution = .proved,
        .evidence = &.{evidence_id},
        .certificate_digest = proof_digest.control_branch_prefix ++ "fixture",
    }};
    const obligations = [_]ir.Obligation{.{
        .id = ir.ObligationId.fromIndex(0),
        .kind = .control_structure,
        .subject = .{ .control_branch = .{ .block = witness_id, .branch = branch } },
        .status = .discharged,
        .blocks_profile = .readable_luau,
        .detail = "authenticated branch witness",
        .evidence = &.{evidence_id},
        .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
        .query = query_id,
        .certificate = certificate_id,
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = entry_id,
        .kind = .jump,
        .from = .{ .target = witness_id },
        .to = .{ .target = clone_id },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    var program: ir.Program = .{
        .program_id = "authenticated-branch-witness",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
        .solver_terms = &terms,
        .queries = &queries,
        .certificates = &certificates,
        .edge_rewrites = &rewrites,
        .obligations = &obligations,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const result = try applyProvedBranches(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 1), result.rewritten_blocks);
    try std.testing.expectEqual(exit_id, program.blocks[witness_id.index()].terminator.jump.target);
    try std.testing.expectEqual(@as(usize, 1), program.edge_rewrites.len);
    try std.testing.expectEqual(ir.EdgeRewriteRule.node_split, program.edge_rewrites[0].rule);
}

test "proved values do not rewrite unreachable branches" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const dead_branch_id = ir.BlockId.fromIndex(1);
    const dead_then_id = ir.BlockId.fromIndex(2);
    const dead_else_id = ir.BlockId.fromIndex(3);
    const condition_id = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = dead_branch_id, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition_id,
            .then_edge = .{ .target = dead_then_id },
            .else_edge = .{ .target = dead_else_id },
        } } },
        .{ .id = dead_then_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = dead_else_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .parameters = &.{condition_id},
        .entry_block = entry_id,
        .blocks = &.{ entry_id, dead_branch_id, dead_then_id, dead_else_id },
    };
    const values = [_]ir.Value{.{
        .id = condition_id,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = condition_id },
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
    var program: ir.Program = .{
        .program_id = "unreachable-proved-branch",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .solver_terms = &terms,
        .queries = &queries,
        .certificates = &certificates,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const result = try applyProvedBranches(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 0), result.rewritten_blocks);
    try std.testing.expectEqual(std.meta.Tag(ir.Terminator).branch, std.meta.activeTag(program.blocks[dead_branch_id.index()].terminator));
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

test "proved Boolean value queries cannot select a global CFG edge without a control witness" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_is_negative.index()].operation = .{ .constant = .{ .boolean = true } };
    const terms = [_]ir.SolverTerm{
        .{
            .id = ir.SolverTermId.fromIndex(0),
            .sort = .{ .kind = .boolean },
            .operation = .{ .boolean_literal = true },
        },
        .{
            .id = ir.SolverTermId.fromIndex(1),
            .sort = .{ .kind = .boolean },
            .operation = .{ .value_definition = .{
                .value = fixture.v_is_negative,
                .expression = ir.SolverTermId.fromIndex(0),
            } },
        },
    };
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(1),
    }};
    const certificates = [_]ir.SolverCertificate{.{
        .id = ir.CertificateId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .engine = .internal_facts,
        .resolution = .proved,
    }};
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.certificates = &certificates;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const result = try applyProvedBranches(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 0), result.rewritten_blocks);
    try std.testing.expect(program.blocks[fixture.b_entry.index()].terminator == .branch);
}

test "proved dynamic truthiness queries cannot select global CFG edges without control witnesses" {
    const fixture = @import("fixtures.zig").dynamic_truthiness_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_truthy_condition } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(0) } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_falsy_condition } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .dynamic_truthiness = ir.SolverTermId.fromIndex(2) } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .boolean }, .operation = .{ .logical_not = ir.SolverTermId.fromIndex(3) } },
    };
    const queries = [_]ir.SolverQuery{
        .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(1) },
        .{ .id = ir.QueryId.fromIndex(1), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(4) },
    };
    const certificates = [_]ir.SolverCertificate{
        .{ .id = ir.CertificateId.fromIndex(0), .query = ir.QueryId.fromIndex(0), .engine = .internal_facts, .resolution = .proved },
        .{ .id = ir.CertificateId.fromIndex(1), .query = ir.QueryId.fromIndex(1), .engine = .internal_facts, .resolution = .proved },
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.certificates = &certificates;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const result = try applyProvedBranches(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 0), result.rewritten_blocks);
    try std.testing.expect(program.blocks[fixture.b_truthy_entry.index()].terminator == .branch);
    try std.testing.expect(program.blocks[fixture.b_falsy_entry.index()].terminator == .branch);
}

test "scalar obligations preserve branch identity across shared proof work" {
    const function_id = ir.FunctionId.fromIndex(0);
    const first_id = ir.BlockId.fromIndex(0);
    const bypass_id = ir.BlockId.fromIndex(1);
    const second_id = ir.BlockId.fromIndex(2);
    const then_id = ir.BlockId.fromIndex(3);
    const else_id = ir.BlockId.fromIndex(4);
    const effect_id = ir.InstructionId.fromIndex(0);
    const first_condition = ir.ValueId.fromIndex(0);
    const second_condition = ir.ValueId.fromIndex(1);
    const first_evidence = ir.EvidenceId.fromIndex(0);
    const second_evidence = ir.EvidenceId.fromIndex(1);
    const query_id = ir.QueryId.fromIndex(0);
    const certificate_id = ir.CertificateId.fromIndex(0);
    const evidence = [_]ir.Evidence{
        .{ .id = first_evidence, .kind = .dynamic_fixture, .locator = "fixture:scalar-first-branch" },
        .{ .id = second_evidence, .kind = .dynamic_fixture, .locator = "fixture:scalar-second-branch" },
    };
    const values = [_]ir.Value{
        .{
            .id = first_condition,
            .function = function_id,
            .type = .string,
            .origin = .{ .instruction_result = .{ .instruction = effect_id, .index = 0 } },
        },
        .{ .id = second_condition, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = effect_id,
        .block = first_id,
        .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "effectful_condition" } },
        .results = &.{first_condition},
        .effects = .semantic_environment_read,
        .evidence = &.{first_evidence},
    }};
    const first_branch: ir.Branch = .{
        .condition = first_condition,
        .then_edge = .{ .target = second_id },
        .else_edge = .{ .target = bypass_id },
    };
    const second_branch: ir.Branch = .{
        .condition = second_condition,
        .then_edge = .{ .target = then_id },
        .else_edge = .{ .target = else_id },
    };
    const blocks = [_]ir.Block{
        .{
            .id = first_id,
            .function = function_id,
            .instructions = &.{effect_id},
            .terminator = .{ .branch = first_branch },
            .evidence = &.{first_evidence},
        },
        .{ .id = bypass_id, .function = function_id, .terminator = .{ .jump = .{ .target = second_id } } },
        .{
            .id = second_id,
            .function = function_id,
            .terminator = .{ .branch = second_branch },
            .evidence = &.{second_evidence},
        },
        .{ .id = then_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = else_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{second_condition},
        .blocks = &.{ first_id, bypass_id, second_id, then_id, else_id },
        .entry_block = first_id,
        .evidence = &.{second_evidence},
    }};
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const queries = [_]ir.SolverQuery{.{ .id = query_id, .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(0) }};
    const certificates = [_]ir.SolverCertificate{.{
        .id = certificate_id,
        .query = query_id,
        .engine = .internal_facts,
        .resolution = .proved,
        .evidence = &.{ first_evidence, second_evidence },
        .certificate_digest = proof_digest.control_branch_prefix ++ "fixture",
    }};
    const obligations = [_]ir.Obligation{
        .{
            .id = ir.ObligationId.fromIndex(0),
            .kind = .control_structure,
            .subject = .{ .control_branch = .{ .block = first_id, .branch = first_branch } },
            .status = .discharged,
            .blocks_profile = .readable_luau,
            .detail = "first scalar branch",
            .evidence = &.{first_evidence},
            .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
            .query = query_id,
            .certificate = certificate_id,
        },
        .{
            .id = ir.ObligationId.fromIndex(1),
            .kind = .control_structure,
            .subject = .{ .control_branch = .{ .block = second_id, .branch = second_branch } },
            .status = .discharged,
            .blocks_profile = .readable_luau,
            .detail = "second scalar branch",
            .evidence = &.{second_evidence},
            .requirement = ir.ObligationRequirement.fromQuery(queries[0]),
            .query = query_id,
            .certificate = certificate_id,
        },
    };
    const base: ir.Program = .{
        .program_id = "shared-scalar-truthiness-proof",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
        .solver_terms = &terms,
        .queries = &queries,
        .certificates = &certificates,
        .obligations = &obligations,
    };

    {
        var program = base;
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const result = try applyProvedBranches(arena.allocator(), &program);
        try std.testing.expectEqual(@as(usize, 2), result.rewritten_blocks);
        try std.testing.expectEqual(second_id, program.blocks[first_id.index()].terminator.jump.target);
        try std.testing.expectEqual(then_id, program.blocks[second_id.index()].terminator.jump.target);
        try std.testing.expectEqualSlices(ir.InstructionId, &.{effect_id}, program.blocks[first_id.index()].instructions);
    }
    {
        var insufficient_certificates = certificates;
        insufficient_certificates[0].evidence = &.{first_evidence};
        var program = base;
        program.certificates = &insufficient_certificates;
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const result = try applyProvedBranches(arena.allocator(), &program);
        try std.testing.expectEqual(@as(usize, 1), result.rewritten_blocks);
        try std.testing.expect(program.blocks[second_id.index()].terminator == .branch);
    }
    {
        const constraints = [_]ir.Constraint{
            .{
                .id = ir.ConstraintId.fromIndex(0),
                .predicate = ir.SolverTermId.fromIndex(0),
                .evidence = &.{first_evidence},
                .scope = .{ .edge = .{ .source = first_id, .kind = .branch_then, .target = second_id } },
            },
            .{
                .id = ir.ConstraintId.fromIndex(1),
                .predicate = ir.SolverTermId.fromIndex(0),
                .evidence = &.{first_evidence},
                .scope = .{ .edge = .{ .source = first_id, .kind = .branch_else, .target = bypass_id } },
            },
        };
        var program = base;
        program.constraints = &constraints;
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const result = try applyProvedBranches(arena.allocator(), &program);
        try std.testing.expectEqual(@as(usize, 2), result.rewritten_blocks);
        try std.testing.expectEqual(second_id, program.blocks[first_id.index()].terminator.jump.target);
        try std.testing.expectEqual(second_id, edge_path.constraintEffectiveTarget(&program, constraints[0]).?);
        try std.testing.expectEqual(bypass_id, edge_path.constraintEffectiveTarget(&program, constraints[1]).?);

        var unwitnessed = program;
        unwitnessed.obligations = &.{};
        try std.testing.expect(edge_path.constraintEffectiveTarget(&unwitnessed, constraints[0]) == null);
        try std.testing.expect(edge_path.constraintEffectiveTarget(&unwitnessed, constraints[1]) == null);
    }
    {
        var mismatched_terms = terms;
        mismatched_terms[0].operation.boolean_literal = false;
        var program = base;
        program.solver_terms = &mismatched_terms;
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const result = try applyProvedBranches(arena.allocator(), &program);
        try std.testing.expectEqual(@as(usize, 0), result.rewritten_blocks);
    }
}

test "proved edge fact bypasses a parameterized instruction-free dispatcher" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const dispatch_id = ir.BlockId.fromIndex(1);
    const true_id = ir.BlockId.fromIndex(2);
    const false_id = ir.BlockId.fromIndex(3);
    const input_id = ir.ValueId.fromIndex(0);
    const condition_id = ir.ValueId.fromIndex(1);
    const true_parameter = ir.ValueId.fromIndex(2);
    const false_parameter = ir.ValueId.fromIndex(3);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .jump = .{ .target = dispatch_id, .arguments = &.{input_id} } } },
        .{ .id = dispatch_id, .function = function_id, .parameters = &.{condition_id}, .terminator = .{ .branch = .{
            .condition = condition_id,
            .then_edge = .{ .target = true_id, .arguments = &.{condition_id} },
            .else_edge = .{ .target = false_id, .arguments = &.{condition_id} },
        } } },
        .{ .id = true_id, .function = function_id, .parameters = &.{true_parameter}, .terminator = .{ .return_values = &.{true_parameter} } },
        .{ .id = false_id, .function = function_id, .parameters = &.{false_parameter}, .terminator = .{ .return_values = &.{false_parameter} } },
    };
    const values = [_]ir.Value{
        .{ .id = input_id, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = condition_id, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = dispatch_id, .index = 0 } } },
        .{ .id = true_parameter, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = true_id, .index = 0 } } },
        .{ .id = false_parameter, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = false_id, .index = 0 } } },
    };
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = condition_id },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{evidence_id},
        .scope = .{ .edge = .{ .source = entry_id, .kind = .jump, .target = dispatch_id } },
    }};
    const queries = [_]ir.SolverQuery{.{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(0),
    }};
    const certificates = [_]ir.SolverCertificate{.{
        .id = ir.CertificateId.fromIndex(0),
        .query = ir.QueryId.fromIndex(0),
        .engine = .internal_facts,
        .resolution = .proved,
    }};
    const base_program: ir.Program = .{
        .program_id = "edge-dispatch-bypass",
        .entry_function = function_id,
        .functions = &.{.{
            .id = function_id,
            .parameters = &.{input_id},
            .entry_block = entry_id,
            .blocks = &.{ entry_id, dispatch_id, true_id, false_id },
        }},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &.{.{ .id = evidence_id, .kind = .dynamic_fixture, .locator = "fixture:edge-dispatch-bypass" }},
        .solver_terms = &terms,
        .constraints = &constraints,
        .queries = &queries,
        .certificates = &certificates,
    };

    var program = base_program;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const result = try applyProvedBranches(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 0), result.rewritten_blocks);
    try std.testing.expectEqual(@as(usize, 1), result.specialized_edges);
    try std.testing.expectEqual(true_id, program.blocks[entry_id.index()].terminator.jump.target);
    try std.testing.expectEqualSlices(ir.ValueId, &.{input_id}, program.blocks[entry_id.index()].terminator.jump.arguments);

    var escaping_blocks = blocks;
    escaping_blocks[true_id.index()].terminator = .{ .return_values = &.{condition_id} };
    var escaping = base_program;
    escaping.blocks = &escaping_blocks;
    const escaping_result = try applyProvedBranches(arena.allocator(), &escaping);
    try std.testing.expectEqual(@as(usize, 0), escaping_result.specialized_edges);
    try std.testing.expectEqual(dispatch_id, escaping.blocks[entry_id.index()].terminator.jump.target);
}

test "opposite proved facts in one edge context suppress specialization" {
    const fixture = @import("fixtures.zig").relational_dispatch_module;
    const t_condition = ir.SolverTermId.fromIndex(fixture.solver_terms.len);
    const t_not_condition = ir.SolverTermId.fromIndex(fixture.solver_terms.len + 1);
    const terms = fixture.solver_terms ++ [_]ir.SolverTerm{
        .{ .id = t_condition, .sort = .{ .kind = .boolean }, .operation = .{ .value = fixture.v_condition } },
        .{ .id = t_not_condition, .sort = .{ .kind = .boolean }, .operation = .{ .logical_not = t_condition } },
    };
    const queries = [_]ir.SolverQuery{
        .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .assumptions = &.{fixture.c_left},
            .goal = t_condition,
        },
        .{
            .id = ir.QueryId.fromIndex(1),
            .kind = .prove_true,
            .assumptions = &.{fixture.c_left},
            .goal = t_not_condition,
        },
    };
    const certificates = [_]ir.SolverCertificate{
        .{ .id = ir.CertificateId.fromIndex(0), .query = ir.QueryId.fromIndex(0), .engine = .internal_facts, .resolution = .proved },
        .{ .id = ir.CertificateId.fromIndex(1), .query = ir.QueryId.fromIndex(1), .engine = .internal_facts, .resolution = .proved },
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    program.queries = &queries;
    program.certificates = &certificates;
    const original_edge = program.blocks[fixture.b_left.index()].terminator.jump;

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    for (0..2) |_| {
        const result = try applyProvedBranches(arena.allocator(), &program);
        try std.testing.expect(result.conflicting_certificate == null);
        try std.testing.expectEqual(@as(usize, 0), result.specialized_edges);
        try std.testing.expect(edge_path.sameEdge(original_edge, program.blocks[fixture.b_left.index()].terminator.jump));
        try std.testing.expectEqual(@as(usize, 0), program.edge_rewrites.len);
    }
}

test "proved relational edge fact drops only a local exact-pure dispatcher expression" {
    const fixture = @import("fixtures.zig").relational_dispatch_module;
    const t_condition = ir.SolverTermId.fromIndex(fixture.solver_terms.len);
    const t_not_condition = ir.SolverTermId.fromIndex(fixture.solver_terms.len + 1);
    const terms = fixture.solver_terms ++ [_]ir.SolverTerm{
        .{ .id = t_condition, .sort = .{ .kind = .boolean }, .operation = .{ .value = fixture.v_condition } },
        .{ .id = t_not_condition, .sort = .{ .kind = .boolean }, .operation = .{ .logical_not = t_condition } },
    };
    const queries = [_]ir.SolverQuery{
        .{
            .id = ir.QueryId.fromIndex(0),
            .kind = .prove_true,
            .assumptions = &.{fixture.c_left},
            .goal = t_condition,
        },
        .{
            .id = ir.QueryId.fromIndex(1),
            .kind = .prove_true,
            .assumptions = &.{fixture.c_right},
            .goal = t_not_condition,
        },
    };
    const certificates = [_]ir.SolverCertificate{
        .{
            .id = ir.CertificateId.fromIndex(0),
            .query = ir.QueryId.fromIndex(0),
            .engine = .internal_facts,
            .resolution = .proved,
        },
        .{
            .id = ir.CertificateId.fromIndex(1),
            .query = ir.QueryId.fromIndex(1),
            .engine = .internal_facts,
            .resolution = .proved,
        },
    };
    var base_program = fixture.program;
    base_program.solver_terms = &terms;
    base_program.queries = &queries;
    base_program.certificates = &certificates;

    {
        var program = base_program;
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const result = try applyProvedBranches(arena.allocator(), &program);
        try std.testing.expectEqual(@as(usize, 2), result.specialized_edges);
        try std.testing.expectEqual(fixture.b_true, program.blocks[fixture.b_left.index()].terminator.jump.target);
        try std.testing.expectEqual(fixture.b_false, program.blocks[fixture.b_right.index()].terminator.jump.target);
    }
    {
        var escaping_blocks = fixture.blocks;
        escaping_blocks[fixture.b_true.index()].terminator = .{ .return_values = &.{fixture.v_condition} };
        var program = base_program;
        program.blocks = &escaping_blocks;
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const result = try applyProvedBranches(arena.allocator(), &program);
        try std.testing.expectEqual(@as(usize, 0), result.specialized_edges);
        try std.testing.expectEqual(fixture.b_dispatch, program.blocks[fixture.b_left.index()].terminator.jump.target);
        try std.testing.expectEqual(fixture.b_dispatch, program.blocks[fixture.b_right.index()].terminator.jump.target);
    }
    {
        var throwing_instructions = fixture.instructions;
        throwing_instructions[fixture.i_condition.index()].effects = .{ .precision = .exact, .may_throw = true };
        var program = base_program;
        program.instructions = &throwing_instructions;
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const result = try applyProvedBranches(arena.allocator(), &program);
        try std.testing.expectEqual(@as(usize, 0), result.specialized_edges);
        try std.testing.expectEqual(fixture.b_dispatch, program.blocks[fixture.b_left.index()].terminator.jump.target);
        try std.testing.expectEqual(fixture.b_dispatch, program.blocks[fixture.b_right.index()].terminator.jump.target);
    }
}

test "iteration forwarding retains an empty acyclic body arm" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const header_id = ir.BlockId.fromIndex(1);
    const body_id = ir.BlockId.fromIndex(2);
    const exit_id = ir.BlockId.fromIndex(3);
    const transition_id = ir.InstructionId.fromIndex(0);
    const input_control = ir.ValueId.fromIndex(0);
    const input_limit = ir.ValueId.fromIndex(1);
    const input_step = ir.ValueId.fromIndex(2);
    const input_initial = ir.ValueId.fromIndex(3);
    const header_control = ir.ValueId.fromIndex(4);
    const header_limit = ir.ValueId.fromIndex(5);
    const header_step = ir.ValueId.fromIndex(6);
    const header_initial = ir.ValueId.fromIndex(7);
    const has_value = ir.ValueId.fromIndex(8);
    const normalized_limit = ir.ValueId.fromIndex(9);
    const normalized_step = ir.ValueId.fromIndex(10);
    const index = ir.ValueId.fromIndex(11);
    const body_index = ir.ValueId.fromIndex(12);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .jump = .{
            .target = header_id,
            .arguments = &.{ input_control, input_limit, input_step, input_initial },
        } } },
        .{
            .id = header_id,
            .function = function_id,
            .parameters = &.{ header_control, header_limit, header_step, header_initial },
            .instructions = &.{transition_id},
            .terminator = .{ .branch = .{
                .condition = has_value,
                .then_edge = .{ .target = body_id, .arguments = &.{index} },
                .else_edge = .{ .target = exit_id },
            } },
        },
        .{
            .id = body_id,
            .function = function_id,
            .parameters = &.{body_index},
            .terminator = .{ .jump = .{ .target = exit_id } },
        },
        .{ .id = exit_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const values = [_]ir.Value{
        .{ .id = input_control, .function = function_id, .type = .number, .origin = .{ .parameter = 0 } },
        .{ .id = input_limit, .function = function_id, .type = .number, .origin = .{ .parameter = 1 } },
        .{ .id = input_step, .function = function_id, .type = .number, .origin = .{ .parameter = 2 } },
        .{ .id = input_initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 3 } },
        .{ .id = header_control, .function = function_id, .type = .number, .origin = .{ .block_parameter = .{ .block = header_id, .index = 0 } } },
        .{ .id = header_limit, .function = function_id, .type = .number, .origin = .{ .block_parameter = .{ .block = header_id, .index = 1 } } },
        .{ .id = header_step, .function = function_id, .type = .number, .origin = .{ .block_parameter = .{ .block = header_id, .index = 2 } } },
        .{ .id = header_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = header_id, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 2 } } },
        .{ .id = index, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = transition_id, .index = 3 } } },
        .{ .id = body_index, .function = function_id, .type = .number, .origin = .{ .block_parameter = .{ .block = body_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = transition_id,
        .block = header_id,
        .operation = .{ .numeric_for_next = .{
            .control = header_control,
            .limit = header_limit,
            .step = header_step,
            .initial = header_initial,
        } },
        .results = &.{ has_value, normalized_limit, normalized_step, index },
        .effects = .numeric_for_next,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .frontend_proof,
        .locator = "fixture:iteration-empty-body-arm",
    }};
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = has_value },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{evidence_id},
        .scope = .{ .edge = .{ .source = header_id, .kind = .branch_then, .target = body_id } },
    }};
    var program: ir.Program = .{
        .program_id = "iteration-empty-body-arm",
        .entry_function = function_id,
        .functions = &.{.{
            .id = function_id,
            .parameters = &.{ input_control, input_limit, input_step, input_initial },
            .blocks = &.{ entry_id, header_id, body_id, exit_id },
            .entry_block = entry_id,
        }},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
        .solver_terms = &terms,
        .constraints = &constraints,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const result = try applyProvedBranches(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 0), result.specialized_edges);
    try std.testing.expectEqual(body_id, program.blocks[header_id.index()].terminator.branch.then_edge.target);
    try std.testing.expectEqual(@as(usize, 0), program.edge_rewrites.len);
}

test "forwarding jumps persist replayable copy-chain parameter substitution" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const forwarding_id = ir.BlockId.fromIndex(1);
    const exit_id = ir.BlockId.fromIndex(2);
    const input_left = ir.ValueId.fromIndex(0);
    const input_right = ir.ValueId.fromIndex(1);
    const forwarded_left = ir.ValueId.fromIndex(2);
    const forwarded_right = ir.ValueId.fromIndex(3);
    const output_left = ir.ValueId.fromIndex(4);
    const output_right = ir.ValueId.fromIndex(5);
    const output_duplicate = ir.ValueId.fromIndex(6);
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .jump = .{
            .target = forwarding_id,
            .arguments = &.{ input_left, input_right },
        } } },
        .{
            .id = forwarding_id,
            .function = function_id,
            .parameters = &.{ forwarded_left, forwarded_right },
            .terminator = .{ .jump = .{
                .target = exit_id,
                .arguments = &.{ forwarded_right, forwarded_left, forwarded_right },
            } },
        },
        .{
            .id = exit_id,
            .function = function_id,
            .parameters = &.{ output_left, output_right, output_duplicate },
            .terminator = .{ .return_values = &.{ output_left, output_right, output_duplicate } },
        },
    };
    const values = [_]ir.Value{
        .{ .id = input_left, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = input_right, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = forwarded_left, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = forwarding_id, .index = 0 } } },
        .{ .id = forwarded_right, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = forwarding_id, .index = 1 } } },
        .{ .id = output_left, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = exit_id, .index = 0 } } },
        .{ .id = output_right, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = exit_id, .index = 1 } } },
        .{ .id = output_duplicate, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = exit_id, .index = 2 } } },
    };
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .frontend_proof,
        .locator = "fixture:forwarding-jump-substitution",
    }};
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = input_left },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{evidence_id},
        .scope = .{ .edge = .{ .source = entry_id, .kind = .jump, .target = forwarding_id } },
    }};
    var program: ir.Program = .{
        .program_id = "forwarding-jump-substitution",
        .entry_function = function_id,
        .functions = &.{.{
            .id = function_id,
            .parameters = &.{ input_left, input_right },
            .blocks = &.{ entry_id, forwarding_id, exit_id },
            .entry_block = entry_id,
        }},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
        .solver_terms = &terms,
        .constraints = &constraints,
    };

    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const result = try applyProvedBranches(arena.allocator(), &program);
    try std.testing.expectEqual(@as(usize, 1), result.specialized_edges);
    try std.testing.expectEqual(exit_id, program.blocks[entry_id.index()].terminator.jump.target);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ input_right, input_left, input_right }, program.blocks[entry_id.index()].terminator.jump.arguments);
    try std.testing.expectEqual(@as(usize, 1), program.edge_rewrites.len);
    try std.testing.expectEqual(ir.EdgeRewriteRule.forwarding_jump, program.edge_rewrites[0].rule);
    try std.testing.expect(program.edge_rewrites[0].certificate == null);

    var report = try @import("validate.zig").validate(std.testing.allocator, &program, .core);
    defer report.deinit();
    try std.testing.expect(report.isClean());

    const copied_right = ir.ValueId.fromIndex(values.len);
    const recopied_right = ir.ValueId.fromIndex(values.len + 1);
    const copied_values = values ++ [_]ir.Value{
        .{
            .id = copied_right,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } },
        },
        .{
            .id = recopied_right,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } },
        },
    };
    const copy_instructions = [_]ir.Instruction{
        .{
            .id = ir.InstructionId.fromIndex(0),
            .block = forwarding_id,
            .operation = .{ .copy = forwarded_right },
            .results = &.{copied_right},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
        .{
            .id = ir.InstructionId.fromIndex(1),
            .block = forwarding_id,
            .operation = .{ .copy = copied_right },
            .results = &.{recopied_right},
            .effects = .pure,
            .evidence = &.{evidence_id},
        },
    };
    var copy_blocks = blocks;
    copy_blocks[forwarding_id.index()].instructions = &.{ ir.InstructionId.fromIndex(0), ir.InstructionId.fromIndex(1) };
    copy_blocks[forwarding_id.index()].terminator.jump.arguments = &.{ recopied_right, forwarded_left, recopied_right };
    var copy_program = program;
    copy_program.blocks = &copy_blocks;
    copy_program.instructions = &copy_instructions;
    copy_program.values = &copied_values;
    copy_program.edge_rewrites = &.{};
    const copy_result = try applyProvedBranches(arena.allocator(), &copy_program);
    try std.testing.expectEqual(@as(usize, 1), copy_result.specialized_edges);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ input_right, input_left, input_right }, copy_program.blocks[entry_id.index()].terminator.jump.arguments);
    var copy_report = try @import("validate.zig").validate(std.testing.allocator, &copy_program, .core);
    defer copy_report.deinit();
    try std.testing.expect(copy_report.isClean());

    var escaping_parameter_blocks = blocks;
    escaping_parameter_blocks[exit_id.index()].terminator = .{ .return_values = &.{forwarded_left} };
    var escaping_parameter_program = program;
    escaping_parameter_program.blocks = &escaping_parameter_blocks;
    escaping_parameter_program.edge_rewrites = &.{};
    const escaping_parameter_result = try applyProvedBranches(arena.allocator(), &escaping_parameter_program);
    try std.testing.expectEqual(@as(usize, 0), escaping_parameter_result.specialized_edges);
    try std.testing.expectEqual(forwarding_id, escaping_parameter_program.blocks[entry_id.index()].terminator.jump.target);

    var escaping_result_blocks = copy_blocks;
    escaping_result_blocks[exit_id.index()].terminator = .{ .return_values = &.{copied_right} };
    var escaping_result_program = copy_program;
    escaping_result_program.blocks = &escaping_result_blocks;
    escaping_result_program.edge_rewrites = &.{};
    const escaping_result = try applyProvedBranches(arena.allocator(), &escaping_result_program);
    try std.testing.expectEqual(@as(usize, 0), escaping_result.specialized_edges);
    try std.testing.expectEqual(forwarding_id, escaping_result_program.blocks[entry_id.index()].terminator.jump.target);

    var throwing_instructions = copy_instructions;
    throwing_instructions[0].effects = .{ .precision = .exact, .may_throw = true };
    var throwing_program = program;
    throwing_program.blocks = &copy_blocks;
    throwing_program.instructions = &throwing_instructions;
    throwing_program.values = &copied_values;
    throwing_program.edge_rewrites = &.{};
    const throwing_result = try applyProvedBranches(arena.allocator(), &throwing_program);
    try std.testing.expectEqual(@as(usize, 0), throwing_result.specialized_edges);
    try std.testing.expectEqual(forwarding_id, throwing_program.blocks[entry_id.index()].terminator.jump.target);

    var constant_instructions = copy_instructions;
    constant_instructions[0].operation = .{ .constant = .{ .boolean = true } };
    var constant_program = program;
    constant_program.blocks = &copy_blocks;
    constant_program.instructions = &constant_instructions;
    constant_program.values = &copied_values;
    constant_program.edge_rewrites = &.{};
    const constant_result = try applyProvedBranches(arena.allocator(), &constant_program);
    try std.testing.expectEqual(@as(usize, 0), constant_result.specialized_edges);
    try std.testing.expectEqual(forwarding_id, constant_program.blocks[entry_id.index()].terminator.jump.target);

    var tampered_rewrites = [_]ir.CfgEdgeRewrite{program.edge_rewrites[0]};
    tampered_rewrites[0].to.arguments = &.{ input_left, input_right, input_left };
    var tampered = program;
    tampered.edge_rewrites = &tampered_rewrites;
    var tampered_report = try @import("validate.zig").validate(std.testing.allocator, &tampered, .core);
    defer tampered_report.deinit();
    try std.testing.expect(tampered_report.contains(.invalid_edge_rewrite));

    var instruction_blocks = blocks;
    instruction_blocks[forwarding_id.index()].instructions = &.{ir.InstructionId.fromIndex(0)};
    var retained = program;
    retained.blocks = &instruction_blocks;
    retained.edge_rewrites = &.{};
    const retained_result = try applyProvedBranches(arena.allocator(), &retained);
    try std.testing.expectEqual(@as(usize, 0), retained_result.specialized_edges);
    try std.testing.expectEqual(forwarding_id, retained.blocks[entry_id.index()].terminator.jump.target);
}
