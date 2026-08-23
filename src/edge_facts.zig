const std = @import("std");
const ir = @import("ir.zig");
const solver = @import("solver.zig");
const edge_path = @import("edge_path.zig");
const readable_scope = @import("readable_scope.zig");

const argument_evidence_locator = "backend:cfg-edge-argument-equality:v1";
const branch_evidence_locator = "backend:cfg-branch-arm-truth:v1";
const max_unique_predecessor_depth: usize = 64;
const edge_kinds = [_]ir.CfgEdgeKind{ .jump, .branch_then, .branch_else };

const StructuralRootEdge = union(enum) {
    none: void,
    edge: ir.Edge,
    invalid: void,
};

/// Indexes structural edge roots once for one immutable CFG view. The
/// predecessor facts below used to rescan every rewrite for every edge fact.
pub const StructuralCache = struct {
    allocator: std.mem.Allocator,
    roots: []StructuralRootEdge,
    rewritten: []bool,
    valid_layout: bool,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program) !StructuralCache {
        const entry_count = std.math.mul(usize, program.blocks.len, edge_kinds.len) catch return error.OutOfMemory;
        const roots = try allocator.alloc(StructuralRootEdge, entry_count);
        errdefer allocator.free(roots);
        const rewritten = try allocator.alloc(bool, entry_count);
        errdefer allocator.free(rewritten);
        for (roots) |*root| root.* = .{ .none = {} };
        @memset(rewritten, false);

        var cache: StructuralCache = .{
            .allocator = allocator,
            .roots = roots,
            .rewritten = rewritten,
            .valid_layout = true,
        };
        for (program.edge_rewrites, 0..) |rewrite, rewrite_index| {
            const source_index = rewrite.source.index();
            if (source_index >= program.blocks.len) continue;
            const entry_index = source_index * edge_kinds.len + kindIndex(rewrite.kind);
            if (cache.rewritten[entry_index]) continue;
            cache.rewritten[entry_index] = true;
            cache.roots[entry_index] = if (rewrite.id.index() == rewrite_index)
                .{ .edge = rewrite.from }
            else
                .{ .invalid = {} };
        }
        for (program.blocks, 0..) |block, block_index| {
            if (block.id.index() != block_index) {
                cache.valid_layout = false;
                continue;
            }
            for (edge_kinds, 0..) |kind, kind_index| {
                const entry_index = block_index * edge_kinds.len + kind_index;
                if (!cache.rewritten[entry_index]) cache.roots[entry_index] = liveStructuralRootEdge(program, block, kind);
            }
        }
        return cache;
    }

    pub fn deinit(self: *StructuralCache) void {
        self.allocator.free(self.roots);
        self.allocator.free(self.rewritten);
        self.* = undefined;
    }

    fn get(self: *const StructuralCache, block: ir.Block, kind: ir.CfgEdgeKind) StructuralRootEdge {
        if (!self.valid_layout or block.id.index() >= self.roots.len / edge_kinds.len) return .{ .invalid = {} };
        return self.roots[block.id.index() * edge_kinds.len + kindIndex(kind)];
    }
};

fn kindIndex(kind: ir.CfgEdgeKind) usize {
    return switch (kind) {
        .jump => 0,
        .branch_then => 1,
        .branch_else => 2,
    };
}

pub fn isStructuralEvidence(record: ir.Evidence) bool {
    return record.kind == .structural_derivation and
        (std.mem.eql(u8, record.locator, argument_evidence_locator) or std.mem.eql(u8, record.locator, branch_evidence_locator));
}

pub fn replaysConstraint(program: *const ir.Program, constraint: ir.Constraint) bool {
    switch (constraint.scope) {
        .edge => {},
        else => return false,
    }
    if (constraint.evidence.len != 1 or constraint.evidence[0].index() >= program.evidence.len) return false;
    const record = program.evidence[constraint.evidence[0].index()];
    if (std.mem.eql(u8, record.locator, branch_evidence_locator)) return replaysBranchConstraint(program, constraint);
    if (!std.mem.eql(u8, record.locator, argument_evidence_locator)) return false;
    const edge = edge_path.constraintEdgeValue(program, constraint) orelse return false;
    if (edge.target.index() >= program.blocks.len) return false;
    const target = program.blocks[edge.target.index()];
    if (target.id != edge.target or target.parameters.len != edge.arguments.len) return false;
    for (target.parameters, edge.arguments) |parameter_id, argument_id| {
        if (parameter_id.index() >= program.values.len or argument_id.index() >= program.values.len) continue;
        const sort = commonSort(program.values[parameter_id.index()].type, program.values[argument_id.index()].type) orelse continue;
        if (predicateMatches(
            program,
            constraint.predicate,
            parameter_id,
            argument_id,
            sort,
            constraint.scope.edge,
            constraint.path_rewrites,
        )) return true;
    }
    return false;
}

pub fn derive(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    constraints: *std.ArrayList(ir.Constraint),
    evidence: *std.ArrayList(ir.Evidence),
) !void {
    var scope = try readable_scope.Scope.init(allocator, program);
    defer scope.deinit();
    var history_cache = try edge_path.HistoryCache.init(allocator, program);
    defer history_cache.deinit();
    var structural_cache = try StructuralCache.init(allocator, program);
    defer structural_cache.deinit();
    for (program.blocks) |block| try deriveBlockWithHistory(
        allocator,
        program,
        &scope,
        terms,
        constraints,
        evidence,
        &history_cache,
        &structural_cache,
        block,
        true,
    );
}

pub fn deriveBlock(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    terms: *std.ArrayList(ir.SolverTerm),
    constraints: *std.ArrayList(ir.Constraint),
    evidence: *std.ArrayList(ir.Evidence),
    block: ir.Block,
    derive_branch_arms: bool,
) !void {
    return deriveBlockWithHistory(
        allocator,
        program,
        scope,
        terms,
        constraints,
        evidence,
        null,
        null,
        block,
        derive_branch_arms,
    );
}

pub fn deriveBlockWithHistory(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    terms: *std.ArrayList(ir.SolverTerm),
    constraints: *std.ArrayList(ir.Constraint),
    evidence: *std.ArrayList(ir.Evidence),
    history_cache: ?*const edge_path.HistoryCache,
    structural_cache: ?*const StructuralCache,
    block: ir.Block,
    derive_branch_arms: bool,
) !void {
    if (!scope.block(block.id)) return;
    switch (block.terminator) {
        .jump => |edge| try deriveEdge(allocator, program, terms, constraints, evidence, history_cache, structural_cache, .{
            .source = block.id,
            .kind = .jump,
            .target = edge.target,
        }, edge),
        .branch => |branch| {
            if (derive_branch_arms and solver.evaluateValue(program, branch.condition) != .boolean) {
                try deriveBranchFact(allocator, program, terms, constraints, evidence, history_cache, block, branch, .branch_then);
                try deriveBranchFact(allocator, program, terms, constraints, evidence, history_cache, block, branch, .branch_else);
            }
            try deriveEdge(allocator, program, terms, constraints, evidence, history_cache, structural_cache, .{
                .source = block.id,
                .kind = .branch_then,
                .target = branch.then_edge.target,
            }, branch.then_edge);
            try deriveEdge(allocator, program, terms, constraints, evidence, history_cache, structural_cache, .{
                .source = block.id,
                .kind = .branch_else,
                .target = branch.else_edge.target,
            }, branch.else_edge);
        },
        else => {},
    }
}

fn deriveEdge(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    constraints: *std.ArrayList(ir.Constraint),
    evidence: *std.ArrayList(ir.Evidence),
    history_cache: ?*const edge_path.HistoryCache,
    structural_cache: ?*const StructuralCache,
    reference: ir.CfgEdgeRef,
    edge: ir.Edge,
) !void {
    if (edge.target.index() >= program.blocks.len) return;
    const target = program.blocks[edge.target.index()];
    if (target.id != edge.target or target.parameters.len != edge.arguments.len) return;
    const history = if (history_cache) |cache|
        (cache.get(reference) orelse return)
    else
        (try edge_path.historyForCurrentEdgeAlloc(allocator, program, reference) orelse return);
    defer if (history_cache == null) allocator.free(history.rewrites);

    for (target.parameters, edge.arguments) |parameter_id, argument_id| {
        if (parameter_id.index() >= program.values.len or argument_id.index() >= program.values.len) continue;
        const sort = commonSort(program.values[parameter_id.index()].type, program.values[argument_id.index()].type) orelse continue;
        const predicate = try edgePredicate(allocator, program, terms, parameter_id, argument_id, sort, history.root, history.rewrites, structural_cache);
        if (hasConstraint(constraints.items, predicate, history.root, history.rewrites)) continue;
        const evidence_id = try ensureEvidence(allocator, evidence, argument_evidence_locator);
        try constraints.append(allocator, .{
            .id = ir.ConstraintId.fromIndex(constraints.items.len),
            .predicate = predicate,
            .evidence = try allocator.dupe(ir.EvidenceId, &.{evidence_id}),
            .scope = .{ .edge = history.root },
            .path_rewrites = try allocator.dupe(ir.EdgeRewriteId, history.rewrites),
        });
    }
}

fn deriveBranchFact(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    constraints: *std.ArrayList(ir.Constraint),
    evidence: *std.ArrayList(ir.Evidence),
    history_cache: ?*const edge_path.HistoryCache,
    block: ir.Block,
    branch: ir.Branch,
    kind: ir.CfgEdgeKind,
) !void {
    if (branch.condition.index() >= program.values.len or program.values[branch.condition.index()].type.kind != .boolean) return;
    const edge = if (kind == .branch_then) branch.then_edge else branch.else_edge;
    const reference: ir.CfgEdgeRef = .{ .source = block.id, .kind = kind, .target = edge.target };
    const history = if (history_cache) |cache|
        (cache.get(reference) orelse return)
    else
        (try edge_path.historyForCurrentEdgeAlloc(allocator, program, reference) orelse return);
    defer if (history_cache == null) allocator.free(history.rewrites);
    const condition = try ensureValueTerm(allocator, terms, branch.condition, .{ .kind = .boolean });
    const predicate = if (kind == .branch_then) condition else try ensureNotTerm(allocator, terms, condition);
    if (hasConstraint(constraints.items, predicate, history.root, &.{})) return;
    const evidence_id = try ensureEvidence(allocator, evidence, branch_evidence_locator);
    try constraints.append(allocator, .{
        .id = ir.ConstraintId.fromIndex(constraints.items.len),
        .predicate = predicate,
        .evidence = try allocator.dupe(ir.EvidenceId, &.{evidence_id}),
        .scope = .{ .edge = history.root },
        .path_rewrites = try allocator.dupe(ir.EdgeRewriteId, &.{}),
    });
}

fn commonSort(parameter_type: ir.ValueType, argument_type: ir.ValueType) ?ir.SolverSort {
    if (parameter_type.kind != argument_type.kind) return null;
    return switch (parameter_type.kind) {
        .boolean => .{ .kind = .boolean },
        .integer => .{ .kind = .integer },
        else => null,
    };
}

fn predicateMatches(
    program: *const ir.Program,
    predicate_id: ir.SolverTermId,
    parameter_id: ir.ValueId,
    argument_id: ir.ValueId,
    sort: ir.SolverSort,
    root: ir.CfgEdgeRef,
    path: []const ir.EdgeRewriteId,
) bool {
    if (predicate_id.index() >= program.solver_terms.len) return false;
    if (sort.kind == .boolean) {
        const known = knownBooleanOnPath(program, parameter_id, argument_id, root, path, null) orelse switch (solver.evaluateValue(program, argument_id)) {
            .boolean => |truth| truth,
            else => null,
        };
        if (known) |truth| return if (truth)
            termIsValue(program, predicate_id, parameter_id, sort)
        else
            termIsNotValue(program, predicate_id, parameter_id);
    }
    return termIsEquality(program, predicate_id, parameter_id, argument_id, sort);
}

fn termIsValue(program: *const ir.Program, term_id: ir.SolverTermId, value_id: ir.ValueId, sort: ir.SolverSort) bool {
    if (term_id.index() >= program.solver_terms.len) return false;
    const term = program.solver_terms[term_id.index()];
    if (!sameSort(term.sort, sort)) return false;
    return switch (term.operation) {
        .value => |candidate| candidate == value_id,
        else => false,
    };
}

fn termIsNotValue(program: *const ir.Program, term_id: ir.SolverTermId, value_id: ir.ValueId) bool {
    if (term_id.index() >= program.solver_terms.len) return false;
    const term = program.solver_terms[term_id.index()];
    if (term.sort.kind != .boolean) return false;
    return switch (term.operation) {
        .logical_not => |operand| termIsValue(program, operand, value_id, .{ .kind = .boolean }),
        else => false,
    };
}

fn termIsEquality(
    program: *const ir.Program,
    term_id: ir.SolverTermId,
    left_value: ir.ValueId,
    right_value: ir.ValueId,
    operand_sort: ir.SolverSort,
) bool {
    if (term_id.index() >= program.solver_terms.len) return false;
    const term = program.solver_terms[term_id.index()];
    if (term.sort.kind != .boolean) return false;
    return switch (term.operation) {
        .binary => |binary| binary.operator == .equal and
            ((termIsValue(program, binary.left, left_value, operand_sort) and termIsValue(program, binary.right, right_value, operand_sort)) or
                (termIsValue(program, binary.left, right_value, operand_sort) and termIsValue(program, binary.right, left_value, operand_sort))),
        else => false,
    };
}

fn edgePredicate(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    terms: *std.ArrayList(ir.SolverTerm),
    parameter_id: ir.ValueId,
    argument_id: ir.ValueId,
    sort: ir.SolverSort,
    root: ir.CfgEdgeRef,
    path: []const ir.EdgeRewriteId,
    structural_cache: ?*const StructuralCache,
) !ir.SolverTermId {
    const parameter = try ensureValueTerm(allocator, terms, parameter_id, sort);
    if (sort.kind == .boolean) {
        const truth = knownBooleanOnPath(program, parameter_id, argument_id, root, path, structural_cache) orelse switch (solver.evaluateValue(program, argument_id)) {
            .boolean => |value| value,
            else => null,
        };
        if (truth) |value| return if (value) parameter else try ensureNotTerm(allocator, terms, parameter);
    }
    const argument = try ensureValueTerm(allocator, terms, argument_id, sort);
    return ensureEqualityTerm(allocator, terms, parameter, argument);
}

fn knownBooleanOnPath(
    program: *const ir.Program,
    parameter_id: ir.ValueId,
    value_id: ir.ValueId,
    root: ir.CfgEdgeRef,
    path: []const ir.EdgeRewriteId,
    structural_cache: ?*const StructuralCache,
) ?bool {
    var known: ?bool = null;
    for (program.constraints) |constraint| {
        const constraint_root = switch (constraint.scope) {
            .edge => |edge| edge,
            else => continue,
        };
        if (!std.meta.eql(constraint_root, root) or !edge_path.constraintSupportsPath(program, constraint, path)) continue;
        const truth = predicateValueTruth(program, constraint.predicate, value_id) orelse continue;
        if (known) |existing| {
            if (existing != truth) return null;
        } else {
            known = truth;
        }
    }
    if (known) |truth| return truth;
    if (path.len != 0 or !closedBooleanInputPartition(program, root, parameter_id, value_id, structural_cache)) return null;
    return uniquePredecessorBranchTruth(program, root.source, value_id, structural_cache);
}

const StructuralPredecessor = struct {
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
};

// Fold only a straight, unambiguous predecessor chain into the downstream edge root.
fn uniquePredecessorBranchTruth(
    program: *const ir.Program,
    source_id: ir.BlockId,
    value_id: ir.ValueId,
    structural_cache: ?*const StructuralCache,
) ?bool {
    if (source_id.index() >= program.blocks.len or value_id.index() >= program.values.len) return null;
    const source = program.blocks[source_id.index()];
    const value = program.values[value_id.index()];
    if (source.id != source_id or value.id != value_id or value.function != source.function or value.type.kind != .boolean) return null;

    var visited: [max_unique_predecessor_depth]ir.BlockId = undefined;
    visited[0] = source_id;
    var visited_len: usize = 1;
    var current_id = source_id;

    for (0..max_unique_predecessor_depth) |_| {
        const predecessor = uniqueStructuralPredecessor(program, current_id, structural_cache) orelse return null;
        for (visited[0..visited_len]) |visited_id| {
            if (visited_id == predecessor.source) return null;
        }

        const block = program.blocks[predecessor.source.index()];
        switch (block.terminator) {
            .branch => |branch| {
                if (branch.condition.index() >= program.values.len) return null;
                const condition = program.values[branch.condition.index()];
                if (condition.id != branch.condition or condition.function != source.function) return null;
                if (branch.condition == value_id) return switch (predecessor.kind) {
                    .branch_then => true,
                    .branch_else => false,
                    .jump => null,
                };
            },
            .jump => {},
            else => return null,
        }

        if (visited_len == visited.len) return null;
        visited[visited_len] = predecessor.source;
        visited_len += 1;
        current_id = predecessor.source;
    }
    return null;
}

fn uniqueStructuralPredecessor(
    program: *const ir.Program,
    target_id: ir.BlockId,
    structural_cache: ?*const StructuralCache,
) ?StructuralPredecessor {
    if (target_id.index() >= program.blocks.len) return null;
    const target = program.blocks[target_id.index()];
    if (target.id != target_id) return null;

    var found: ?StructuralPredecessor = null;
    for (program.blocks, 0..) |block, block_index| {
        if (block.id.index() != block_index) return null;
        for ([_]ir.CfgEdgeKind{ .jump, .branch_then, .branch_else }) |kind| {
            const edge = switch (structuralRootEdgeCached(program, block, kind, structural_cache)) {
                .none => continue,
                .edge => |value| value,
                .invalid => return null,
            };
            if (edge.target != target_id) continue;
            if (block.function != target.function or found != null) return null;
            found = .{ .source = block.id, .kind = kind };
        }
    }
    return found;
}

fn structuralRootEdge(program: *const ir.Program, block: ir.Block, kind: ir.CfgEdgeKind) StructuralRootEdge {
    if (kind == .jump and edge_path.witnessedBranchCondition(program, block.id) != null) return .{ .none = {} };
    for (program.edge_rewrites, 0..) |rewrite, rewrite_index| {
        if (rewrite.source != block.id or rewrite.kind != kind) continue;
        if (rewrite.id.index() != rewrite_index) return .{ .invalid = {} };
        return .{ .edge = rewrite.from };
    }
    const live: ?ir.Edge = switch (block.terminator) {
        .jump => |edge| if (kind == .jump) edge else null,
        .branch => |branch| switch (kind) {
            .branch_then => branch.then_edge,
            .branch_else => branch.else_edge,
            .jump => null,
        },
        else => null,
    };
    if (live) |edge| return .{ .edge = edge };
    if (edge_path.witnessedBranchEdge(program, block.id, kind)) |edge| return .{ .edge = edge };
    return .{ .none = {} };
}

fn liveStructuralRootEdge(program: *const ir.Program, block: ir.Block, kind: ir.CfgEdgeKind) StructuralRootEdge {
    if (kind == .jump and edge_path.witnessedBranchCondition(program, block.id) != null) return .{ .none = {} };
    const live: ?ir.Edge = switch (block.terminator) {
        .jump => |edge| if (kind == .jump) edge else null,
        .branch => |branch| switch (kind) {
            .branch_then => branch.then_edge,
            .branch_else => branch.else_edge,
            .jump => null,
        },
        else => null,
    };
    if (live) |edge| return .{ .edge = edge };
    if (edge_path.witnessedBranchEdge(program, block.id, kind)) |edge| return .{ .edge = edge };
    return .{ .none = {} };
}

fn structuralRootEdgeCached(
    program: *const ir.Program,
    block: ir.Block,
    kind: ir.CfgEdgeKind,
    structural_cache: ?*const StructuralCache,
) StructuralRootEdge {
    return if (structural_cache) |cache| cache.get(block, kind) else structuralRootEdge(program, block, kind);
}

fn closedBooleanInputPartition(
    program: *const ir.Program,
    root: ir.CfgEdgeRef,
    parameter_id: ir.ValueId,
    argument_id: ir.ValueId,
    structural_cache: ?*const StructuralCache,
) bool {
    if (parameter_id.index() >= program.values.len) return false;
    const parameter = program.values[parameter_id.index()];
    if (parameter.id != parameter_id or parameter.type.kind != .boolean) return false;
    const origin = switch (parameter.origin) {
        .block_parameter => |value| value,
        else => return false,
    };
    if (root.target != origin.block or origin.block.index() >= program.blocks.len) return false;
    const target = program.blocks[origin.block.index()];
    const parameter_index: usize = @intCast(origin.index);
    if (target.id != origin.block or target.function != parameter.function or
        parameter_index >= target.parameters.len or target.parameters[parameter_index] != parameter_id) return false;

    var found_current = false;
    for (program.blocks, 0..) |block, block_index| {
        if (block.id.index() != block_index) return false;
        for ([_]ir.CfgEdgeKind{ .jump, .branch_then, .branch_else }) |kind| {
            const edge = switch (structuralRootEdgeCached(program, block, kind, structural_cache)) {
                .none => continue,
                .edge => |value| value,
                .invalid => return false,
            };
            if (edge.target != target.id) continue;
            if (block.function != target.function or edge.arguments.len != target.parameters.len) return false;
            const candidate = edge.arguments[parameter_index];
            if (block.id == root.source and kind == root.kind) {
                if (found_current or candidate != argument_id) return false;
                found_current = true;
                continue;
            }
            if (candidate.index() >= program.values.len) return false;
            const sibling = program.values[candidate.index()];
            if (sibling.id != candidate or sibling.function != target.function or sibling.type.kind != .boolean) return false;
            switch (solver.evaluateValue(program, candidate)) {
                .boolean => {},
                else => return false,
            }
        }
    }
    return found_current;
}

fn predicateValueTruth(program: *const ir.Program, predicate: ir.SolverTermId, value_id: ir.ValueId) ?bool {
    if (predicate.index() >= program.solver_terms.len) return null;
    return switch (program.solver_terms[predicate.index()].operation) {
        .value => |candidate| if (candidate == value_id) true else null,
        .logical_not => |operand| if (termIsValue(program, operand, value_id, .{ .kind = .boolean })) false else null,
        else => null,
    };
}

fn replaysBranchConstraint(program: *const ir.Program, constraint: ir.Constraint) bool {
    const root = switch (constraint.scope) {
        .edge => |edge| edge,
        else => return false,
    };
    if (edge_path.constraintEdgeValue(program, constraint) == null or root.source.index() >= program.blocks.len) return false;
    const branch = switch (program.blocks[root.source.index()].terminator) {
        .branch => |value| value,
        else => return false,
    };
    return switch (root.kind) {
        .branch_then => termIsValue(program, constraint.predicate, branch.condition, .{ .kind = .boolean }),
        .branch_else => termIsNotValue(program, constraint.predicate, branch.condition),
        .jump => false,
    };
}

fn ensureValueTerm(
    allocator: std.mem.Allocator,
    terms: *std.ArrayList(ir.SolverTerm),
    value_id: ir.ValueId,
    sort: ir.SolverSort,
) !ir.SolverTermId {
    for (terms.items) |term| {
        if (!sameSort(term.sort, sort)) continue;
        switch (term.operation) {
            .value => |candidate| if (candidate == value_id) return term.id,
            else => {},
        }
    }
    const id = ir.SolverTermId.fromIndex(terms.items.len);
    try terms.append(allocator, .{ .id = id, .sort = sort, .operation = .{ .value = value_id } });
    return id;
}

fn ensureNotTerm(
    allocator: std.mem.Allocator,
    terms: *std.ArrayList(ir.SolverTerm),
    operand: ir.SolverTermId,
) !ir.SolverTermId {
    for (terms.items) |term| switch (term.operation) {
        .logical_not => |candidate| if (candidate == operand) return term.id,
        else => {},
    };
    const id = ir.SolverTermId.fromIndex(terms.items.len);
    try terms.append(allocator, .{
        .id = id,
        .sort = .{ .kind = .boolean },
        .operation = .{ .logical_not = operand },
    });
    return id;
}

fn ensureEqualityTerm(
    allocator: std.mem.Allocator,
    terms: *std.ArrayList(ir.SolverTerm),
    left: ir.SolverTermId,
    right: ir.SolverTermId,
) !ir.SolverTermId {
    for (terms.items) |term| switch (term.operation) {
        .binary => |binary| if (binary.operator == .equal and
            ((binary.left == left and binary.right == right) or (binary.left == right and binary.right == left))) return term.id,
        else => {},
    };
    const id = ir.SolverTermId.fromIndex(terms.items.len);
    try terms.append(allocator, .{
        .id = id,
        .sort = .{ .kind = .boolean },
        .operation = .{ .binary = .{ .operator = .equal, .left = left, .right = right } },
    });
    return id;
}

fn hasConstraint(
    constraints: []const ir.Constraint,
    predicate: ir.SolverTermId,
    reference: ir.CfgEdgeRef,
    path_rewrites: []const ir.EdgeRewriteId,
) bool {
    for (constraints) |constraint| {
        if (constraint.predicate != predicate) continue;
        switch (constraint.scope) {
            .edge => |edge| if (std.meta.eql(edge, reference) and
                std.mem.eql(ir.EdgeRewriteId, constraint.path_rewrites, path_rewrites)) return true,
            else => {},
        }
    }
    return false;
}

fn ensureEvidence(allocator: std.mem.Allocator, evidence: *std.ArrayList(ir.Evidence), locator: []const u8) !ir.EvidenceId {
    for (evidence.items) |record| {
        if (record.kind == .structural_derivation and std.mem.eql(u8, record.locator, locator)) return record.id;
    }
    const id = ir.EvidenceId.fromIndex(evidence.items.len);
    try evidence.append(allocator, .{
        .id = id,
        .kind = .structural_derivation,
        .locator = locator,
    });
    return id;
}

fn sameSort(left: ir.SolverSort, right: ir.SolverSort) bool {
    return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed;
}

test "edge facts derive branch truth and integer equalities once with structural provenance" {
    const fixture = @import("fixtures.zig").relational_dispatch_module;
    var program = fixture.program;
    program.constraints = &.{};

    var terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer terms.deinit(std.testing.allocator);
    try terms.appendSlice(std.testing.allocator, program.solver_terms);
    var constraints: std.ArrayList(ir.Constraint) = .empty;
    defer constraints.deinit(std.testing.allocator);
    defer for (constraints.items) |constraint| {
        std.testing.allocator.free(@constCast(constraint.evidence));
        std.testing.allocator.free(@constCast(constraint.path_rewrites));
    };
    var evidence: std.ArrayList(ir.Evidence) = .empty;
    defer evidence.deinit(std.testing.allocator);
    try evidence.appendSlice(std.testing.allocator, program.evidence);

    try derive(std.testing.allocator, &program, &terms, &constraints, &evidence);
    try std.testing.expectEqual(@as(usize, 6), constraints.items.len);
    try std.testing.expectEqual(@as(usize, program.evidence.len + 2), evidence.items.len);
    try std.testing.expectEqualStrings(branch_evidence_locator, evidence.items[constraints.items[0].evidence[0].index()].locator);
    try std.testing.expectEqualStrings(argument_evidence_locator, evidence.items[constraints.items[2].evidence[0].index()].locator);

    const entry_then = constraints.items[0];
    try std.testing.expect(std.meta.eql(
        ir.CfgEdgeRef{ .source = fixture.b_entry, .kind = .branch_then, .target = fixture.b_left },
        entry_then.scope.edge,
    ));

    var derived = program;
    derived.solver_terms = terms.items;
    derived.constraints = constraints.items;
    derived.evidence = evidence.items;
    try std.testing.expect(termIsValue(&derived, entry_then.predicate, fixture.v_selector, .{ .kind = .boolean }));
    try std.testing.expect(termIsNotValue(&derived, constraints.items[1].predicate, fixture.v_selector));
    try std.testing.expect(termIsEquality(
        &derived,
        constraints.items[2].predicate,
        fixture.v_dispatch_state,
        fixture.v_left_state,
        .{ .kind = .integer },
    ));
    try std.testing.expect(termIsEquality(
        &derived,
        constraints.items[3].predicate,
        fixture.v_dispatch_state,
        fixture.v_right_state,
        .{ .kind = .integer },
    ));
    try std.testing.expect(termIsValue(&derived, constraints.items[4].predicate, fixture.v_condition, .{ .kind = .boolean }));
    try std.testing.expect(termIsNotValue(&derived, constraints.items[5].predicate, fixture.v_condition));
    for (derived.constraints) |constraint| try std.testing.expect(replaysConstraint(&derived, constraint));
    var tampered_branch = constraints.items[0];
    tampered_branch.scope.edge.target = fixture.b_true;
    try std.testing.expect(!replaysConstraint(&derived, tampered_branch));
    var tampered_argument = constraints.items[2];
    tampered_argument.scope.edge.target = fixture.b_true;
    try std.testing.expect(!replaysConstraint(&derived, tampered_argument));
    const term_count = terms.items.len;
    const evidence_count = evidence.items.len;
    try derive(std.testing.allocator, &program, &terms, &constraints, &evidence);
    try std.testing.expectEqual(@as(usize, 6), constraints.items.len);
    try std.testing.expectEqual(term_count, terms.items.len);
    try std.testing.expectEqual(evidence_count, evidence.items.len);
}

test "path-normalized Boolean edge facts replay only through their authenticated root history" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const left_id = ir.BlockId.fromIndex(1);
    const right_id = ir.BlockId.fromIndex(2);
    const dispatch_id = ir.BlockId.fromIndex(3);
    const true_id = ir.BlockId.fromIndex(4);
    const false_id = ir.BlockId.fromIndex(5);
    const selector_id = ir.ValueId.fromIndex(0);
    const dispatch_condition_id = ir.ValueId.fromIndex(1);
    const root: ir.CfgEdgeRef = .{ .source = entry_id, .kind = .branch_then, .target = left_id };
    const rewrite_id = ir.EdgeRewriteId.fromIndex(0);
    const branch_evidence_id = ir.EvidenceId.fromIndex(0);
    const argument_evidence_id = ir.EvidenceId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector_id,
            .then_edge = .{ .target = dispatch_id, .arguments = &.{selector_id} },
            .else_edge = .{ .target = right_id },
        } } },
        .{ .id = left_id, .function = function_id, .terminator = .{ .jump = .{ .target = dispatch_id, .arguments = &.{selector_id} } } },
        .{ .id = right_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = dispatch_id, .function = function_id, .parameters = &.{dispatch_condition_id}, .terminator = .{ .branch = .{
            .condition = dispatch_condition_id,
            .then_edge = .{ .target = true_id },
            .else_edge = .{ .target = false_id },
        } } },
        .{ .id = true_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = false_id, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const values = [_]ir.Value{
        .{ .id = selector_id, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = dispatch_condition_id, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = dispatch_id, .index = 0 } } },
    };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .value = selector_id } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .value = dispatch_condition_id } },
    };
    const constraints = [_]ir.Constraint{
        .{
            .id = ir.ConstraintId.fromIndex(0),
            .predicate = ir.SolverTermId.fromIndex(0),
            .evidence = &.{branch_evidence_id},
            .scope = .{ .edge = root },
        },
        .{
            .id = ir.ConstraintId.fromIndex(1),
            .predicate = ir.SolverTermId.fromIndex(1),
            .evidence = &.{argument_evidence_id},
            .scope = .{ .edge = root },
            .path_rewrites = &.{rewrite_id},
        },
    };
    const program: ir.Program = .{
        .program_id = "path-normalized-boolean-replay",
        .entry_function = function_id,
        .functions = &.{.{
            .id = function_id,
            .parameters = &.{selector_id},
            .entry_block = entry_id,
            .blocks = &.{ entry_id, left_id, right_id, dispatch_id, true_id, false_id },
        }},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &.{
            .{ .id = branch_evidence_id, .kind = .structural_derivation, .locator = branch_evidence_locator },
            .{ .id = argument_evidence_id, .kind = .structural_derivation, .locator = argument_evidence_locator },
        },
        .solver_terms = &terms,
        .constraints = &constraints,
        .edge_rewrites = &.{.{
            .id = rewrite_id,
            .source = entry_id,
            .kind = .branch_then,
            .from = .{ .target = left_id },
            .to = .{ .target = dispatch_id, .arguments = &.{selector_id} },
            .rule = .forwarding_jump,
        }},
    };

    try std.testing.expect(replaysConstraint(&program, constraints[0]));
    try std.testing.expect(replaysConstraint(&program, constraints[1]));

    var missing_history = constraints[1];
    missing_history.path_rewrites = &.{};
    try std.testing.expect(!replaysConstraint(&program, missing_history));
    var forged_branch = constraints[0];
    forged_branch.predicate = constraints[1].predicate;
    try std.testing.expect(!replaysConstraint(&program, forged_branch));

    const conflicting_terms = [_]ir.SolverTerm{
        terms[0],
        terms[1],
        .{
            .id = ir.SolverTermId.fromIndex(2),
            .sort = .{ .kind = .boolean },
            .operation = .{ .logical_not = ir.SolverTermId.fromIndex(0) },
        },
    };
    const conflicting_constraints = [_]ir.Constraint{
        constraints[0],
        constraints[1],
        .{
            .id = ir.ConstraintId.fromIndex(2),
            .predicate = ir.SolverTermId.fromIndex(2),
            .evidence = &.{ir.EvidenceId.fromIndex(2)},
            .scope = .{ .edge = root },
        },
    };
    var conflicting = program;
    conflicting.solver_terms = &conflicting_terms;
    conflicting.constraints = &conflicting_constraints;
    conflicting.evidence = &.{
        program.evidence[0],
        program.evidence[1],
        .{ .id = ir.EvidenceId.fromIndex(2), .kind = .dynamic_fixture, .locator = "fixture:contradictory-path-truth" },
    };
    try std.testing.expect(!replaysConstraint(&conflicting, conflicting_constraints[1]));
}
