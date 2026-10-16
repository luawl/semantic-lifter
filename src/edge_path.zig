const std = @import("std");
const ir = @import("ir.zig");
const cfg_edge = @import("cfg_edge.zig");

pub const EdgeHistory = struct {
    root: ir.CfgEdgeRef,
    rewrites: []ir.EdgeRewriteId,
};

/// Memoizes the current history for each live source/kind edge in one
/// immutable program view. Branch-fact and edge-argument derivation consume
/// the same replay result instead of rescanning the rewrite list.
pub const HistoryCache = struct {
    allocator: std.mem.Allocator,
    entries: []Entry,

    const Entry = struct {
        built: bool = false,
        history: ?EdgeHistory = null,
    };

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program) !HistoryCache {
        const entry_count = std.math.mul(usize, program.blocks.len, 3) catch return error.OutOfMemory;
        const entries = try allocator.alloc(Entry, entry_count);
        @memset(entries, .{});
        var cache: HistoryCache = .{ .allocator = allocator, .entries = entries };
        errdefer cache.deinit();

        for (program.blocks) |block| switch (block.terminator) {
            .jump => |edge| try cache.populate(program, .{
                .source = block.id,
                .kind = .jump,
                .target = edge.target,
            }),
            .branch => |branch| {
                try cache.populate(program, .{
                    .source = block.id,
                    .kind = .branch_then,
                    .target = branch.then_edge.target,
                });
                try cache.populate(program, .{
                    .source = block.id,
                    .kind = .branch_else,
                    .target = branch.else_edge.target,
                });
            },
            else => {},
        };
        return cache;
    }

    pub fn deinit(self: *HistoryCache) void {
        for (self.entries) |entry| if (entry.history) |history| self.allocator.free(history.rewrites);
        self.allocator.free(self.entries);
        self.* = undefined;
    }

    pub fn get(self: *const HistoryCache, reference: ir.CfgEdgeRef) ?EdgeHistory {
        const entry_index = self.index(reference) orelse return null;
        const entry = self.entries[entry_index];
        if (!entry.built) return null;
        return entry.history;
    }

    fn populate(self: *HistoryCache, program: *const ir.Program, reference: ir.CfgEdgeRef) !void {
        const entry_index = self.index(reference) orelse return;
        if (self.entries[entry_index].built) return;
        self.entries[entry_index].built = true;
        self.entries[entry_index].history = try historyForCurrentEdgeAlloc(self.allocator, program, reference);
    }

    fn index(self: *const HistoryCache, reference: ir.CfgEdgeRef) ?usize {
        if (reference.source.index() >= self.entries.len / 3) return null;
        const kind_index: usize = switch (reference.kind) {
            .jump => 0,
            .branch_then => 1,
            .branch_else => 2,
        };
        return reference.source.index() * 3 + kind_index;
    }
};

pub const QueryRoot = union(enum) {
    none: void,
    one: ir.CfgEdgeRef,
    ambiguous: void,
};

pub fn queryRoot(program: *const ir.Program, query: ir.SolverQuery) QueryRoot {
    var found: ?ir.CfgEdgeRef = null;
    for (query.assumptions) |constraint_id| {
        if (constraint_id.index() >= program.constraints.len) return .{ .ambiguous = {} };
        const edge = switch (program.constraints[constraint_id.index()].scope) {
            .edge => |value| value,
            else => continue,
        };
        if (found) |existing| {
            if (!std.meta.eql(existing, edge)) return .{ .ambiguous = {} };
        } else {
            found = edge;
        }
    }
    return if (found) |edge| .{ .one = edge } else .{ .none = {} };
}

pub fn resolvedQueryEdge(program: *const ir.Program, query: ir.SolverQuery) ?ir.CfgEdgeRef {
    const root = switch (queryRoot(program, query)) {
        .one => |edge| edge,
        .none, .ambiguous => return null,
    };
    return referenceAfterPath(program, root, query.path_rewrites);
}

pub fn constraintEdgeValue(program: *const ir.Program, constraint: ir.Constraint) ?ir.Edge {
    const root = switch (constraint.scope) {
        .edge => |edge| edge,
        else => return null,
    };
    return edgeAfterPath(program, root, constraint.path_rewrites);
}

pub fn constraintSupportsPath(program: *const ir.Program, constraint: ir.Constraint, path: []const ir.EdgeRewriteId) bool {
    const root = switch (constraint.scope) {
        .edge => |edge| edge,
        else => return path.len == 0,
    };
    if (constraint.path_rewrites.len > path.len or
        !std.mem.eql(ir.EdgeRewriteId, constraint.path_rewrites, path[0..constraint.path_rewrites.len])) return false;
    var edge = edgeAfterPath(program, root, constraint.path_rewrites) orelse return false;
    for (path[constraint.path_rewrites.len..], constraint.path_rewrites.len..) |rewrite_id, path_index| {
        if (rewrite_id.index() >= program.edge_rewrites.len) return false;
        const rewrite = program.edge_rewrites[rewrite_id.index()];
        if (rewrite.source != root.source or rewrite.kind != root.kind or
            !sameEdge(rewrite.from, edge) or !rewriteUsesConstraint(program, rewrite, constraint.id) or
            rewrite.to.target == root.source or targetAppearsInPath(program, root.target, path[0..path_index], rewrite.to.target)) return false;
        edge = rewrite.to;
    }
    return true;
}

pub fn historyForCurrentEdgeAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    current: ir.CfgEdgeRef,
) !?EdgeHistory {
    const live = cfg_edge.value(program, current) orelse return null;
    if (live.target != current.target) return null;
    var root = current;
    var edge = live;
    var found = false;
    var path: std.ArrayList(ir.EdgeRewriteId) = .empty;
    defer path.deinit(allocator);
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.source != current.source or rewrite.kind != current.kind) continue;
        if (!found) {
            root.target = rewrite.from.target;
            edge = rewrite.from;
            found = true;
        }
        if (!sameEdge(edge, rewrite.from) or rewrite.to.target == root.source or
            targetAppearsInPath(program, root.target, path.items, rewrite.to.target)) return null;
        try path.append(allocator, rewrite.id);
        edge = rewrite.to;
    }
    if (!found) return .{ .root = current, .rewrites = try path.toOwnedSlice(allocator) };
    if (!sameEdge(edge, live)) return null;
    return .{ .root = root, .rewrites = try path.toOwnedSlice(allocator) };
}

pub fn pathForConstraintAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    constraint: ir.Constraint,
    current_edge: ir.CfgEdgeRef,
) !?[]ir.EdgeRewriteId {
    const scoped = switch (constraint.scope) {
        .edge => |edge| edge,
        else => return null,
    };
    if (scoped.source != current_edge.source or scoped.kind != current_edge.kind) return null;
    var edge = edgeAfterPath(program, scoped, constraint.path_rewrites) orelse return null;
    var path: std.ArrayList(ir.EdgeRewriteId) = .empty;
    defer path.deinit(allocator);
    try path.appendSlice(allocator, constraint.path_rewrites);
    const first_unlisted = if (constraint.path_rewrites.len == 0) 0 else constraint.path_rewrites[constraint.path_rewrites.len - 1].index() + 1;

    for (program.edge_rewrites, 0..) |rewrite, rewrite_index| {
        if (rewrite_index < first_unlisted) continue;
        if (rewrite.source != scoped.source or rewrite.kind != scoped.kind) continue;
        if (!sameEdge(rewrite.from, edge) or
            !rewriteUsesConstraint(program, rewrite, constraint.id) or
            targetAppearsInHistory(program.edge_rewrites[0..rewrite_index], scoped, rewrite.to.target))
        {
            return null;
        }
        try path.append(allocator, rewrite.id);
        edge = rewrite.to;
    }
    return if (edge.target == current_edge.target) try path.toOwnedSlice(allocator) else null;
}

pub fn constraintEffectiveTarget(program: *const ir.Program, constraint: ir.Constraint) ?ir.BlockId {
    const scoped = switch (constraint.scope) {
        .edge => |edge| edge,
        else => return null,
    };
    var edge = edgeAfterPath(program, scoped, constraint.path_rewrites) orelse return null;
    // Once an authenticated branch has consumed its terminator, an inactive
    // historical arm is no longer a live edge on which later implicit
    // forwarding rewrites can operate. Keep that constraint anchored to its
    // witnessed branch successor. Explicit path rewrites still apply above;
    // live jump/branch edges continue through the implicit history below.
    const followsImplicitHistory = cfg_edge.value(program, scoped) != null;
    if (!followsImplicitHistory) return edge.target;
    const first_unlisted = if (constraint.path_rewrites.len == 0) 0 else constraint.path_rewrites[constraint.path_rewrites.len - 1].index() + 1;
    for (program.edge_rewrites, 0..) |rewrite, rewrite_index| {
        if (rewrite_index < first_unlisted) continue;
        if (rewrite.source != scoped.source or rewrite.kind != scoped.kind) continue;
        if (!sameEdge(rewrite.from, edge)) return null;
        if (!rewriteUsesConstraint(program, rewrite, constraint.id)) return edge.target;
        // A clone fold may return to an endpoint the arm already visited, as rewrite admission allows
        // (validate_proofs.zig hasCanonicalRewritePrefix, validCloneFoldBoundary); the walk follows
        // positions (`sameEdge` above), so a fact the fold carries stays on the arm's history. The
        // `scoped.source` comparison is defensive: admission refuses every rewrite whose target is its
        // own source (validate_proofs.zig hasCanonicalRewritePrefix), a clone fold included.
        if (targetAppearsInHistory(program.edge_rewrites[0..rewrite_index], scoped, rewrite.to.target) and
            (rewrite.rule != .clone_fold or rewrite.to.target == scoped.source)) return null;
        edge = rewrite.to;
    }
    return edge.target;
}

pub fn rewriteUsesConstraint(program: *const ir.Program, rewrite: ir.CfgEdgeRewrite, constraint_id: ir.ConstraintId) bool {
    if (rewrite.rule == .forwarding_jump or rewrite.rule == .node_split or rewrite.rule == .clone_fold) return rewrite.certificate == null;
    const certificate_id = rewrite.certificate orelse return false;
    if (certificate_id.index() >= program.certificates.len) return false;
    const certificate = program.certificates[certificate_id.index()];
    if (certificate.id != certificate_id or certificate.resolution != .proved or certificate.query.index() >= program.queries.len) return false;
    const query = program.queries[certificate.query.index()];
    const resolved = resolvedQueryEdge(program, query) orelse return false;
    if (resolved.source != rewrite.source or resolved.kind != rewrite.kind or resolved.target != rewrite.from.target) return false;
    for (query.assumptions) |assumption| if (assumption == constraint_id) return true;
    return false;
}

pub fn sameEdge(left: ir.Edge, right: ir.Edge) bool {
    return left.target == right.target and std.mem.eql(ir.ValueId, left.arguments, right.arguments);
}

/// Returns the final historical branch arm retained by a discharged control
/// obligation after its source has become a jump. Proof validation authenticates
/// the obligation; this helper only recovers its structural edge history.
pub fn witnessedBranchEdge(
    program: *const ir.Program,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
) ?ir.Edge {
    if (kind == .jump) return null;
    const subject = witnessedControlBranch(program, source) orelse return null;
    return if (kind == .branch_then) subject.branch.then_edge else subject.branch.else_edge;
}

/// Returns the witnessed branch arm after the authenticated edge-rewrite
/// history, including the case where branch selection has already consumed
/// the source terminator.
pub fn replayedWitnessedBranchEdge(
    program: *const ir.Program,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
) ?ir.Edge {
    if (kind == .jump) return null;
    var current = witnessedBranchEdge(program, source, kind) orelse return null;
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.source != source or rewrite.kind != kind) continue;
        if (!sameEdge(rewrite.from, current)) return null;
        current = rewrite.to;
    }
    return current;
}

/// Reconstruct the live branch that preceded an authenticated branch
/// consumption. The CFG stores the selected arm as a jump, while node-split
/// replay still needs the branch terminator to compare the source and clone
/// bodies. Branch-arm rewrite history is applied before returning the view.
pub fn consumedBranchForReplay(program: *const ir.Program, source: ir.BlockId) ?ir.Branch {
    const subject = witnessedControlBranch(program, source) orelse return null;
    var branch = subject.branch;
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.source != source) continue;
        switch (rewrite.kind) {
            .branch_then => {
                if (!sameEdge(rewrite.from, branch.then_edge)) return null;
                branch.then_edge = rewrite.to;
            },
            .branch_else => {
                if (!sameEdge(rewrite.from, branch.else_edge)) return null;
                branch.else_edge = rewrite.to;
            },
            .jump => {},
        }
    }
    return branch;
}

pub fn witnessedBranchCondition(program: *const ir.Program, source: ir.BlockId) ?ir.ValueId {
    const subject = witnessedControlBranch(program, source) orelse return null;
    return subject.branch.condition;
}

fn witnessedControlBranch(program: *const ir.Program, source: ir.BlockId) ?ir.ControlBranchSubject {
    if (source.index() >= program.blocks.len or program.blocks[source.index()].terminator != .jump) return null;
    var found: ?ir.ControlBranchSubject = null;
    for (program.obligations) |obligation| {
        if (obligation.kind != .control_structure or obligation.status != .discharged or
            obligation.query == null or obligation.certificate == null or
            obligation.query.?.index() >= program.queries.len or
            obligation.certificate.?.index() >= program.certificates.len)
        {
            continue;
        }
        const subject = switch (obligation.subject) {
            .control_branch => |value| value,
            else => continue,
        };
        if (subject.block != source) continue;
        const certificate = program.certificates[obligation.certificate.?.index()];
        if (certificate.id != obligation.certificate.? or
            certificate.query != obligation.query.? or
            certificate.resolution != .proved) continue;
        if (found) |existing| {
            if (existing.branch.condition != subject.branch.condition or
                !sameEdge(existing.branch.then_edge, subject.branch.then_edge) or
                !sameEdge(existing.branch.else_edge, subject.branch.else_edge)) return null;
        } else {
            found = subject;
        }
    }
    return found;
}

fn referenceAfterPath(program: *const ir.Program, root: ir.CfgEdgeRef, path: []const ir.EdgeRewriteId) ?ir.CfgEdgeRef {
    var current = root;
    for (path, 0..) |rewrite_id, path_index| {
        if (rewrite_id.index() >= program.edge_rewrites.len) return null;
        const rewrite = program.edge_rewrites[rewrite_id.index()];
        if (rewrite.id != rewrite_id or
            rewrite.source != current.source or
            rewrite.kind != current.kind or
            rewrite.from.target != current.target or
            rewrite.to.target == current.source or
            targetAppearsInPath(program, root.target, path[0..path_index], rewrite.to.target)) return null;
        current.target = rewrite.to.target;
    }
    return current;
}

fn edgeAfterPath(program: *const ir.Program, root: ir.CfgEdgeRef, path: []const ir.EdgeRewriteId) ?ir.Edge {
    var current = rootEdgeValue(program, root, path) orelse return null;
    for (path, 0..) |rewrite_id, path_index| {
        if (rewrite_id.index() >= program.edge_rewrites.len) return null;
        const rewrite = program.edge_rewrites[rewrite_id.index()];
        if (rewrite.id != rewrite_id or
            rewrite.source != root.source or
            rewrite.kind != root.kind or
            !sameEdge(rewrite.from, current) or
            rewrite.to.target == root.source or
            targetAppearsInPath(program, root.target, path[0..path_index], rewrite.to.target)) return null;
        current = rewrite.to;
    }
    return current;
}

fn rootEdgeValue(program: *const ir.Program, root: ir.CfgEdgeRef, path: []const ir.EdgeRewriteId) ?ir.Edge {
    if (path.len != 0) {
        const first_id = path[0];
        if (first_id.index() >= program.edge_rewrites.len) return null;
        const first = program.edge_rewrites[first_id.index()];
        if (first.source != root.source or first.kind != root.kind or first.from.target != root.target) return null;
        return first.from;
    }
    if (cfg_edge.target(program, root) != null) return cfg_edge.value(program, root);
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.source == root.source and rewrite.kind == root.kind) {
            return if (rewrite.from.target == root.target) rewrite.from else null;
        }
    }
    const historical = witnessedBranchEdge(program, root.source, root.kind) orelse return null;
    return if (historical.target == root.target) historical else null;
}

fn targetAppearsInPath(
    program: *const ir.Program,
    root_target: ir.BlockId,
    prior_rewrites: []const ir.EdgeRewriteId,
    candidate: ir.BlockId,
) bool {
    if (candidate == root_target) return true;
    for (prior_rewrites) |rewrite_id| {
        if (rewrite_id.index() >= program.edge_rewrites.len) return true;
        if (program.edge_rewrites[rewrite_id.index()].to.target == candidate) return true;
    }
    return false;
}

fn targetAppearsInHistory(
    prior_rewrites: []const ir.CfgEdgeRewrite,
    root: ir.CfgEdgeRef,
    candidate: ir.BlockId,
) bool {
    if (candidate == root.source or candidate == root.target) return true;
    for (prior_rewrites) |rewrite| {
        if (rewrite.source == root.source and rewrite.kind == root.kind and rewrite.to.target == candidate) return true;
    }
    return false;
}
