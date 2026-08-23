const std = @import("std");
const ir = @import("ir.zig");
const solver = @import("solver.zig");
const diagnostics = @import("diagnostics.zig");
const validate_solver_terms = @import("validate_solver_terms.zig");
const validate_solver_artifacts = @import("validate_solver_artifacts.zig");
const readable_scope = @import("readable_scope.zig");
const cfg_edge = @import("cfg_edge.zig");
const edge_path = @import("edge_path.zig");
const edge_facts = @import("edge_facts.zig");
const control_flow = @import("control_flow.zig");
const proof_plan = @import("proof_plan.zig");
const proof_closure = @import("proof_closure.zig");
const cfg = @import("cfg.zig");
const type_validation = @import("validate_types.zig");
const control_query_plan = @import("control_query_plan.zig");
const node_split = @import("node_split.zig");

pub fn validate(
    report: *diagnostics.Report,
    program: *const ir.Program,
    profile: ir.AdmissionProfile,
    scope: ?*const readable_scope.Scope,
) !void {
    try validateSolver(report, program);
    try validateClaimsAndObligations(report, program, profile, scope);
}

pub fn validateSolverInputs(report: *diagnostics.Report, program: *const ir.Program) !void {
    for (program.solver_terms, 0..) |term, index| if (term.id.index() != index) try report.add(.noncanonical_solver_term_id, index);
    for (program.constraints, 0..) |constraint, index| if (constraint.id.index() != index) try report.add(.noncanonical_constraint_id, index);
    for (program.queries, 0..) |query, index| if (query.id.index() != index) try report.add(.noncanonical_query_id, index);
    for (program.solver_models, 0..) |model, index| if (model.id.index() != index) try report.add(.noncanonical_solver_model_id, index);
    for (program.unsat_cores, 0..) |core, index| if (core.id.index() != index) try report.add(.noncanonical_unsat_core_id, index);
    for (program.certificates, 0..) |certificate, index| if (certificate.id.index() != index) try report.add(.noncanonical_certificate_id, index);
    for (program.edge_rewrites, 0..) |rewrite, index| if (rewrite.id.index() != index) try report.add(.noncanonical_edge_rewrite_id, index);
    try validateSolver(report, program);
}

fn validateSolver(report: *diagnostics.Report, program: *const ir.Program) !void {
    try validate_solver_terms.validate(report, program);

    for (program.constraints, 0..) |constraint, constraint_index| {
        if (!validId(constraint.predicate, program.solver_terms.len)) {
            try report.add(.invalid_constraint_predicate, constraint_index);
        } else if (program.solver_terms[constraint.predicate.index()].sort.kind != .boolean) {
            try report.add(.invalid_constraint_predicate, constraint_index);
        }
        for (constraint.evidence) |evidence_id| if (!validId(evidence_id, program.evidence.len)) try report.add(.invalid_evidence_reference, constraint_index);
        var structural_evidence = false;
        for (constraint.evidence) |evidence_id| {
            if (!validId(evidence_id, program.evidence.len)) continue;
            if (program.evidence[evidence_id.index()].kind == .structural_derivation) {
                structural_evidence = true;
                if (!edge_facts.isStructuralEvidence(program.evidence[evidence_id.index()])) {
                    try report.add(.invalid_structural_derivation, constraint_index);
                }
            }
        }
        if (structural_evidence and (constraint.evidence.len != 1 or !edge_facts.replaysConstraint(program, constraint))) {
            try report.add(.invalid_structural_derivation, constraint_index);
        }
        switch (constraint.scope) {
            .explicit_only, .program => if (constraint.path_rewrites.len != 0) try report.add(.invalid_constraint_path_rewrite, constraint_index),
            .function => |function_id| {
                if (!validId(function_id, program.functions.len)) try report.add(.invalid_constraint_scope, constraint_index);
                if (constraint.path_rewrites.len != 0) try report.add(.invalid_constraint_path_rewrite, constraint_index);
            },
            .block => |block_id| {
                if (!validId(block_id, program.blocks.len)) try report.add(.invalid_constraint_scope, constraint_index);
                if (constraint.path_rewrites.len != 0) try report.add(.invalid_constraint_path_rewrite, constraint_index);
            },
            .edge => if (!validConstraintEdgeScope(program, constraint)) try report.add(.invalid_constraint_scope, constraint_index),
        }
        for (constraint.path_rewrites, 0..) |rewrite_id, rewrite_index| {
            if (!validId(rewrite_id, program.edge_rewrites.len) or
                (rewrite_index != 0 and constraint.path_rewrites[rewrite_index - 1].index() >= rewrite_id.index()))
            {
                try report.add(.invalid_constraint_path_rewrite, constraint_index);
            }
        }
        if (constraint.path_rewrites.len != 0 and edge_path.constraintEdgeValue(program, constraint) == null) {
            try report.add(.invalid_constraint_path_rewrite, constraint_index);
        }
        if (constraint.scope != .explicit_only and constraint.evidence.len == 0) {
            try report.add(.scoped_constraint_without_evidence, constraint_index);
        }
    }

    for (program.queries, 0..) |query, query_index| {
        if (!validId(query.goal, program.solver_terms.len)) {
            try report.add(.invalid_query_reference, query_index);
        } else if (program.solver_terms[query.goal.index()].sort.kind != .boolean) {
            try report.add(.invalid_query_reference, query_index);
        }
        for (query.assumptions, 0..) |constraint_id, assumption_index| {
            if (!validId(constraint_id, program.constraints.len)) try report.add(.invalid_query_reference, query_index);
            for (query.assumptions[0..assumption_index]) |prior_id| {
                if (prior_id == constraint_id) {
                    try report.add(.duplicate_query_assumption, query_index);
                    break;
                }
            }
        }
        for (query.path_rewrites, 0..) |rewrite_id, rewrite_index| {
            if (!validId(rewrite_id, program.edge_rewrites.len) or
                (rewrite_index != 0 and query.path_rewrites[rewrite_index - 1].index() >= rewrite_id.index()) or
                (validId(rewrite_id, program.edge_rewrites.len) and !rewriteAvailableToQuery(program, program.edge_rewrites[rewrite_id.index()], query.id)))
            {
                try report.add(.invalid_query_path_rewrite, query_index);
            }
        }
        if (query.path_rewrites.len != 0 and edge_path.resolvedQueryEdge(program, query) == null) {
            try report.add(.invalid_query_path_rewrite, query_index);
        }
        switch (edge_path.queryRoot(program, query)) {
            .ambiguous => try report.add(.invalid_query_path_rewrite, query_index),
            .one => {
                for (query.assumptions) |constraint_id| {
                    if (!validId(constraint_id, program.constraints.len)) continue;
                    const constraint = program.constraints[constraint_id.index()];
                    if (constraint.scope == .edge and !edge_path.constraintSupportsPath(program, constraint, query.path_rewrites)) {
                        try report.add(.invalid_query_path_rewrite, query_index);
                    }
                }
            },
            .none => {},
        }
    }

    try validate_solver_artifacts.validate(report, program);

    var rewrite_history = try RewriteHistory.init(report.allocator, program);
    defer rewrite_history.deinit();
    const has_node_split = for (program.edge_rewrites) |rewrite| {
        if (rewrite.rule == .node_split) break true;
    } else false;
    var replay_index: ?node_split.ReplayIndex = if (has_node_split)
        try node_split.ReplayIndex.init(report.allocator, program)
    else
        null;
    defer if (replay_index) |*index| index.deinit();
    for (program.edge_rewrites, 0..) |rewrite, rewrite_index| {
        if (!try validEdgeRewriteWithHistory(
            report.allocator,
            program,
            rewrite,
            rewrite_index,
            &rewrite_history,
            if (replay_index) |*index| index else null,
        )) {
            try report.add(.invalid_edge_rewrite, rewrite_index);
        }
    }
}

fn validConstraintEdgeScope(program: *const ir.Program, constraint: ir.Constraint) bool {
    const edge = switch (constraint.scope) {
        .edge => |value| value,
        else => return false,
    };
    if (cfg_edge.isValid(program, edge)) {
        if (cfg_edge.isCurrent(program, edge)) return true;
        const current = cfg_edge.value(program, edge) orelse return false;
        return edge_path.constraintEffectiveTarget(program, constraint) == current.target;
    }
    // An unqualified constraint remains anchored to the witnessed branch arm
    // after branch selection consumes the source terminator. An explicit
    // constraint path is different: it opts into replaying the authenticated
    // continuation history and must validate against that final edge.
    const effective = if (constraint.path_rewrites.len == 0)
        edge_path.witnessedBranchEdge(program, edge.source, edge.kind) orelse return false
    else
        edge_path.replayedWitnessedBranchEdge(program, edge.source, edge.kind) orelse return false;
    return edge_path.constraintEffectiveTarget(program, constraint) == effective.target;
}

const RewriteArmKey = struct {
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
};

const RewriteEndpointKey = struct {
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    target: ir.BlockId,
};

const RewriteArmState = struct {
    count: usize = 0,
    chain_valid: bool = true,
    last_to: ?ir.Edge = null,
};

/// Precompute the append-only rewrite facts used by proof validation.  The
/// serialized rewrite list is ordered history, so each arm's prefix state and
/// endpoint set can be updated once instead of rescanning the full prefix for
/// every rewrite.
const RewriteHistory = struct {
    allocator: std.mem.Allocator,
    ordinals: []usize,
    canonical_prefix: []bool,
    target_fresh: []bool,
    superseded: []bool,
    arm_states: std.AutoHashMapUnmanaged(RewriteArmKey, RewriteArmState) = .empty,
    endpoints: std.AutoHashMapUnmanaged(RewriteEndpointKey, void) = .empty,

    fn init(allocator: std.mem.Allocator, program: *const ir.Program) !RewriteHistory {
        const ordinals = try allocator.alloc(usize, program.edge_rewrites.len);
        errdefer allocator.free(ordinals);
        const canonical_prefix = try allocator.alloc(bool, program.edge_rewrites.len);
        errdefer allocator.free(canonical_prefix);
        const target_fresh = try allocator.alloc(bool, program.edge_rewrites.len);
        errdefer allocator.free(target_fresh);
        const superseded = try allocator.alloc(bool, program.edge_rewrites.len);
        errdefer allocator.free(superseded);

        var history = RewriteHistory{
            .allocator = allocator,
            .ordinals = ordinals,
            .canonical_prefix = canonical_prefix,
            .target_fresh = target_fresh,
            .superseded = superseded,
        };
        errdefer history.deinit();

        var later_arms: std.AutoHashMapUnmanaged(RewriteArmKey, void) = .empty;
        defer later_arms.deinit(allocator);
        var reverse_index = program.edge_rewrites.len;
        while (reverse_index != 0) {
            reverse_index -= 1;
            const rewrite = program.edge_rewrites[reverse_index];
            const key = RewriteArmKey{ .source = rewrite.source, .kind = rewrite.kind };
            history.superseded[reverse_index] = later_arms.contains(key);
            try later_arms.put(allocator, key, {});
        }

        for (program.edge_rewrites, 0..) |rewrite, rewrite_index| {
            const arm_key = RewriteArmKey{ .source = rewrite.source, .kind = rewrite.kind };
            const state_entry = try history.arm_states.getOrPut(allocator, arm_key);
            if (!state_entry.found_existing) state_entry.value_ptr.* = .{};
            const state = state_entry.value_ptr;

            history.ordinals[rewrite_index] = state.count;
            history.canonical_prefix[rewrite_index] = state.chain_valid and
                (if (state.last_to) |last_to| edge_path.sameEdge(last_to, rewrite.from) else true);

            history.target_fresh[rewrite_index] = !history.endpoints.contains(.{
                .source = rewrite.source,
                .kind = rewrite.kind,
                .target = rewrite.to.target,
            });
            try history.endpoints.put(allocator, .{
                .source = rewrite.source,
                .kind = rewrite.kind,
                .target = rewrite.from.target,
            }, {});
            try history.endpoints.put(allocator, .{
                .source = rewrite.source,
                .kind = rewrite.kind,
                .target = rewrite.to.target,
            }, {});

            state.chain_valid = history.canonical_prefix[rewrite_index];
            state.last_to = rewrite.to;
            state.count += 1;
        }
        return history;
    }

    fn deinit(self: *RewriteHistory) void {
        self.endpoints.deinit(self.allocator);
        self.arm_states.deinit(self.allocator);
        self.allocator.free(self.superseded);
        self.allocator.free(self.target_fresh);
        self.allocator.free(self.canonical_prefix);
        self.allocator.free(self.ordinals);
        self.* = undefined;
    }

    fn queryPathMatches(
        self: *const RewriteHistory,
        program: *const ir.Program,
        rewrite: ir.CfgEdgeRewrite,
        rewrite_index: usize,
        query_path: []const ir.EdgeRewriteId,
    ) bool {
        if (rewrite_index >= self.ordinals.len or query_path.len != self.ordinals[rewrite_index]) return false;
        for (query_path, 0..) |path_id, path_index| {
            const prior_index = path_id.index();
            if (prior_index >= rewrite_index or prior_index >= program.edge_rewrites.len) return false;
            const prior = program.edge_rewrites[prior_index];
            if (prior.source != rewrite.source or prior.kind != rewrite.kind or
                self.ordinals[prior_index] != path_index)
            {
                return false;
            }
        }
        return true;
    }
};

fn validEdgeRewrite(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    rewrite: ir.CfgEdgeRewrite,
    rewrite_index: usize,
) !bool {
    var history = try RewriteHistory.init(allocator, program);
    defer history.deinit();
    return validEdgeRewriteWithHistory(allocator, program, rewrite, rewrite_index, &history, null);
}

fn validEdgeRewriteWithHistory(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    rewrite: ir.CfgEdgeRewrite,
    rewrite_index: usize,
    history: *const RewriteHistory,
    replay_index: ?*const node_split.ReplayIndex,
) !bool {
    if (!validId(rewrite.source, program.blocks.len) or
        !validId(rewrite.from.target, program.blocks.len) or
        !validId(rewrite.to.target, program.blocks.len))
    {
        return false;
    }
    if (!validNodeSplitGroup(program, rewrite, rewrite_index)) return false;
    for (rewrite.from.arguments) |argument| if (!validId(argument, program.values.len)) return false;
    for (rewrite.to.arguments) |argument| if (!validId(argument, program.values.len)) return false;
    const replayed = switch (rewrite.rule) {
        .proved_branch => blk: {
            const certificate_id = rewrite.certificate orelse return false;
            if (!validId(certificate_id, program.certificates.len)) return false;
            const certificate = program.certificates[certificate_id.index()];
            if (certificate.id != certificate_id or certificate.resolution != .proved or !validId(certificate.query, program.queries.len)) return false;
            const query = program.queries[certificate.query.index()];
            const resolved = edge_path.resolvedQueryEdge(program, query) orelse return false;
            if (resolved.source != rewrite.source or resolved.kind != rewrite.kind or resolved.target != rewrite.from.target) return false;
            if (!hasCanonicalRewritePrefix(program, rewrite, rewrite_index, query.path_rewrites, history)) return false;
            break :blk try control_flow.replayQuerySpecialization(allocator, program, query, rewrite.from) orelse return false;
        },
        .forwarding_jump => blk: {
            if (rewrite.certificate != null or !hasCanonicalRewritePrefix(program, rewrite, rewrite_index, null, history)) return false;
            break :blk try control_flow.replayForwardingJump(allocator, program, rewrite.from) orelse return false;
        },
        .node_split => blk: {
            if (rewrite.certificate != null or !hasCanonicalRewritePrefix(program, rewrite, rewrite_index, null, history)) return false;
            if (replay_index) |index| {
                break :blk try control_flow.replayNodeSplitWithIndex(
                    allocator,
                    program,
                    rewrite.from,
                    rewrite.to.target,
                    rewrite.node_split_group,
                    index,
                ) orelse return false;
            }
            break :blk try control_flow.replayNodeSplit(
                allocator,
                program,
                rewrite.from,
                rewrite.to.target,
                rewrite.node_split_group,
            ) orelse return false;
        },
        .clone_fold => blk: {
            if (rewrite.certificate != null or rewrite.node_split_group == null or
                !validCloneFoldBoundary(program, rewrite, rewrite_index) or
                !hasCanonicalRewritePrefix(program, rewrite, rewrite_index, null, history)) return false;
            break :blk try node_split.replayCloneFold(
                allocator,
                program,
                rewrite.from,
                rewrite.to.target,
                rewrite.node_split_group.?,
            ) orelse return false;
        },
    };
    defer if (replayed.arguments.len != 0) allocator.free(replayed.arguments);
    if (!edge_path.sameEdge(replayed, rewrite.to)) return false;

    if (!history.superseded[rewrite_index]) {
        const current = cfg_edge.value(program, .{
            .source = rewrite.source,
            .kind = rewrite.kind,
            .target = rewrite.to.target,
        }) orelse edge_path.replayedWitnessedBranchEdge(program, rewrite.source, rewrite.kind) orelse return false;
        if (!edge_path.sameEdge(current, rewrite.to)) return false;
    }
    return true;
}

fn validNodeSplitGroup(program: *const ir.Program, rewrite: ir.CfgEdgeRewrite, rewrite_index: usize) bool {
    const group = rewrite.node_split_group orelse return true;
    const group_index = group.index();
    if (group_index >= program.edge_rewrites.len) return false;
    const root = program.edge_rewrites[group_index];
    if (root.id.index() != group_index or root.rule != .node_split or root.node_split_group != group) return false;
    return switch (rewrite.rule) {
        .node_split => group_index <= rewrite_index,
        .clone_fold => group_index < rewrite_index,
        .proved_branch, .forwarding_jump => false,
    };
}

fn validCloneFoldBoundary(
    program: *const ir.Program,
    rewrite: ir.CfgEdgeRewrite,
    rewrite_index: usize,
) bool {
    const group = rewrite.node_split_group orelse return false;
    if (rewrite_index > program.edge_rewrites.len) return false;
    for (program.edge_rewrites[0..rewrite_index]) |root| {
        if (root.rule != .node_split or root.node_split_group != group or
            root.from.target != rewrite.to.target or root.to.target != rewrite.from.target or
            !std.mem.eql(ir.ValueId, root.from.arguments, rewrite.to.arguments) or
            !std.mem.eql(ir.ValueId, root.to.arguments, rewrite.from.arguments)) continue;
        // A fold may enter a target clone from a separately split source
        // endpoint.  The clone mapping is the semantic boundary being
        // replayed; requiring the same source edge would reject an
        // independently composed but authenticated target fold.
        return true;
    }
    return false;
}

fn hasCanonicalRewritePrefix(
    program: *const ir.Program,
    rewrite: ir.CfgEdgeRewrite,
    rewrite_index: usize,
    query_path: ?[]const ir.EdgeRewriteId,
    history: *const RewriteHistory,
) bool {
    if (rewrite_index >= history.canonical_prefix.len or
        !history.canonical_prefix[rewrite_index] or
        // A clone fold intentionally returns to the root target already
        // recorded by its node-split proof.  Its inverse-root boundary is
        // checked by validCloneFoldBoundary before this exception is reached.
        (!history.target_fresh[rewrite_index] and rewrite.rule != .clone_fold) or
        rewrite.to.target == rewrite.source or
        rewrite.from.target == rewrite.to.target)
    {
        return false;
    }
    if (query_path) |path| {
        if (!history.queryPathMatches(program, rewrite, rewrite_index, path)) return false;
    }
    return true;
}

fn rewriteAvailableToQuery(program: *const ir.Program, rewrite: ir.CfgEdgeRewrite, query_id: ir.QueryId) bool {
    return switch (rewrite.rule) {
        .forwarding_jump, .node_split, .clone_fold => rewrite.certificate == null,
        .proved_branch => blk: {
            const certificate_id = rewrite.certificate orelse break :blk false;
            if (!validId(certificate_id, program.certificates.len)) break :blk false;
            const certificate = program.certificates[certificate_id.index()];
            break :blk validId(certificate.query, program.queries.len) and certificate.query.index() < query_id.index();
        },
    };
}

test "node split rewrite replay rejects every mutable witness surface" {
    const function_id = ir.FunctionId.fromIndex(0);
    const edge_source = ir.BlockId.fromIndex(0);
    const original = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const parameter = ir.ValueId.fromIndex(0);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const base_blocks = [_]ir.Block{
        .{ .id = edge_source, .function = function_id, .terminator = .{ .jump = .{ .target = clone } }, .evidence = &.{evidence_id} },
        .{ .id = original, .function = function_id, .terminator = .{ .jump = .{ .target = exit } }, .evidence = &.{evidence_id} },
        .{ .id = clone, .function = function_id, .terminator = .{ .jump = .{ .target = exit } }, .evidence = &.{evidence_id} },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} }, .evidence = &.{evidence_id} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{parameter},
        .blocks = &.{ edge_source, original, clone, exit },
        .entry_block = edge_source,
        .evidence = &.{evidence_id},
    }};
    const values = [_]ir.Value{.{ .id = parameter, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } }};
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .structural_derivation, .locator = "fixture:node-split-replay" }};
    const base_rewrite: ir.CfgEdgeRewrite = .{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = edge_source,
        .kind = .jump,
        .from = .{ .target = original },
        .to = .{ .target = clone },
        .rule = .node_split,
    };
    var program: ir.Program = .{
        .program_id = "node-split-replay",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &base_blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
        .edge_rewrites = &.{base_rewrite},
    };
    try std.testing.expect(try validEdgeRewrite(std.testing.allocator, &program, base_rewrite, 0));

    var changed_blocks = base_blocks;
    changed_blocks[clone.index()].terminator = .{ .return_values = &.{} };
    program.blocks = &changed_blocks;
    try std.testing.expect(!try validEdgeRewrite(std.testing.allocator, &program, base_rewrite, 0));

    changed_blocks = base_blocks;
    changed_blocks[clone.index()].parameters = &.{parameter};
    program.blocks = &changed_blocks;
    try std.testing.expect(!try validEdgeRewrite(std.testing.allocator, &program, base_rewrite, 0));

    changed_blocks = base_blocks;
    changed_blocks[clone.index()].instructions = &.{ir.InstructionId.fromIndex(0)};
    program.blocks = &changed_blocks;
    try std.testing.expect(!try validEdgeRewrite(std.testing.allocator, &program, base_rewrite, 0));

    changed_blocks = base_blocks;
    changed_blocks[clone.index()].evidence = &.{};
    program.blocks = &changed_blocks;
    try std.testing.expect(!try validEdgeRewrite(std.testing.allocator, &program, base_rewrite, 0));

    program.blocks = &base_blocks;
    var changed_rewrite = base_rewrite;
    changed_rewrite.from.arguments = &.{parameter};
    changed_rewrite.to.arguments = &.{parameter};
    program.edge_rewrites = &.{changed_rewrite};
    try std.testing.expect(!try validEdgeRewrite(std.testing.allocator, &program, changed_rewrite, 0));

    changed_rewrite = base_rewrite;
    changed_rewrite.certificate = ir.CertificateId.fromIndex(0);
    program.edge_rewrites = &.{changed_rewrite};
    try std.testing.expect(!try validEdgeRewrite(std.testing.allocator, &program, changed_rewrite, 0));
}

test "node split group provenance names a canonical structural root" {
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const base_rewrite: ir.CfgEdgeRewrite = .{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = ir.BlockId.fromIndex(0),
        .kind = .jump,
        .from = .{ .target = ir.BlockId.fromIndex(1) },
        .to = .{ .target = ir.BlockId.fromIndex(2) },
        .rule = .node_split,
        .node_split_group = group,
    };
    var program: ir.Program = .{
        .program_id = "node-split-group-provenance",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &.{base_rewrite},
    };
    try std.testing.expect(validNodeSplitGroup(&program, base_rewrite, 0));

    var changed = base_rewrite;
    changed.rule = .forwarding_jump;
    program.edge_rewrites = &.{changed};
    try std.testing.expect(!validNodeSplitGroup(&program, changed, 0));

    changed = base_rewrite;
    changed.node_split_group = ir.NodeSplitGroupId.fromIndex(1);
    program.edge_rewrites = &.{changed};
    try std.testing.expect(!validNodeSplitGroup(&program, changed, 0));

    var ungrouped_root = base_rewrite;
    ungrouped_root.node_split_group = null;
    var grouped_follower = base_rewrite;
    grouped_follower.id = ir.EdgeRewriteId.fromIndex(1);
    const rootless_group = [_]ir.CfgEdgeRewrite{ ungrouped_root, grouped_follower };
    program.edge_rewrites = &rootless_group;
    try std.testing.expect(!validNodeSplitGroup(&program, grouped_follower, 1));

    try std.testing.expect(validNodeSplitGroup(&program, ungrouped_root, 0));
}

test "clone fold replay rejects altered clone semantics" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const owner_exit = ir.BlockId.fromIndex(2);
    const clone = ir.BlockId.fromIndex(3);
    const clone_exit = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const owner_result = ir.ValueId.fromIndex(1);
    const clone_result = ir.ValueId.fromIndex(2);
    const owner_instruction = ir.InstructionId.fromIndex(0);
    const clone_instruction = ir.InstructionId.fromIndex(1);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const root_id = ir.EdgeRewriteId.fromIndex(0);
    const fold_id = ir.EdgeRewriteId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = owner },
        } } },
        .{ .id = owner, .function = function_id, .instructions = &.{owner_instruction}, .terminator = .{ .jump = .{ .target = owner_exit } } },
        .{ .id = owner_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = clone, .function = function_id, .instructions = &.{clone_instruction}, .terminator = .{ .jump = .{ .target = clone_exit } } },
        .{ .id = clone_exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, owner, owner_exit, clone, clone_exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = owner_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = owner_instruction, .index = 0 } } },
        .{ .id = clone_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = clone_instruction, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = owner_instruction, .block = owner, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{owner_result}, .effects = .pure },
        .{ .id = clone_instruction, .block = clone, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{clone_result}, .effects = .pure },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = root_id,
            .source = entry,
            .kind = .branch_then,
            .from = .{ .target = owner },
            .to = .{ .target = clone },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = clone,
            .kind = .jump,
            .from = .{ .target = owner_exit },
            .to = .{ .target = clone_exit },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = fold_id,
            .source = entry,
            .kind = .branch_then,
            .from = .{ .target = clone },
            .to = .{ .target = owner },
            .rule = .clone_fold,
            .node_split_group = group,
        },
    };
    var program = ir.Program{
        .program_id = "clone-fold-replay",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .edge_rewrites = &rewrites,
    };

    try std.testing.expect(try validEdgeRewrite(std.testing.allocator, &program, rewrites[2], 2));

    var changed_instructions = instructions;
    changed_instructions[clone_instruction.index()].operation = .{ .constant = .{ .integer = "2" } };
    program.instructions = &changed_instructions;
    try std.testing.expect(!try validEdgeRewrite(std.testing.allocator, &program, rewrites[2], 2));

    changed_instructions = instructions;
    changed_instructions[clone_instruction.index()].effects = .dynamic_call;
    program.instructions = &changed_instructions;
    try std.testing.expect(!try validEdgeRewrite(std.testing.allocator, &program, rewrites[2], 2));

    program.instructions = &instructions;
    var changed_blocks = blocks;
    changed_blocks[clone.index()].terminator = .{ .return_values = &.{} };
    program.blocks = &changed_blocks;
    try std.testing.expect(!try validEdgeRewrite(std.testing.allocator, &program, rewrites[2], 2));

    // A group may contain later split arms after its canonical root.  The
    // fold must bind to the matching prior arm, not to group.index().
    const grouped_rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .branch_then,
            .from = .{ .target = owner },
            .to = .{ .target = clone },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = entry,
            .kind = .branch_else,
            .from = .{ .target = owner },
            .to = .{ .target = clone },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = entry,
            .kind = .branch_else,
            .from = .{ .target = clone },
            .to = .{ .target = owner },
            .rule = .clone_fold,
            .node_split_group = group,
        },
    };
    program.blocks = &blocks;
    program.edge_rewrites = &grouped_rewrites;
    try std.testing.expect(validCloneFoldBoundary(&program, grouped_rewrites[2], 2));
}

fn validateClaimsAndObligations(
    report: *diagnostics.Report,
    program: *const ir.Program,
    profile: ir.AdmissionProfile,
    scope: ?*const readable_scope.Scope,
) !void {
    for (program.claims, 0..) |claim, claim_index| {
        if (!validEntity(program, claim.subject) or !validId(claim.predicate, program.solver_terms.len)) try report.add(.invalid_claim_reference, claim_index);
        for (claim.evidence) |evidence_id| if (!validId(evidence_id, program.evidence.len)) try report.add(.invalid_evidence_reference, claim_index);
        switch (claim.purpose) {
            .generic_predicate => {},
            .effect_summary => |claimed_effects| switch (claim.subject) {
                .instruction => |instruction_id| {
                    if (!validId(instruction_id, program.instructions.len)) {
                        try report.add(.claim_purpose_subject_mismatch, claim_index);
                    } else if (!sameEffects(claimed_effects, program.instructions[instruction_id.index()].effects)) {
                        try report.add(.claim_effect_summary_mismatch, claim_index);
                    }
                },
                else => try report.add(.claim_purpose_subject_mismatch, claim_index),
            },
            .no_metamethod_dispatch => |claimed_effects| try validateInstructionEffectPurpose(report, program, claim.subject, claimed_effects, claim_index),
            .primitive_operator_domain => |claimed_effects| try validateInstructionEffectPurpose(report, program, claim.subject, claimed_effects, claim_index),
        }
        const requires_semantic_atom = switch (claim.purpose) {
            .generic_predicate => false,
            else => true,
        };
        if (requires_semantic_atom and
            validEntity(program, claim.subject) and
            validId(claim.predicate, program.solver_terms.len) and
            !claimPredicateMatchesPurpose(program, claim))
        {
            try report.add(.claim_predicate_purpose_mismatch, claim_index);
        }

        if (claim.certificate) |certificate_id| {
            if (!validId(certificate_id, program.certificates.len)) {
                try report.add(.invalid_certificate_reference, claim_index);
            } else {
                const certificate = program.certificates[certificate_id.index()];
                if (validId(certificate.query, program.queries.len)) {
                    const query = program.queries[certificate.query.index()];
                    if (query.goal != claim.predicate) try report.add(.invalid_certificate_reference, claim_index);
                    if (claim.query) |claim_query| if (claim_query != certificate.query) try report.add(.invalid_certificate_reference, claim_index);
                    const agrees = switch (claim.status) {
                        .proved => certificate.resolution == .proved,
                        .disproved => certificate.resolution == .disproved,
                        .unproven => certificate.resolution == .unknown,
                    };
                    if (!agrees) try report.add(.certificate_resolution_mismatch, claim_index);
                    if (certificate.resolution != .unknown and !evidenceCovers(certificate.evidence, claim.evidence)) {
                        try report.add(.claim_certificate_evidence_mismatch, claim_index);
                    }
                }
            }
        }
        if (claim.query) |query_id| {
            if (!validId(query_id, program.queries.len)) {
                try report.add(.invalid_claim_query_reference, claim_index);
            } else {
                const query = program.queries[query_id.index()];
                if (query.goal != claim.predicate or (query.kind != .prove_true and query.kind != .prove_equivalent)) {
                    try report.add(.invalid_claim_query_reference, claim_index);
                }
            }
        }

        if (claim.status == .proved and claim.evidence.len == 0 and claim.certificate == null) try report.add(.proved_claim_without_proof, claim_index);
        if (profile == .readable_luau and
            (scope == null or scope.?.entity(claim.subject)) and
            claim.required_for_emission and
            claim.status != .proved)
        {
            try report.add(.required_claim_unproved, claim_index);
        }
        switch (claim.subject) {
            .instruction => |instruction_id| {
                if (validId(instruction_id, program.instructions.len) and
                    !instructionListsClaim(program.instructions[instruction_id.index()], claim.id))
                {
                    try report.add(.unlisted_instruction_claim, claim_index);
                }
            },
            else => {},
        }
    }

    for (program.obligations, 0..) |obligation, obligation_index| {
        const valid_subject = validObligationSubject(program, obligation.subject);
        if (!valid_subject) try report.add(.invalid_obligation_reference, obligation_index);
        switch (obligation.subject) {
            .control_branch => |subject| try validateControlBranchObligation(report, program, obligation, subject, obligation_index),
            .block => |block_id| if (isUnwitnessedConsumedLiteralBranch(program, obligation, block_id)) {
                try report.add(.invalid_control_branch_witness, obligation_index);
            },
            else => {},
        }
        for (obligation.evidence) |evidence_id| {
            if (!validId(evidence_id, program.evidence.len)) try report.add(.invalid_evidence_reference, obligation_index);
        }
        const valid_requirement = if (obligation.requirement) |requirement| blk: {
            const valid = validId(requirement.predicate, program.solver_terms.len) and
                program.solver_terms[requirement.predicate.index()].sort.kind == .boolean;
            if (!valid) try report.add(.invalid_obligation_requirement_reference, obligation_index);
            break :blk valid;
        } else true;
        if (obligation.query) |query_id| {
            if (!validId(query_id, program.queries.len)) {
                try report.add(.invalid_obligation_query_reference, obligation_index);
            } else {
                const query = program.queries[query_id.index()];
                const matches_requirement = if (obligation.requirement) |requirement|
                    requirement.kind == query.kind and requirement.predicate == query.goal
                else
                    false;
                if (!matches_requirement) {
                    try report.add(.obligation_query_requirement_mismatch, obligation_index);
                } else if (valid_subject and valid_requirement and obligation.subject != .control_branch and
                    !try obligationQueryCoversSubject(report.allocator, program, obligation, query, scope))
                {
                    try report.add(.obligation_query_subject_mismatch, obligation_index);
                }
            }
        }
        if (obligation.certificate) |certificate_id| {
            if (!validId(certificate_id, program.certificates.len)) {
                try report.add(.invalid_obligation_certificate_reference, obligation_index);
            } else {
                const certificate = program.certificates[certificate_id.index()];
                if (obligation.query == null or obligation.query.? != certificate.query) {
                    try report.add(.invalid_obligation_certificate_reference, obligation_index);
                }
                const agrees = switch (obligation.status) {
                    .open => certificate.resolution != .proved,
                    .discharged => certificate.resolution == .proved,
                };
                if (!agrees) try report.add(.obligation_certificate_resolution_mismatch, obligation_index);
                if (certificate.resolution != .unknown and !evidenceCovers(certificate.evidence, obligation.evidence)) {
                    try report.add(.obligation_certificate_evidence_mismatch, obligation_index);
                }
            }
        }
        if (obligation.status == .discharged and obligation.certificate == null) {
            try report.add(.discharged_obligation_without_proof, obligation_index);
        }
        if (obligation.status == .open and
            profileIncludes(profile, obligation.blocks_profile) and
            (profile != .readable_luau or
                obligation.blocks_profile == .core or
                scope == null or
                scope.?.obligationSubject(obligation.subject)))
        {
            try report.add(.open_profile_obligation, obligation_index);
        }
    }
}

fn obligationQueryCoversSubject(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    obligation: ir.Obligation,
    query: ir.SolverQuery,
    scope: ?*const readable_scope.Scope,
) !bool {
    var closure = proof_closure.Closure.initForObligationSubject(allocator, program, query) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.InvalidClosureInput => return false,
    };
    defer closure.deinit();

    if (closure.coversObligationSubject(program, obligation.subject)) return true;
    const block_id = switch (obligation.subject) {
        .block => |value| value,
        else => return false,
    };
    if (!try currentBlockIsUnreachable(allocator, program, scope, block_id)) return false;

    for (program.obligations) |candidate| {
        const retired = try authenticatedRetiredControlEdgeAlloc(allocator, program, candidate) orelse continue;
        if (closure.coversBlockThroughIncomingEdge(program, block_id, retired)) return true;
    }
    return false;
}

fn currentBlockIsUnreachable(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: ?*const readable_scope.Scope,
    block_id: ir.BlockId,
) !bool {
    if (scope) |current| return !current.block(block_id);
    if (block_id.index() >= program.blocks.len) return false;
    const block = program.blocks[block_id.index()];
    if (block.id != block_id or block.function.index() >= program.functions.len) return false;
    const function = program.functions[block.function.index()];
    if (function.id != block.function) return false;
    var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
        error.InvalidCfg => return false,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    return !analysis.isReachable(block_id);
}

fn authenticatedRetiredControlEdgeAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    obligation: ir.Obligation,
) !?ir.Edge {
    if (obligation.status != .discharged) return null;
    const subject = switch (obligation.subject) {
        .control_branch => |value| value,
        else => return null,
    };

    var witness_report = diagnostics.Report.init(allocator);
    defer witness_report.deinit();
    try validateControlBranchObligation(&witness_report, program, obligation, subject, obligation.id.index());
    if (!witness_report.isClean()) return null;

    const replay = control_flow.replayControlBranchObligation(program, obligation) orelse return null;
    const retired_kind: ir.CfgEdgeKind = if (replay.truth) .branch_else else .branch_then;
    const original = if (replay.truth) subject.branch.else_edge else subject.branch.then_edge;
    return replayEdgeHistory(program, subject.block, retired_kind, original);
}

test "obligation closure lookup rejects malformed ownership references" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var instructions = fixture.instructions;
    var values = fixture.values;
    var program = fixture.program;
    program.instructions = &instructions;
    program.values = &values;

    var function_marks = [_]bool{false} ** fixture.functions.len;
    var term_marks: [0]bool = .{};
    var value_marks = [_]bool{false} ** fixture.values.len;
    var pack_marks: [0]bool = .{};
    var place_marks: [0]bool = .{};
    var capture_marks: [0]bool = .{};
    var instruction_marks = [_]bool{false} ** fixture.instructions.len;
    var block_marks = [_]bool{false} ** fixture.blocks.len;
    var evidence_marks = [_]bool{false} ** fixture.evidence.len;
    var rewrite_marks: [0]bool = .{};
    var closure: proof_closure.Closure = .{
        .allocator = std.testing.allocator,
        .lexical_witness = false,
        .runtime_value_witness = false,
        .combined_runtime_witness = false,
        .functions = &function_marks,
        .terms = &term_marks,
        .values = &value_marks,
        .value_packs = &pack_marks,
        .places = &place_marks,
        .captures = &capture_marks,
        .instructions = &instruction_marks,
        .blocks = &block_marks,
        .evidence = &evidence_marks,
        .edge_rewrites = &rewrite_marks,
    };

    instruction_marks[fixture.i_sum.index()] = true;
    instructions[fixture.i_sum.index()].block = ir.BlockId.fromIndex(99);
    try std.testing.expect(!closure.coversObligationSubject(&program, .{ .function = fixture.f_add }));

    instruction_marks[fixture.i_sum.index()] = false;
    value_marks[fixture.v_sum.index()] = true;
    values[fixture.v_sum.index()].origin = .{ .instruction_result = .{
        .instruction = ir.InstructionId.fromIndex(99),
        .index = 0,
    } };
    try std.testing.expect(!closure.coversObligationSubject(&program, .{ .block = fixture.b_add }));
}

pub fn hasEffectAuthority(program: *const ir.Program, instruction: ir.Instruction) bool {
    return hasInstructionPurposeAuthority(program, instruction, .effect_summary);
}

pub fn hasPrimitiveOperatorAuthority(program: *const ir.Program, instruction: ir.Instruction) bool {
    return hasInstructionPurposeAuthority(program, instruction, .primitive_operator_domain);
}

pub fn hasNoMetamethodAuthority(program: *const ir.Program, instruction: ir.Instruction) bool {
    return hasInstructionPurposeAuthority(program, instruction, .no_metamethod_dispatch);
}

pub fn hasPendingEffectAuthority(program: *const ir.Program, instruction: ir.Instruction) bool {
    return hasPendingInstructionPurposeAuthority(program, instruction, .effect_summary);
}

pub fn hasPendingPrimitiveOperatorAuthority(program: *const ir.Program, instruction: ir.Instruction) bool {
    return hasPendingInstructionPurposeAuthority(program, instruction, .primitive_operator_domain);
}

pub fn hasPendingNoMetamethodAuthority(program: *const ir.Program, instruction: ir.Instruction) bool {
    return hasPendingInstructionPurposeAuthority(program, instruction, .no_metamethod_dispatch);
}

pub fn hasPendingCoreObligation(program: *const ir.Program, obligation_index: usize) bool {
    if (obligation_index >= program.obligations.len) return false;
    const obligation = program.obligations[obligation_index];
    if (obligation.id.index() != obligation_index or obligation.blocks_profile != .core) return false;
    const query_id = obligation.query orelse return false;
    if (!validId(query_id, program.queries.len)) return false;
    return proof_plan.obligationIsEligible(obligation, program.queries[query_id.index()]);
}

const InstructionPurpose = enum {
    effect_summary,
    no_metamethod_dispatch,
    primitive_operator_domain,
};

fn hasInstructionPurposeAuthority(program: *const ir.Program, instruction: ir.Instruction, expected_purpose: InstructionPurpose) bool {
    for (instruction.claims) |claim_id| {
        if (claimHasInstructionPurposeAuthority(program, instruction, claim_id, expected_purpose)) return true;
    }
    return false;
}

fn hasPendingInstructionPurposeAuthority(
    program: *const ir.Program,
    instruction: ir.Instruction,
    expected_purpose: InstructionPurpose,
) bool {
    for (instruction.claims) |claim_id| {
        if (claimHasPendingInstructionPurposeAuthority(program, instruction, claim_id, expected_purpose)) return true;
    }
    return false;
}

fn claimHasPendingInstructionPurposeAuthority(
    program: *const ir.Program,
    instruction: ir.Instruction,
    claim_id: ir.ClaimId,
    expected_purpose: InstructionPurpose,
) bool {
    if (!validId(claim_id, program.claims.len)) return false;
    const claim = program.claims[claim_id.index()];
    if (claim.id != claim_id) return false;
    const subject_matches = switch (claim.subject) {
        .instruction => |instruction_id| instruction_id == instruction.id,
        else => false,
    };
    if (!subject_matches) return false;
    const claimed_effects = switch (expected_purpose) {
        .effect_summary => switch (claim.purpose) {
            .effect_summary => |effects| effects,
            else => return false,
        },
        .no_metamethod_dispatch => switch (claim.purpose) {
            .no_metamethod_dispatch => |effects| effects,
            else => return false,
        },
        .primitive_operator_domain => switch (claim.purpose) {
            .primitive_operator_domain => |effects| effects,
            else => return false,
        },
    };
    if (!sameEffects(claimed_effects, instruction.effects) or !claimPredicateMatchesPurpose(program, claim)) return false;
    const query_id = claim.query orelse return false;
    if (!validId(query_id, program.queries.len)) return false;
    return proof_plan.claimIsEligible(claim, program.queries[query_id.index()]);
}

fn claimHasInstructionPurposeAuthority(
    program: *const ir.Program,
    instruction: ir.Instruction,
    claim_id: ir.ClaimId,
    expected_purpose: InstructionPurpose,
) bool {
    if (!validId(claim_id, program.claims.len)) return false;
    const claim = program.claims[claim_id.index()];
    const subject_matches = switch (claim.subject) {
        .instruction => |instruction_id| instruction_id == instruction.id,
        else => false,
    };
    if (!subject_matches or claim.status != .proved) return false;
    const claimed_effects = switch (expected_purpose) {
        .effect_summary => switch (claim.purpose) {
            .effect_summary => |effects| effects,
            else => return false,
        },
        .no_metamethod_dispatch => switch (claim.purpose) {
            .no_metamethod_dispatch => |effects| effects,
            else => return false,
        },
        .primitive_operator_domain => switch (claim.purpose) {
            .primitive_operator_domain => |effects| effects,
            else => return false,
        },
    };
    if (!sameEffects(claimed_effects, instruction.effects)) return false;
    if (!claimPredicateMatchesPurpose(program, claim)) return false;

    const certificate_id = claim.certificate orelse return false;
    if (!validId(certificate_id, program.certificates.len)) return false;
    const certificate = program.certificates[certificate_id.index()];
    if (certificate.resolution != .proved or !validId(certificate.query, program.queries.len)) return false;
    const query = program.queries[certificate.query.index()];
    if (query.goal != claim.predicate) return false;
    return switch (certificate.engine) {
        .internal_facts => solver.solve(program, query) == .proved,
        .z3, .imported => certificate.evidence.len != 0 and certificate.certificate_digest != null and certificate.certificate_digest.?.len != 0,
    };
}

fn instructionListsClaim(instruction: ir.Instruction, claim_id: ir.ClaimId) bool {
    for (instruction.claims) |listed_id| {
        if (listed_id == claim_id) return true;
    }
    return false;
}

fn claimPredicateMatchesPurpose(program: *const ir.Program, claim: ir.Claim) bool {
    if (!validId(claim.predicate, program.solver_terms.len)) return false;
    const atom = switch (program.solver_terms[claim.predicate.index()].operation) {
        .semantic_atom => |value| value,
        else => return false,
    };
    const instruction_id = switch (claim.subject) {
        .instruction => |value| value,
        else => return false,
    };
    return switch (claim.purpose) {
        .generic_predicate => true,
        .effect_summary => switch (atom) {
            .instruction_effects => |atom_instruction| atom_instruction == instruction_id,
            else => false,
        },
        .no_metamethod_dispatch => switch (atom) {
            .no_metamethod_dispatch => |atom_instruction| atom_instruction == instruction_id,
            else => false,
        },
        .primitive_operator_domain => switch (atom) {
            .primitive_operator_domain => |atom_instruction| atom_instruction == instruction_id,
            else => false,
        },
    };
}

fn validateInstructionEffectPurpose(
    report: *diagnostics.Report,
    program: *const ir.Program,
    subject: ir.EntityRef,
    claimed_effects: ir.EffectSummary,
    claim_index: usize,
) !void {
    switch (subject) {
        .instruction => |instruction_id| {
            if (!validId(instruction_id, program.instructions.len)) {
                try report.add(.claim_purpose_subject_mismatch, claim_index);
            } else if (!sameEffects(claimed_effects, program.instructions[instruction_id.index()].effects)) {
                try report.add(.claim_effect_summary_mismatch, claim_index);
            }
        },
        else => try report.add(.claim_purpose_subject_mismatch, claim_index),
    }
}

fn sameEffects(left: ir.EffectSummary, right: ir.EffectSummary) bool {
    return left.precision == right.precision and
        left.reads_memory == right.reads_memory and
        left.writes_memory == right.writes_memory and
        left.may_throw == right.may_throw and
        left.may_yield == right.may_yield and
        left.invokes_unknown_code == right.invokes_unknown_code;
}

fn evidenceCovers(available: []const ir.EvidenceId, required: []const ir.EvidenceId) bool {
    for (required) |required_id| {
        for (available) |available_id| {
            if (available_id == required_id) break;
        } else return false;
    }
    return true;
}

fn validateControlBranchObligation(
    report: *diagnostics.Report,
    program: *const ir.Program,
    obligation: ir.Obligation,
    subject: ir.ControlBranchSubject,
    obligation_index: usize,
) !void {
    if (!try validHistoricalBranch(report.allocator, program, subject)) {
        try report.add(.invalid_control_branch_witness, obligation_index);
        return;
    }

    const source = program.blocks[subject.block.index()];
    const expected_evidence = try control_query_plan.branchTruthinessEvidenceAlloc(
        report.allocator,
        program,
        source,
        subject.branch.condition,
    );
    defer report.allocator.free(expected_evidence);
    if (!std.mem.eql(ir.EvidenceId, expected_evidence, obligation.evidence)) {
        try report.add(.invalid_control_branch_witness, obligation_index);
    }

    const replay = if (obligation.status == .discharged)
        control_flow.replayControlBranchObligation(program, obligation)
    else
        null;
    if (obligation.status == .discharged and replay == null) {
        try report.add(.invalid_control_branch_witness, obligation_index);
        return;
    }

    switch (source.terminator) {
        .branch => |live| {
            const expected_then = replayEdgeHistory(program, subject.block, .branch_then, subject.branch.then_edge) orelse {
                try report.add(.invalid_control_branch_witness, obligation_index);
                return;
            };
            const expected_else = replayEdgeHistory(program, subject.block, .branch_else, subject.branch.else_edge) orelse {
                try report.add(.invalid_control_branch_witness, obligation_index);
                return;
            };
            if (live.condition != subject.branch.condition or
                !edge_path.sameEdge(live.then_edge, expected_then) or
                !edge_path.sameEdge(live.else_edge, expected_else))
            {
                try report.add(.invalid_control_branch_witness, obligation_index);
            }
        },
        .jump => |live| {
            const decision = replay orelse {
                try report.add(.invalid_control_branch_witness, obligation_index);
                return;
            };
            const selected_kind: ir.CfgEdgeKind = if (decision.truth) .branch_then else .branch_else;
            const selected = replayEdgeHistory(program, subject.block, selected_kind, decision.selected) orelse {
                try report.add(.invalid_control_branch_witness, obligation_index);
                return;
            };
            const effective = replayEdgeHistory(program, subject.block, .jump, selected) orelse {
                try report.add(.invalid_control_branch_witness, obligation_index);
                return;
            };
            if (!edge_path.sameEdge(live, effective)) try report.add(.invalid_control_branch_witness, obligation_index);
        },
        else => try report.add(.invalid_control_branch_witness, obligation_index),
    }
}

fn validHistoricalBranch(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    subject: ir.ControlBranchSubject,
) !bool {
    if (subject.block.index() >= program.blocks.len or subject.branch.condition.index() >= program.values.len) return false;
    const source = program.blocks[subject.block.index()];
    if (source.id != subject.block or source.function.index() >= program.functions.len) return false;
    const condition = program.values[subject.branch.condition.index()];
    if (condition.id != subject.branch.condition or condition.function != source.function) return false;
    if (condition.type.kind != .boolean and condition.type.kind != .dynamic and condition.type.knownLuauTruthiness() == null) return false;
    if (!validHistoricalEdge(program, source, subject.branch.then_edge) or
        !validHistoricalEdge(program, source, subject.branch.else_edge)) return false;

    const blocks = try allocator.dupe(ir.Block, program.blocks);
    defer allocator.free(blocks);
    blocks[subject.block.index()].terminator = .{ .branch = subject.branch };
    var historical = program.*;
    historical.blocks = blocks;
    var analysis = cfg.Analysis.init(allocator, &historical, historical.functions[source.function.index()]) catch |err| switch (err) {
        error.InvalidCfg => return false,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    if (!analysis.isReachable(subject.block)) return true;
    if (!valueAvailableAtTerminator(&historical, &analysis, source, subject.branch.condition)) return false;
    for (subject.branch.then_edge.arguments) |argument| {
        if (!valueAvailableAtTerminator(&historical, &analysis, source, argument)) return false;
    }
    for (subject.branch.else_edge.arguments) |argument| {
        if (!valueAvailableAtTerminator(&historical, &analysis, source, argument)) return false;
    }
    return true;
}

fn validHistoricalEdge(program: *const ir.Program, source: ir.Block, edge: ir.Edge) bool {
    if (edge.target.index() >= program.blocks.len) return false;
    const target = program.blocks[edge.target.index()];
    if (target.id != edge.target or target.function != source.function or target.parameters.len != edge.arguments.len) return false;
    for (edge.arguments, 0..) |argument, index| {
        if (argument.index() >= program.values.len or target.parameters[index].index() >= program.values.len) return false;
        const value = program.values[argument.index()];
        const parameter = program.values[target.parameters[index].index()];
        if (value.id != argument or value.function != source.function or
            !type_validation.isAssignable(parameter.type, value.type)) return false;
    }
    return true;
}

fn valueAvailableAtTerminator(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.Block,
    value_id: ir.ValueId,
) bool {
    if (value_id.index() >= program.values.len) return false;
    const value = program.values[value_id.index()];
    if (value.id != value_id or value.function != source.function) return false;
    return switch (value.origin) {
        .parameter, .capture => true,
        .block_parameter => |origin| origin.block.index() < program.blocks.len and
            (origin.block == source.id or analysis.dominates(origin.block, source.id)),
        .instruction_result => |origin| blk: {
            if (origin.instruction.index() >= program.instructions.len) break :blk false;
            const definition = program.instructions[origin.instruction.index()];
            if (definition.id != origin.instruction or definition.block.index() >= program.blocks.len) break :blk false;
            if (definition.block != source.id) break :blk analysis.dominates(definition.block, source.id);
            for (source.instructions) |instruction_id| if (instruction_id == origin.instruction) break :blk true;
            break :blk false;
        },
    };
}

fn replayEdgeHistory(
    program: *const ir.Program,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    original: ir.Edge,
) ?ir.Edge {
    var current = original;
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.source != source or rewrite.kind != kind) continue;
        if (!edge_path.sameEdge(rewrite.from, current)) return null;
        current = rewrite.to;
    }
    return current;
}

fn isUnwitnessedConsumedLiteralBranch(program: *const ir.Program, obligation: ir.Obligation, block_id: ir.BlockId) bool {
    if (obligation.kind != .control_structure or obligation.status != .discharged or
        obligation.query == null or block_id.index() >= program.blocks.len or
        obligation.query.?.index() >= program.queries.len or program.blocks[block_id.index()].terminator != .jump)
    {
        return false;
    }
    const query = program.queries[obligation.query.?.index()];
    if (query.goal.index() >= program.solver_terms.len) return false;
    return program.solver_terms[query.goal.index()].operation == .boolean_literal;
}

fn validObligationSubject(program: *const ir.Program, subject: ir.ObligationSubject) bool {
    return switch (subject) {
        .program => true,
        .function => |id| validId(id, program.functions.len),
        .block => |id| validId(id, program.blocks.len),
        .instruction => |id| validId(id, program.instructions.len),
        .value => |id| validId(id, program.values.len),
        .value_pack => |id| validId(id, program.value_packs.len),
        .place => |id| validId(id, program.places.len),
        .capture => |id| validId(id, program.captures.len),
        .external_binding => |id| validId(id, program.external_bindings.len),
        .control_branch => |control| validId(control.block, program.blocks.len) and
            validId(control.branch.condition, program.values.len) and
            validId(control.branch.then_edge.target, program.blocks.len) and
            validId(control.branch.else_edge.target, program.blocks.len),
    };
}

fn profileIncludes(selected: ir.AdmissionProfile, blocked: ir.AdmissionProfile) bool {
    return switch (selected) {
        .core => blocked == .core,
        .readable_luau => true,
    };
}

fn validEntity(program: *const ir.Program, entity: ir.EntityRef) bool {
    return switch (entity) {
        .program => true,
        .function => |id| validId(id, program.functions.len),
        .block => |id| validId(id, program.blocks.len),
        .instruction => |id| validId(id, program.instructions.len),
        .value => |id| validId(id, program.values.len),
        .value_pack => |id| validId(id, program.value_packs.len),
        .place => |id| validId(id, program.places.len),
        .capture => |id| validId(id, program.captures.len),
        .external_binding => |id| validId(id, program.external_bindings.len),
    };
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}
