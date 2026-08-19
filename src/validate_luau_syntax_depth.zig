const std = @import("std");
const branch_expression = @import("emit_luau_branch_expr.zig");
const branch_statement = @import("emit_luau_branch_stmt.zig");
const cfg = @import("cfg.zig");
const diagnostics = @import("diagnostics.zig");
const emission_planning = @import("emit_luau_plan.zig");
const emission_scope = @import("emit_luau_scope.zig");
const lexical = @import("emit_luau_lexical.zig");
const ir = @import("ir.zig");
const iteration_protocol = @import("iteration_protocol.zig");
const luau_runtime = @import("luau_runtime.zig");
const readable_scope = @import("readable_scope.zig");
const structure = @import("structure.zig");
const structured_escape = @import("structured_escape.zig");

const Site = struct {
    target: ir.FunctionId,
    ambient_depth: usize,
};

const StableCaptureValues = struct {
    scopes: *const emission_scope.Plan,

    pub fn contains(self: StableCaptureValues, value_id: ir.ValueId) bool {
        return self.scopes.valueHasStableLexicalBinding(value_id);
    }
};

const Summary = struct {
    local_depth: usize = 0,
    site_start: usize = 0,
    site_end: usize = 0,
    recorded: bool = false,
};

/// Prove a narrow control shape is too deep before the recursive structurer
/// sees it. The check only follows direct branch-to-branch spines with a
/// terminal sibling, so sequential branches and loops are not mistaken for
/// nested syntax. It is deliberately iterative and therefore safe to use as
/// the guard for the recursive planning path.
pub fn maxDirectSpineDepth(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
) std.mem.Allocator.Error!usize {
    const block_count = analysis.function.blocks.len;
    if (block_count == 0) return 0;

    const state = try allocator.alloc(u8, block_count);
    defer allocator.free(state);
    @memset(state, 0);
    const depths = try allocator.alloc(usize, block_count);
    defer allocator.free(depths);
    @memset(depths, 0);
    const path = try allocator.alloc(usize, block_count);
    defer allocator.free(path);
    var maximum_depth: usize = 0;

    for (0..block_count) |start| {
        if (state[start] == 2 or !analysis.isReachable(analysis.function.blocks[start])) continue;
        const start_block = program.blocks[analysis.function.blocks[start].index()];
        if (std.meta.activeTag(start_block.terminator) != .branch) continue;

        var path_len: usize = 0;
        var current = start;
        var terminal_depth: usize = 0;
        var resolved = false;
        while (path_len < block_count) {
            if (state[current] == 2) {
                terminal_depth = depths[current];
                resolved = true;
                break;
            }
            if (state[current] == 1) {
                // A cycle is a loop candidate, not a finite nested syntax
                // chain. Leave it conservative and let control structuring
                // classify it through the normal loop machinery.
                for (path[0..path_len]) |index| {
                    state[index] = 2;
                    depths[index] = 0;
                }
                resolved = true;
                terminal_depth = 0;
                break;
            }
            state[current] = 1;
            path[path_len] = current;
            path_len += 1;

            const block_id = analysis.function.blocks[current];
            const block = program.blocks[block_id.index()];
            const next = switch (block.terminator) {
                .branch => |branch| directSpineSuccessor(analysis, program, branch),
                else => null,
            };
            if (next) |next_index| {
                current = next_index;
                continue;
            }
            terminal_depth = 0;
            resolved = true;
            break;
        }
        if (!resolved) {
            for (path[0..path_len]) |index| {
                state[index] = 2;
                depths[index] = 0;
            }
            continue;
        }

        while (path_len != 0) {
            path_len -= 1;
            terminal_depth = saturatingAdd(terminal_depth, 1);
            const index = path[path_len];
            state[index] = 2;
            depths[index] = terminal_depth;
            maximum_depth = @max(maximum_depth, terminal_depth);
        }
    }
    return maximum_depth;
}

pub fn exceedsPlanningDepth(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
) std.mem.Allocator.Error!bool {
    return (try maxDirectSpineDepth(allocator, program, analysis)) > luau_runtime.max_emitted_syntax_nesting;
}

fn directSpineSuccessor(
    analysis: *const cfg.Analysis,
    program: *const ir.Program,
    branch: ir.Branch,
) ?usize {
    const candidates = [_]struct { next: ir.BlockId, sibling: ir.BlockId }{
        .{ .next = branch.then_edge.target, .sibling = branch.else_edge.target },
        .{ .next = branch.else_edge.target, .sibling = branch.then_edge.target },
    };
    for (candidates) |candidate| {
        const next_index = analysis.blockIndex(candidate.next) orelse continue;
        _ = analysis.blockIndex(candidate.sibling) orelse continue;
        const next_block = program.blocks[candidate.next.index()];
        const sibling_block = program.blocks[candidate.sibling.index()];
        if (isTerminal(sibling_block.terminator) and sibling_block.id != next_block.id and
            std.meta.activeTag(next_block.terminator) == .branch)
        {
            return next_index;
        }
    }
    return null;
}

fn isTerminal(terminator: ir.Terminator) bool {
    return switch (terminator) {
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => true,
        else => false,
    };
}

/// Tracks source blocks that remain after control and expression recovery.
/// Closure bodies are expanded at their actual emitted sites, so lexical
/// function nesting and structured control consume one shared parser budget.
pub const Plan = struct {
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    summaries: []Summary,
    sites: std.ArrayList(Site) = .empty,
    memoized_depths: []?usize,
    visiting: []bool,

    pub fn init(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        readable: *const readable_scope.Scope,
        emission: *const emission_planning.Plan,
    ) !Plan {
        const summaries = try allocator.alloc(Summary, program.functions.len);
        errdefer allocator.free(summaries);
        @memset(summaries, .{});
        const memoized_depths = try allocator.alloc(?usize, program.functions.len);
        errdefer allocator.free(memoized_depths);
        @memset(memoized_depths, null);
        const visiting = try allocator.alloc(bool, program.functions.len);
        errdefer allocator.free(visiting);
        @memset(visiting, false);
        return .{
            .allocator = allocator,
            .program = program,
            .readable = readable,
            .emission = emission,
            .summaries = summaries,
            .memoized_depths = memoized_depths,
            .visiting = visiting,
        };
    }

    pub fn deinit(self: *Plan) void {
        self.allocator.free(self.visiting);
        self.allocator.free(self.memoized_depths);
        self.sites.deinit(self.allocator);
        self.allocator.free(self.summaries);
        self.* = undefined;
    }

    pub fn recordFunction(
        self: *Plan,
        function: ir.Function,
        structured: *const structure.Plan,
        scopes: *const emission_scope.Plan,
    ) !void {
        if (function.id.index() >= self.summaries.len) return;
        const start = self.sites.items.len;
        var recorder: Recorder = .{
            .plan = self,
            .scopes = scopes,
        };
        try recorder.region(structured.root, 0);
        self.summaries[function.id.index()] = .{
            .local_depth = recorder.maximum,
            .site_start = start,
            .site_end = self.sites.items.len,
            .recorded = true,
        };
    }

    pub fn recordDirectSpineFunction(self: *Plan, function: ir.Function, depth: usize) void {
        if (function.id.index() >= self.summaries.len) return;
        self.summaries[function.id.index()] = .{
            .local_depth = depth,
            .site_start = self.sites.items.len,
            .site_end = self.sites.items.len,
            .recorded = true,
        };
    }

    pub fn addDiagnostics(self: *Plan, report: *diagnostics.Report, emitted_functions: []const bool) !void {
        for (self.program.functions) |function| {
            if (function.id.index() >= emitted_functions.len or !emitted_functions[function.id.index()]) continue;
            if (function.id != self.program.entry_function and function.lexical_parent != null) continue;
            if (self.expandedDepth(function.id) > luau_runtime.max_emitted_syntax_nesting) {
                try report.add(.unsupported_readable_syntax_depth, function.id.index());
            }
        }
    }

    fn expandedDepth(self: *Plan, function_id: ir.FunctionId) usize {
        if (function_id.index() >= self.summaries.len) return std.math.maxInt(usize);
        if (self.memoized_depths[function_id.index()]) |depth| return depth;

        const Frame = struct {
            function_index: usize,
            next_site: usize,
            maximum: usize,
            ambient_depth: usize,
        };
        const frames = self.allocator.alloc(Frame, self.summaries.len) catch
            return std.math.maxInt(usize);
        defer self.allocator.free(frames);

        var frame_count: usize = 1;
        const root_summary = self.summaries[function_id.index()];
        if (!root_summary.recorded or root_summary.site_start > root_summary.site_end or
            root_summary.site_end > self.sites.items.len)
        {
            return std.math.maxInt(usize);
        }
        self.visiting[function_id.index()] = true;
        frames[0] = .{
            .function_index = function_id.index(),
            .next_site = root_summary.site_start,
            .maximum = root_summary.local_depth,
            .ambient_depth = 0,
        };

        while (frame_count != 0) {
            const frame = &frames[frame_count - 1];
            const summary = self.summaries[frame.function_index];
            if (frame.next_site < summary.site_end) {
                const site = self.sites.items[frame.next_site];
                frame.next_site += 1;
                if (site.target.index() >= self.summaries.len) {
                    frame.maximum = std.math.maxInt(usize);
                    continue;
                }
                if (self.memoized_depths[site.target.index()]) |nested_depth| {
                    frame.maximum = @max(
                        frame.maximum,
                        saturatingAdd(site.ambient_depth, saturatingAdd(1, nested_depth)),
                    );
                    continue;
                }
                if (self.visiting[site.target.index()] or frame_count >= frames.len) {
                    frame.maximum = std.math.maxInt(usize);
                    continue;
                }
                const target_summary = self.summaries[site.target.index()];
                if (!target_summary.recorded or target_summary.site_start > target_summary.site_end or
                    target_summary.site_end > self.sites.items.len)
                {
                    frame.maximum = std.math.maxInt(usize);
                    continue;
                }
                self.visiting[site.target.index()] = true;
                frames[frame_count] = .{
                    .function_index = site.target.index(),
                    .next_site = target_summary.site_start,
                    .maximum = target_summary.local_depth,
                    .ambient_depth = site.ambient_depth,
                };
                frame_count += 1;
                continue;
            }

            const completed = frame.*;
            self.memoized_depths[completed.function_index] = completed.maximum;
            self.visiting[completed.function_index] = false;
            frame_count -= 1;
            if (frame_count == 0) return completed.maximum;
            const parent = &frames[frame_count - 1];
            const nested = saturatingAdd(
                completed.ambient_depth,
                saturatingAdd(1, completed.maximum),
            );
            parent.maximum = @max(parent.maximum, nested);
        }
        return std.math.maxInt(usize);
    }
};

const Recorder = struct {
    plan: *Plan,
    scopes: *const emission_scope.Plan,
    maximum: usize = 0,

    fn region(self: *Recorder, value: *const structure.Region, parent_depth: usize) std.mem.Allocator.Error!void {
        var group_count: usize = 0;
        var previous_group: emission_scope.ScopeId = emission_scope.invalid_scope;
        for (value.nodes) |*structured_node| {
            const group = self.scopes.nodeContainerScope(structured_node) orelse continue;
            if (group != previous_group) {
                previous_group = group;
                group_count += 1;
            }
        }
        const escape_depth = saturatingAdd(parent_depth, @intFromBool(structured_escape.regionOwnsEscape(value)));
        const depth = saturatingAdd(escape_depth, @intFromBool(group_count > 1));
        self.note(depth);
        for (value.nodes) |structured_node| try self.visitNode(structured_node, depth);
    }

    fn visitNode(self: *Recorder, value: structure.Node, depth: usize) std.mem.Allocator.Error!void {
        switch (value) {
            .block => |block_id| try self.visitBlock(block_id, depth),
            .branch => |structured_branch| try self.visitBranch(structured_branch, depth),
            .loop => |structured_loop| try self.visitLoop(structured_loop, depth),
            .latch_loop => |loop| {
                const body_depth = saturatingAdd(depth, 1);
                self.note(body_depth);
                try self.region(loop.body_region, body_depth);
            },
            .infinite_loop => |loop| {
                const body_depth = saturatingAdd(depth, 1);
                self.note(body_depth);
                try self.region(loop.body_region, body_depth);
                if (loop.shared_side_exit) |side_exit| {
                    for (side_exit.entries) |entry| {
                        self.note(body_depth);
                        try self.region(entry.region, body_depth);
                    }
                }
            },
            .loop_control => |control| {
                try self.visitBlock(control.block, depth);
                self.note(saturatingAdd(depth, 1));
            },
            .loop_boundary => |control| try self.loopBoundary(control, depth),
            .loop_terminal => |control| {
                try self.visitBlock(control.block, depth);
                const arm_depth = saturatingAdd(depth, 1);
                self.note(arm_depth);
                try self.visitBlock(control.terminal_block, arm_depth);
            },
        }
    }

    fn visitBranch(self: *Recorder, structured: structure.Branch, depth: usize) std.mem.Allocator.Error!void {
        try self.visitBlock(structured.block, depth);
        if (structured.block.index() >= self.plan.program.blocks.len) return;
        const source_block = self.plan.program.blocks[structured.block.index()];
        const branch = switch (source_block.terminator) {
            .branch => |value| value,
            else => return,
        };
        if (self.plan.emission.branchEdgesAreIdentical(source_block)) {
            try self.region(structured.then_region, depth);
            return;
        }
        if (branch_expression.match(self.plan.program, self.plan.emission, self.scopes, branch, structured) != null) return;

        if (structured.join == null and
            regionAlwaysFunctionTerminates(self.plan.program, structured.then_region) and
            regionAlwaysFunctionTerminates(self.plan.program, structured.else_region))
        {
            const arm_depth = saturatingAdd(depth, 1);
            self.note(arm_depth);
            try self.region(structured.then_region, arm_depth);
            try self.region(structured.else_region, depth);
            return;
        }

        const then_empty = branch_statement.armIsStructurallyEmpty(
            self.plan.program,
            branch.then_edge,
            structured.then_region,
            structured.join,
        );
        const else_empty = branch_statement.armIsStructurallyEmpty(
            self.plan.program,
            branch.else_edge,
            structured.else_region,
            structured.join,
        );
        if (then_empty and else_empty) return;
        const arm_depth = saturatingAdd(depth, 1);
        self.note(arm_depth);
        if (then_empty) {
            try self.region(structured.else_region, arm_depth);
            return;
        }
        try self.region(structured.then_region, arm_depth);
        if (else_empty) return;
        if (branch_statement.matchElseIf(
            self.plan.program,
            self.plan.emission,
            self.scopes,
            branch.else_edge,
            structured.else_region,
            structured.join,
        )) |else_if| {
            try self.elseIf(else_if, structured.join.?, depth);
        } else {
            try self.region(structured.else_region, arm_depth);
        }
    }

    fn elseIf(self: *Recorder, structured: structure.Branch, chain_join: ir.BlockId, depth: usize) std.mem.Allocator.Error!void {
        try self.visitBlock(structured.block, depth);
        if (structured.block.index() >= self.plan.program.blocks.len) return;
        const source_branch = switch (self.plan.program.blocks[structured.block.index()].terminator) {
            .branch => |value| value,
            else => return,
        };
        const arm_depth = saturatingAdd(depth, 1);
        self.note(arm_depth);
        try self.region(structured.then_region, arm_depth);
        if (branch_statement.armIsStructurallyEmpty(
            self.plan.program,
            source_branch.else_edge,
            structured.else_region,
            structured.join,
        )) return;
        if (branch_statement.matchElseIf(
            self.plan.program,
            self.plan.emission,
            self.scopes,
            source_branch.else_edge,
            structured.else_region,
            chain_join,
        )) |next| {
            try self.elseIf(next, chain_join, depth);
        } else {
            try self.region(structured.else_region, arm_depth);
        }
    }

    fn visitLoop(self: *Recorder, value: structure.Loop, depth: usize) std.mem.Allocator.Error!void {
        try self.visitBlock(value.header, depth);
        const is_native = self.scopes.nativeIterationConsumesParameters(value.header) and
            (try iteration_protocol.matchLoop(self.plan.allocator, self.plan.program, value)) != null;
        const body_depth = saturatingAdd(depth, if (is_native) 1 else 2);
        self.note(body_depth);
        try self.region(value.body_region, body_depth);
    }

    fn loopBoundary(self: *Recorder, control: structure.LoopBoundaryControl, depth: usize) std.mem.Allocator.Error!void {
        try self.visitBlock(control.block, depth);
        const arm_depth = saturatingAdd(depth, 1);
        self.note(arm_depth);
        try self.region(control.body_region, arm_depth);
        switch (control.boundary) {
            .exit, .escape, .shared_exit => {},
            .terminal => |terminal| try self.visitBlock(terminal.block, arm_depth),
            .side_exit => |side_exit| try self.region(side_exit.region, arm_depth),
            .side_escape => |side_escape| try self.region(side_escape.region, arm_depth),
        }
    }

    fn visitBlock(self: *Recorder, block_id: ir.BlockId, depth: usize) std.mem.Allocator.Error!void {
        self.note(depth);
        if (block_id.index() >= self.plan.program.blocks.len or !self.plan.readable.block(block_id)) return;
        const source_block = self.plan.program.blocks[block_id.index()];
        const block_scope = self.scopes.blockScope(block_id) orelse emission_scope.invalid_scope;
        for (source_block.instructions) |instruction_id| {
            if (!self.plan.readable.instruction(instruction_id) or instruction_id.index() >= self.plan.program.instructions.len) continue;
            if (self.plan.emission.dead.contains(instruction_id)) continue;
            const instruction = self.plan.program.instructions[instruction_id.index()];
            if (instruction.operation == .numeric_for_next and
                instruction.operation.numeric_for_next.mode == .semantic_normalized and
                !self.scopes.instructionSuppressedByControl(instruction.id))
            {
                self.note(saturatingAdd(depth, 1));
            }
            if (instruction.operation == .table_set_pack or
                self.plan.emission.packs.role(instruction.id) == .stored_invocation_producer)
            {
                self.note(saturatingAdd(depth, 3));
            }
            const closure = switch (instruction.operation) {
                .make_closure => |value| value,
                else => continue,
            };
            if (closure.function.index() >= self.plan.program.functions.len) continue;
            var closure_plan = lexical.ClosurePlan.initWithStableValues(
                self.plan.allocator,
                self.plan.program,
                self.plan.program.functions[closure.function.index()],
                closure,
                &.{},
                StableCaptureValues{ .scopes = self.scopes },
            ) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.InvalidClosureBinding => unreachable,
            };
            defer closure_plan.deinit();
            const rendered_id = self.plan.emission.closure_stores.consumerForProducer(instruction.id) orelse
                self.plan.emission.place_writes.consumerForProducer(instruction.id) orelse instruction.id;
            const rendered_scope = self.scopes.instructionScope(rendered_id) orelse emission_scope.invalid_scope;
            const segment_depth: usize = @intFromBool(
                rendered_scope != emission_scope.invalid_scope and block_scope != emission_scope.invalid_scope and rendered_scope != block_scope,
            );
            try self.plan.sites.append(self.plan.allocator, .{
                .target = closure.function,
                .ambient_depth = saturatingAdd(
                    saturatingAdd(depth, segment_depth),
                    @intFromBool(closure_plan.value_bindings.len != 0),
                ),
            });
        }
    }

    fn note(self: *Recorder, depth: usize) void {
        self.maximum = @max(self.maximum, depth);
    }
};

fn regionAlwaysFunctionTerminates(program: *const ir.Program, region: *const structure.Region) bool {
    if (region.terminal_projection != null) return true;
    if (region.nodes.len == 0) return false;
    return nodeAlwaysFunctionTerminates(program, region.nodes[region.nodes.len - 1]);
}

fn nodeAlwaysFunctionTerminates(program: *const ir.Program, node: structure.Node) bool {
    return switch (node) {
        .block => |block_id| if (block_id.index() < program.blocks.len) switch (program.blocks[block_id.index()].terminator) {
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => true,
            else => false,
        } else false,
        .branch => |branch| branch.join == null and
            regionAlwaysFunctionTerminates(program, branch.then_region) and
            regionAlwaysFunctionTerminates(program, branch.else_region),
        else => false,
    };
}

fn saturatingAdd(left: usize, right: usize) usize {
    return std.math.add(usize, left, right) catch std.math.maxInt(usize);
}
