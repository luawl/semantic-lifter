const std = @import("std");
const Io = std.Io;
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const cfg_edge = @import("cfg_edge.zig");
const natural_loop = @import("natural_loop.zig");
const node_split = @import("node_split.zig");
const node_split_instruction = @import("node_split_instruction.zig");
const runtime_uses = @import("runtime_uses.zig");
const clone_availability = @import("clone_availability.zig");
const iteration_state = @import("iteration_state.zig");
const proof_effect_closure = @import("proof_effect_closure.zig");
const build_options = @import("build_options");

const trace_structural_phases = build_options.trace_normalize_phases;
const trace_conditional_batch = false;

pub fn traceStructural(comptime format: []const u8, args: anytype) void {
    if (trace_structural_phases) std.debug.print(format, args);
}

pub const Selection = struct {
    join: ir.BlockId,
    then_distance: u32,
    else_distance: u32,
};

const DistancePair = struct {
    then_distances: []const u32,
    else_distances: []const u32,
};

pub const Split = struct {
    allocator: std.mem.Allocator,
    function_index: usize,
    branch: ir.BlockId,
    entry: ir.BlockId,
    join: ir.BlockId,
    incoming: []ir.CfgEdgeRef,
    closure: []ir.BlockId,
    entry_measure: ?usize = null,
    entry_measure_kind: EntryMeasureKind = .conditional,

    pub fn deinit(self: *Split) void {
        self.allocator.free(self.incoming);
        self.allocator.free(self.closure);
        self.* = undefined;
    }
};

pub const EntryMeasureKind = enum {
    conditional,
    interior,
};

pub const ExternalCloneMappings = struct {
    allocator: std.mem.Allocator,
    values: []ir.ValueId,
    clone_values: []ir.ValueId,
    packs: []ir.ValuePackId,
    clone_packs: []ir.ValuePackId,

    pub fn deinit(self: *ExternalCloneMappings) void {
        self.allocator.free(self.values);
        self.allocator.free(self.clone_values);
        self.allocator.free(self.packs);
        self.allocator.free(self.clone_packs);
        self.* = undefined;
    }
};

const UseCollector = struct {
    allocator: std.mem.Allocator,
    values: *std.ArrayList(ir.ValueId),
    packs: *std.ArrayList(ir.ValuePackId),
    out_of_memory: *bool,

    pub fn value(self: UseCollector, value_id: ir.ValueId) void {
        for (self.values.items) |existing| if (existing == value_id) return;
        self.values.append(self.allocator, value_id) catch {
            self.out_of_memory.* = true;
        };
    }

    pub fn pack(self: UseCollector, pack_id: ir.ValuePackId) void {
        for (self.packs.items) |existing| if (existing == pack_id) return;
        self.packs.append(self.allocator, pack_id) catch {
            self.out_of_memory.* = true;
        };
    }

    pub fn place(_: UseCollector, _: ir.PlaceId) void {}
};

const CloneLineageStep = struct {
    source: ir.BlockId,
    clone: ir.BlockId,
    group: ir.NodeSplitGroupId,
};

fn closureContainsValue(program: *const ir.Program, closure: []const ir.BlockId, target: ir.ValueId) bool {
    for (closure) |block_id| {
        if (block_id.index() >= program.blocks.len) continue;
        const block = program.blocks[block_id.index()];
        for (block.parameters) |value_id| if (value_id == target) return true;
        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) continue;
            for (program.instructions[instruction_id.index()].results) |value_id| if (value_id == target) return true;
        }
    }
    return false;
}

fn closureContainsPack(program: *const ir.Program, closure: []const ir.BlockId, target: ir.ValuePackId) bool {
    for (closure) |block_id| {
        if (block_id.index() >= program.blocks.len) continue;
        for (program.blocks[block_id.index()].instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) continue;
            if (program.instructions[instruction_id.index()].pack_result == target) return true;
        }
    }
    return false;
}

fn definitionDominatesIncoming(
    analysis: *const cfg.Analysis,
    producer: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
) bool {
    if (analysis.blockIndex(producer) == null) return false;
    for (incoming) |reference| {
        if (analysis.blockIndex(reference.source) == null or !analysis.dominates(producer, reference.source)) return false;
    }
    return true;
}

// A definition owned by every incoming edge source is already in the exact
// context being cloned.  A downstream sibling clone must not replace it: the
// cloned block is entered from these sources, not from that sibling.
fn incomingEdgesOriginateAtProducer(
    incoming: []const ir.CfgEdgeRef,
    producer: ir.BlockId,
) bool {
    if (incoming.len == 0) return false;
    for (incoming) |reference| if (reference.source != producer) return false;
    return true;
}

fn incomingEdgeIsCanonical(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    reference: ir.CfgEdgeRef,
) bool {
    if (reference.source.index() >= program.blocks.len or reference.target.index() >= program.blocks.len) return false;
    const source = program.blocks[reference.source.index()];
    const target = program.blocks[reference.target.index()];
    if (source.id != reference.source or target.id != reference.target or
        source.function != analysis.function.id or target.function != source.function or
        analysis.blockIndex(reference.source) == null or analysis.blockIndex(reference.target) == null)
    {
        return false;
    }
    const edge = cfg_edge.value(program, reference) orelse return false;
    return edge.target == reference.target and edge.arguments.len == target.parameters.len;
}

fn valueAvailableAtSource(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.BlockId,
    value_id: ir.ValueId,
) bool {
    if (source.index() >= program.blocks.len or
        value_id.index() >= program.values.len or
        analysis.blockIndex(source) == null or
        !analysis.isReachable(source)) return false;
    const source_block = program.blocks[source.index()];
    const value = program.values[value_id.index()];
    if (source_block.id != source or value.id != value_id or
        value.function != source_block.function or
        source_block.function != analysis.function.id) return false;

    switch (value.origin) {
        .parameter, .capture => return true,
        .block_parameter => |origin| {
            if (origin.block.index() >= program.blocks.len) return false;
            const definition_block = program.blocks[origin.block.index()];
            const parameter_index: usize = @intCast(origin.index);
            if (definition_block.id != origin.block or
                definition_block.function != source_block.function or
                parameter_index >= definition_block.parameters.len or
                definition_block.parameters[parameter_index] != value_id)
            {
                return false;
            }
            return origin.block == source or analysis.dominates(origin.block, source);
        },
        .instruction_result => |origin| {
            if (origin.instruction.index() >= program.instructions.len) return false;
            const definition = program.instructions[origin.instruction.index()];
            const result_index: usize = @intCast(origin.index);
            if (definition.id != origin.instruction or
                result_index >= definition.results.len or
                definition.results[result_index] != value_id or
                definition.block.index() >= program.blocks.len)
            {
                return false;
            }
            const definition_block = program.blocks[definition.block.index()];
            if (definition_block.id != definition.block or
                definition_block.function != source_block.function)
            {
                return false;
            }
            if (definition.block != source) return analysis.dominates(definition.block, source);
            for (source_block.instructions) |instruction_id| {
                if (instruction_id == origin.instruction) return true;
            }
            return false;
        },
    }
}

fn packAvailableAtSource(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.BlockId,
    pack_id: ir.ValuePackId,
) bool {
    if (source.index() >= program.blocks.len or
        pack_id.index() >= program.value_packs.len or
        analysis.blockIndex(source) == null or
        !analysis.isReachable(source)) return false;
    const source_block = program.blocks[source.index()];
    const pack = program.value_packs[pack_id.index()];
    if (source_block.id != source or pack.id != pack_id or
        pack.function != source_block.function or
        source_block.function != analysis.function.id) return false;

    switch (pack.origin) {
        .varargs => return true,
        .instruction_result => |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) return false;
            const definition = program.instructions[instruction_id.index()];
            if (definition.id != instruction_id or
                definition.pack_result != pack_id or
                definition.block.index() >= program.blocks.len)
            {
                return false;
            }
            const definition_block = program.blocks[definition.block.index()];
            if (definition_block.id != definition.block or
                definition_block.function != source_block.function)
            {
                return false;
            }
            if (definition.block != source) return analysis.dominates(definition.block, source);
            for (source_block.instructions) |candidate| {
                if (candidate == instruction_id) return true;
            }
            return false;
        },
    }
}

fn valueAvailableAtIncomingSources(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    value_id: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
) bool {
    if (incoming.len == 0) return false;
    for (incoming) |reference| {
        if (!valueAvailableAtSource(program, analysis, reference.source, value_id)) return false;
    }
    return true;
}

fn packAvailableAtIncomingSources(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    pack_id: ir.ValuePackId,
    incoming: []const ir.CfgEdgeRef,
) bool {
    if (incoming.len == 0) return false;
    for (incoming) |reference| {
        if (!packAvailableAtSource(program, analysis, reference.source, pack_id)) return false;
    }
    return true;
}

fn selectBoundaryValueMapping(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.ValueId,
    mapped: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
) ?ir.ValueId {
    if (valueAvailableAtIncomingSources(program, analysis, mapped, incoming)) return mapped;
    if (valueAvailableAtIncomingSources(program, analysis, source, incoming)) return source;
    return null;
}

fn selectBoundaryPackMapping(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.ValuePackId,
    mapped: ir.ValuePackId,
    incoming: []const ir.CfgEdgeRef,
) ?ir.ValuePackId {
    if (packAvailableAtIncomingSources(program, analysis, mapped, incoming)) return mapped;
    if (packAvailableAtIncomingSources(program, analysis, source, incoming)) return source;
    return null;
}

fn nodeSplitRewriteArgumentsAreStable(
    program: *const ir.Program,
    rewrite: ir.CfgEdgeRewrite,
) bool {
    if (rewrite.rule != .node_split or rewrite.from.target.index() >= program.blocks.len or
        rewrite.to.target.index() >= program.blocks.len)
    {
        return false;
    }
    const source = program.blocks[rewrite.from.target.index()];
    const clone = program.blocks[rewrite.to.target.index()];
    return source.id == rewrite.from.target and clone.id == rewrite.to.target and
        source.function == clone.function and
        rewrite.from.arguments.len == source.parameters.len and
        rewrite.to.arguments.len == clone.parameters.len and
        std.mem.eql(ir.ValueId, rewrite.from.arguments, rewrite.to.arguments);
}

// Clone provenance is queried from the external-mapping hot path.  Keep its
// immutable lookup state local to one mapping transaction so lineage checks do
// not rescan the complete rewrite history for every candidate value.
const CloneLineageIndex = struct {
    allocator: std.mem.Allocator,
    steps: []?CloneLineageStep,
    malformed: []bool,
    stable: []bool,
    function_id: ?ir.FunctionId = null,

    fn init(allocator: std.mem.Allocator, program: *const ir.Program) std.mem.Allocator.Error!CloneLineageIndex {
        return initWithFunction(allocator, program, null);
    }

    fn initForFunction(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        function_id: ir.FunctionId,
    ) std.mem.Allocator.Error!CloneLineageIndex {
        return initWithFunction(allocator, program, function_id);
    }

    fn initWithFunction(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        function_id: ?ir.FunctionId,
    ) std.mem.Allocator.Error!CloneLineageIndex {
        const steps = try allocator.alloc(?CloneLineageStep, program.blocks.len);
        errdefer allocator.free(steps);
        const malformed = try allocator.alloc(bool, program.blocks.len);
        errdefer allocator.free(malformed);
        const stable = try allocator.alloc(bool, program.blocks.len);
        errdefer allocator.free(stable);
        @memset(steps, null);
        @memset(malformed, false);
        @memset(stable, true);

        for (program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.from.target == rewrite.to.target) continue;
            if (function_id) |selected_function| {
                if (!rewriteBelongsToFunction(program, rewrite, selected_function)) continue;
            }
            const clone_index = rewrite.to.target.index();
            if (clone_index >= program.blocks.len) continue;
            if (rewrite.from.target.index() >= program.blocks.len) {
                malformed[clone_index] = true;
                continue;
            }
            const source = program.blocks[rewrite.from.target.index()];
            const clone = program.blocks[clone_index];
            const group = rewrite.node_split_group orelse {
                malformed[clone_index] = true;
                continue;
            };
            if (source.id != rewrite.from.target or clone.id != rewrite.to.target or
                source.function != clone.function)
            {
                malformed[clone_index] = true;
                continue;
            }
            if (!nodeSplitRewriteArgumentsAreStable(program, rewrite)) stable[clone_index] = false;
            const lineage_step: CloneLineageStep = .{
                .source = rewrite.from.target,
                .clone = rewrite.to.target,
                .group = group,
            };
            if (steps[clone_index]) |existing| {
                if (existing.source != lineage_step.source or existing.group != lineage_step.group) {
                    malformed[clone_index] = true;
                }
            } else {
                steps[clone_index] = lineage_step;
            }
        }

        return .{
            .allocator = allocator,
            .steps = steps,
            .malformed = malformed,
            .stable = stable,
            .function_id = function_id,
        };
    }

    fn rewriteBelongsToFunction(
        program: *const ir.Program,
        rewrite: ir.CfgEdgeRewrite,
        function_id: ir.FunctionId,
    ) bool {
        if (rewrite.source.index() >= program.blocks.len or
            rewrite.from.target.index() >= program.blocks.len or
            rewrite.to.target.index() >= program.blocks.len)
        {
            return false;
        }
        const source = program.blocks[rewrite.source.index()];
        const from = program.blocks[rewrite.from.target.index()];
        const to = program.blocks[rewrite.to.target.index()];
        return source.id == rewrite.source and from.id == rewrite.from.target and
            to.id == rewrite.to.target and source.function == function_id and
            from.function == function_id and to.function == function_id;
    }

    fn deinit(self: *CloneLineageIndex) void {
        self.allocator.free(self.steps);
        self.allocator.free(self.malformed);
        self.allocator.free(self.stable);
        self.* = undefined;
    }

    fn isMalformed(self: *const CloneLineageIndex, block: ir.BlockId) bool {
        return block.index() >= self.malformed.len or self.malformed[block.index()];
    }

    fn step(self: *const CloneLineageIndex, program: *const ir.Program, target: ir.BlockId) ?CloneLineageStep {
        if (target.index() >= self.steps.len or target.index() >= program.blocks.len or
            program.blocks[target.index()].id != target or self.isMalformed(target))
        {
            return null;
        }
        if (self.function_id) |selected| {
            if (program.blocks[target.index()].function != selected) return null;
        }
        return self.steps[target.index()];
    }

    fn isStable(self: *const CloneLineageIndex, program: *const ir.Program, block: ir.BlockId) bool {
        if (block.index() >= self.stable.len or block.index() >= program.blocks.len or
            program.blocks[block.index()].id != block)
        {
            return false;
        }
        if (self.function_id) |selected| {
            if (program.blocks[block.index()].function != selected) return false;
        }
        return !self.isMalformed(block) and self.stable[block.index()];
    }
};

const ReplayCacheKey = struct {
    source: ir.BlockId,
    clone: ir.BlockId,
    group: ir.NodeSplitGroupId,
};

// Replay mappings are immutable for one clone transaction. Cache them by
// lineage step so each external value and pack can reuse the same mapping
// instead of rebuilding the active clone history. The index is scoped with
// the cache because the graph and replay history are immutable only for this
// context.
const ReplayCache = struct {
    const Entry = struct {
        source: ir.BlockId,
        clone: ir.BlockId,
        group: ir.NodeSplitGroupId,
        mappings: node_split.ReplayMappings,
    };

    allocator: std.mem.Allocator,
    program: *const ir.Program,
    // ReplayIndex owns only slice-backed lookup tables. Keep a value copy so
    // the cache never points at the temporary index used during context init.
    replay_index: node_split.ReplayIndex,
    entries: std.ArrayList(Entry) = .empty,
    entry_indices: std.AutoHashMapUnmanaged(ReplayCacheKey, usize) = .empty,

    fn init(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        replay_index: *const node_split.ReplayIndex,
    ) ReplayCache {
        return .{
            .allocator = allocator,
            .program = program,
            .replay_index = replay_index.*,
        };
    }

    fn deinit(self: *ReplayCache) void {
        self.entry_indices.deinit(self.allocator);
        for (self.entries.items) |*entry| entry.mappings.deinit();
        self.entries.deinit(self.allocator);
        self.* = undefined;
    }

    fn get(
        self: *ReplayCache,
        source: ir.BlockId,
        clone: ir.BlockId,
        group: ir.NodeSplitGroupId,
    ) std.mem.Allocator.Error!?*const node_split.ReplayMappings {
        const key = ReplayCacheKey{ .source = source, .clone = clone, .group = group };
        if (self.entry_indices.get(key)) |entry_index| {
            std.debug.assert(entry_index < self.entries.items.len);
            return &self.entries.items[entry_index].mappings;
        }

        var mappings = (try node_split.replayMappingsForCloneAllocWithIndex(
            self.allocator,
            self.program,
            &self.replay_index,
            source,
            clone,
            group,
        )) orelse return null;
        self.entries.append(self.allocator, .{
            .source = source,
            .clone = clone,
            .group = group,
            .mappings = mappings,
        }) catch |err| {
            mappings.deinit();
            return err;
        };
        const entry_index = self.entries.items.len - 1;
        errdefer {
            var entry = self.entries.pop().?;
            entry.mappings.deinit();
        }
        try self.entry_indices.put(self.allocator, key, entry_index);
        return &self.entries.items[entry_index].mappings;
    }
};

fn activeNodeSplitRewrite(program: *const ir.Program, rewrite: ir.CfgEdgeRewrite) bool {
    if (rewrite.rule != .node_split or rewrite.node_split_group == null or
        rewrite.source.index() >= program.blocks.len or rewrite.to.target.index() >= program.blocks.len)
    {
        return false;
    }
    const source = program.blocks[rewrite.source.index()];
    const clone = program.blocks[rewrite.to.target.index()];
    if (source.id != rewrite.source or clone.id != rewrite.to.target or
        source.function != clone.function)
    {
        return false;
    }
    const reference: ir.CfgEdgeRef = .{
        .source = rewrite.source,
        .kind = rewrite.kind,
        .target = rewrite.to.target,
    };
    const current = cfg_edge.value(program, reference) orelse return false;
    return current.target == rewrite.to.target and
        std.mem.eql(ir.ValueId, current.arguments, rewrite.to.arguments);
}

fn edgeReferenceForKind(
    program: *const ir.Program,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
) ?ir.CfgEdgeRef {
    if (source.index() >= program.blocks.len) return null;
    const block = program.blocks[source.index()];
    if (block.id != source) return null;
    return switch (block.terminator) {
        .jump => |edge| if (kind == .jump)
            .{ .source = source, .kind = .jump, .target = edge.target }
        else
            null,
        .branch => |branch| switch (kind) {
            .branch_then => .{ .source = source, .kind = .branch_then, .target = branch.then_edge.target },
            .branch_else => .{ .source = source, .kind = .branch_else, .target = branch.else_edge.target },
            .jump => null,
        },
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => null,
    };
}

fn replayedEdgeArgumentsMatch(
    program: *const ir.Program,
    source: ir.BlockId,
    clone: ir.BlockId,
    source_edge: ir.Edge,
    clone_edge: ir.Edge,
    replay: node_split.ReplayMappings,
    targets_equivalent: bool,
) bool {
    // The caller has already authenticated paired successor lineage.  Keep
    // argument replay separate so a cloned endpoint may have a distinct ID
    // without weakening the value mapping proof.
    if ((!targets_equivalent and source_edge.target != clone_edge.target) or
        source_edge.arguments.len != clone_edge.arguments.len) return false;
    for (source_edge.arguments, clone_edge.arguments) |source_value, clone_value| {
        const mapped = mapValueFromReplay(program, source, clone, source_value, replay) orelse return false;
        if (mapped != clone_value) return false;
    }
    return true;
}

test "replayed edge arguments require authenticated equivalent targets" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const clone = ir.BlockId.fromIndex(1);
    const source_target = ir.BlockId.fromIndex(2);
    const clone_target = ir.BlockId.fromIndex(3);
    const source_value = ir.ValueId.fromIndex(0);
    const clone_value = ir.ValueId.fromIndex(1);

    const blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = clone, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = source_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = clone_target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ source_value, clone_value },
        .blocks = &.{ source, clone, source_target, clone_target },
        .entry_block = source,
    };
    const values = [_]ir.Value{
        .{ .id = source_value, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = clone_value, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
    };
    const program = ir.Program{
        .program_id = "replayed-edge-equivalent-targets",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &.{},
    };
    var replay_source_values = [_]ir.ValueId{source_value};
    var replay_clone_values = [_]ir.ValueId{clone_value};
    var replay_source_packs = [_]ir.ValuePackId{};
    var replay_clone_packs = [_]ir.ValuePackId{};
    const replay = node_split.ReplayMappings{
        .allocator = std.testing.allocator,
        .source_values = replay_source_values[0..],
        .clone_values = replay_clone_values[0..],
        .source_packs = replay_source_packs[0..],
        .clone_packs = replay_clone_packs[0..],
        .history_start = null,
    };
    const source_edge = ir.Edge{ .target = source_target, .arguments = &.{source_value} };
    const clone_edge = ir.Edge{ .target = clone_target, .arguments = &.{clone_value} };

    try std.testing.expect(replayedEdgeArgumentsMatch(
        &program,
        source,
        clone,
        source_edge,
        clone_edge,
        replay,
        true,
    ));
    try std.testing.expect(!replayedEdgeArgumentsMatch(
        &program,
        source,
        clone,
        source_edge,
        clone_edge,
        replay,
        false,
    ));

    const forged_edge = ir.Edge{ .target = clone_target, .arguments = &.{source_value} };
    try std.testing.expect(!replayedEdgeArgumentsMatch(
        &program,
        source,
        clone,
        source_edge,
        forged_edge,
        replay,
        true,
    ));
}

fn projectionValueProducer(program: *const ir.Program, value_id: ir.ValueId) ?ir.BlockId {
    if (value_id.index() >= program.values.len) return null;
    const value = program.values[value_id.index()];
    if (value.id != value_id or value.function.index() >= program.functions.len) return null;
    return switch (value.origin) {
        .parameter, .capture => null,
        .block_parameter => |origin| origin.block,
        .instruction_result => |origin| if (origin.instruction.index() < program.instructions.len) blk: {
            const instruction = program.instructions[origin.instruction.index()];
            if (instruction.id != origin.instruction) break :blk null;
            break :blk instruction.block;
        } else null,
    };
}

fn cloneLineageArgumentsAreStableCached(
    program: *const ir.Program,
    block: ir.BlockId,
    index: ?*const CloneLineageIndex,
) bool {
    var current = block;
    var depth: usize = 0;
    while (true) {
        if (index) |cached| {
            if (cached.isMalformed(current) or !cached.isStable(program, current)) return false;
        }
        const step = cloneStepForTargetCached(program, current, index) orelse break;
        depth = std.math.add(usize, depth, 1) catch return false;
        if (depth > program.blocks.len) return false;
        current = step.source;
    }
    return true;
}

fn externalBlockParameterBlock(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    value_id: ir.ValueId,
    block_id: ir.BlockId,
    parameter_index: u32,
) ?ir.BlockId {
    if (block_id.index() >= program.blocks.len) return null;
    const block = program.blocks[block_id.index()];
    const index: usize = @intCast(parameter_index);
    if (block.id != block_id or block.function != analysis.function.id or
        index >= block.parameters.len or block.parameters[index] != value_id)
    {
        return null;
    }
    return block_id;
}

fn cloneStepForTarget(program: *const ir.Program, target: ir.BlockId) ?CloneLineageStep {
    if (target.index() >= program.blocks.len) return null;
    const target_block = program.blocks[target.index()];
    if (target_block.id != target) return null;
    var selected: ?CloneLineageStep = null;
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.rule != .node_split or rewrite.to.target != target or rewrite.from.target == target) continue;
        if (rewrite.from.target.index() >= program.blocks.len) return null;
        const source_block = program.blocks[rewrite.from.target.index()];
        if (source_block.id != rewrite.from.target or source_block.function != target_block.function) return null;
        const step: CloneLineageStep = .{
            .source = rewrite.from.target,
            .clone = target,
            .group = rewrite.node_split_group orelse return null,
        };
        if (selected) |existing| {
            if (existing.source != step.source or existing.group != step.group) return null;
        } else {
            selected = step;
        }
    }
    return selected;
}

fn cloneStepForTargetCached(
    program: *const ir.Program,
    target: ir.BlockId,
    index: ?*const CloneLineageIndex,
) ?CloneLineageStep {
    if (index) |cached| return cached.step(program, target);
    return cloneStepForTarget(program, target);
}

const CloneLineagePosition = struct {
    root: ir.BlockId,
    depth: usize,
};

fn cloneLineagePositionCached(
    program: *const ir.Program,
    block: ir.BlockId,
    index: ?*const CloneLineageIndex,
) ?CloneLineagePosition {
    if (block.index() >= program.blocks.len or program.blocks[block.index()].id != block) return null;
    var current = block;
    var depth: usize = 0;
    while (true) {
        const step = cloneStepForTargetCached(program, current, index) orelse return .{ .root = current, .depth = depth };
        depth = std.math.add(usize, depth, 1) catch return null;
        if (depth > program.blocks.len) return null;
        current = step.source;
    }
}

fn cloneLineagesCompatibleCached(
    program: *const ir.Program,
    left: ir.BlockId,
    right: ir.BlockId,
    index: ?*const CloneLineageIndex,
) bool {
    if (left == right) return true;
    const left_position = cloneLineagePositionCached(program, left, index) orelse return false;
    const right_position = cloneLineagePositionCached(program, right, index) orelse return false;
    if (left_position.root != right_position.root) return true;

    var left_current = left;
    var right_current = right;
    var left_depth = left_position.depth;
    var right_depth = right_position.depth;
    while (left_depth > right_depth) : (left_depth -= 1) {
        left_current = (cloneStepForTargetCached(program, left_current, index) orelse return false).source;
    }
    while (right_depth > left_depth) : (right_depth -= 1) {
        right_current = (cloneStepForTargetCached(program, right_current, index) orelse return false).source;
    }
    return left_current == right_current;
}

test "same-root composed clone bridge requires complete replay ownership" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const root = ir.BlockId.fromIndex(1);
    const source_clone = ir.BlockId.fromIndex(2);
    const target_clone = ir.BlockId.fromIndex(3);
    const foreign_owner = ir.BlockId.fromIndex(4);
    const selector = ir.ValueId.fromIndex(0);
    const edge_value = ir.ValueId.fromIndex(1);
    const other_value = ir.ValueId.fromIndex(2);
    const root_parameter = ir.ValueId.fromIndex(3);
    const source_clone_parameter = ir.ValueId.fromIndex(4);
    const target_clone_parameter = ir.ValueId.fromIndex(5);
    const function_parameters = [_]ir.ValueId{ selector, edge_value, other_value };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .branch_else,
            .from = .{ .target = root, .arguments = &.{edge_value} },
            .to = .{ .target = source_clone, .arguments = &.{edge_value} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(10),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = root,
            .kind = .jump,
            .from = .{ .target = root, .arguments = &.{edge_value} },
            .to = .{ .target = target_clone, .arguments = &.{edge_value} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(20),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = source_clone,
            .kind = .jump,
            .from = .{ .target = root, .arguments = &.{edge_value} },
            .to = .{ .target = target_clone, .arguments = &.{edge_value} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(20),
        },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = root, .arguments = &.{edge_value} },
            .else_edge = .{ .target = source_clone, .arguments = &.{edge_value} },
        } } },
        .{ .id = root, .function = function_id, .parameters = &.{root_parameter}, .terminator = .{ .jump = .{
            .target = target_clone,
            .arguments = &.{edge_value},
        } } },
        .{ .id = source_clone, .function = function_id, .parameters = &.{source_clone_parameter}, .terminator = .{ .jump = .{
            .target = target_clone,
            .arguments = &.{edge_value},
        } } },
        .{ .id = target_clone, .function = function_id, .parameters = &.{target_clone_parameter}, .terminator = .{ .jump = .{
            .target = target_clone,
            .arguments = &.{edge_value},
        } } },
        .{ .id = foreign_owner, .function = function_id, .terminator = .{ .jump = .{
            .target = target_clone,
            .arguments = &.{edge_value},
        } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = function_parameters[0..],
        .blocks = &.{ entry, root, source_clone, target_clone, foreign_owner },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = edge_value, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = other_value, .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = root_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = root, .index = 0 } } },
        .{ .id = source_clone_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_clone, .index = 0 } } },
        .{ .id = target_clone_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_clone, .index = 0 } } },
    };
    const program = ir.Program{
        .program_id = "same-root-composed-clone-bridge",
        .entry_function = function_id,
        .functions = &.{functions[0]},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(std.testing.allocator, &program, &replay_index);
    defer replay_cache.deinit();

    const incoming = ir.CfgEdgeRef{ .source = source_clone, .kind = .jump, .target = target_clone };
    const authentic = try hasAuthenticatedComposedCloneBridgeAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        incoming,
        &lineage_index,
        &replay_index,
        &replay_cache,
    );
    try std.testing.expect(authentic);

    var tampered_blocks = blocks;
    tampered_blocks[source_clone.index()].terminator = .{ .jump = .{
        .target = target_clone,
        .arguments = &.{other_value},
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, functions[0]);
    defer tampered_analysis.deinit();
    var tampered_lineage = try CloneLineageIndex.init(std.testing.allocator, &tampered_program);
    defer tampered_lineage.deinit();
    var tampered_replay = try node_split.ReplayIndex.init(std.testing.allocator, &tampered_program);
    defer tampered_replay.deinit();
    var tampered_cache = ReplayCache.init(std.testing.allocator, &tampered_program, &tampered_replay);
    defer tampered_cache.deinit();
    const tampered_authentic = try hasAuthenticatedComposedCloneBridgeAlloc(
        std.testing.allocator,
        &tampered_program,
        &tampered_analysis,
        incoming,
        &tampered_lineage,
        &tampered_replay,
        &tampered_cache,
    );
    try std.testing.expect(!tampered_authentic);

    var foreign_rewrites = rewrites;
    foreign_rewrites[1].source = foreign_owner;
    var foreign_program = program;
    foreign_program.edge_rewrites = &foreign_rewrites;
    var foreign_lineage = try CloneLineageIndex.init(std.testing.allocator, &foreign_program);
    defer foreign_lineage.deinit();
    var foreign_replay = try node_split.ReplayIndex.init(std.testing.allocator, &foreign_program);
    defer foreign_replay.deinit();
    var foreign_cache = ReplayCache.init(std.testing.allocator, &foreign_program, &foreign_replay);
    defer foreign_cache.deinit();
    const foreign_authentic = try hasAuthenticatedComposedCloneBridgeAlloc(
        std.testing.allocator,
        &foreign_program,
        &analysis,
        incoming,
        &foreign_lineage,
        &foreign_replay,
        &foreign_cache,
    );
    try std.testing.expect(!foreign_authentic);

    var inconsistent_rewrites = [_]ir.CfgEdgeRewrite{
        rewrites[0],
        rewrites[1],
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = root,
            .kind = .jump,
            .from = .{ .target = root, .arguments = &.{edge_value} },
            .to = .{ .target = target_clone, .arguments = &.{edge_value} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(30),
        },
    };
    var inconsistent_program = program;
    inconsistent_program.edge_rewrites = &inconsistent_rewrites;
    var inconsistent_lineage = try CloneLineageIndex.init(std.testing.allocator, &inconsistent_program);
    defer inconsistent_lineage.deinit();
    var inconsistent_replay = try node_split.ReplayIndex.init(std.testing.allocator, &inconsistent_program);
    defer inconsistent_replay.deinit();
    var inconsistent_cache = ReplayCache.init(std.testing.allocator, &inconsistent_program, &inconsistent_replay);
    defer inconsistent_cache.deinit();
    const inconsistent_authentic = try hasAuthenticatedComposedCloneBridgeAlloc(
        std.testing.allocator,
        &inconsistent_program,
        &analysis,
        incoming,
        &inconsistent_lineage,
        &inconsistent_replay,
        &inconsistent_cache,
    );
    try std.testing.expect(!inconsistent_authentic);

    var incomplete_rewrites = [_]ir.CfgEdgeRewrite{rewrites[1]};
    var incomplete_program = program;
    incomplete_program.edge_rewrites = &incomplete_rewrites;
    var incomplete_lineage = try CloneLineageIndex.init(std.testing.allocator, &incomplete_program);
    defer incomplete_lineage.deinit();
    var incomplete_replay = try node_split.ReplayIndex.init(std.testing.allocator, &incomplete_program);
    defer incomplete_replay.deinit();
    var incomplete_cache = ReplayCache.init(std.testing.allocator, &incomplete_program, &incomplete_replay);
    defer incomplete_cache.deinit();
    try std.testing.expect(!try hasAuthenticatedComposedCloneBridgeAlloc(
        std.testing.allocator,
        &incomplete_program,
        &analysis,
        incoming,
        &incomplete_lineage,
        &incomplete_replay,
        &incomplete_cache,
    ));
}

test "cross-root clone bridge composes an authenticated original edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source_root = ir.BlockId.fromIndex(1);
    const target_root = ir.BlockId.fromIndex(2);
    const source_clone = ir.BlockId.fromIndex(3);
    const target_clone = ir.BlockId.fromIndex(4);
    const exit = ir.BlockId.fromIndex(5);
    const selector = ir.ValueId.fromIndex(0);
    const source_parameter = ir.ValueId.fromIndex(1);
    const source_clone_parameter = ir.ValueId.fromIndex(2);
    const target_parameter = ir.ValueId.fromIndex(3);
    const target_clone_parameter = ir.ValueId.fromIndex(4);
    const alternate = ir.ValueId.fromIndex(5);
    const function_parameters = [_]ir.ValueId{ selector, alternate };
    const source_root_parameters = [_]ir.ValueId{source_parameter};
    const source_clone_parameters = [_]ir.ValueId{source_clone_parameter};
    const target_root_parameters = [_]ir.ValueId{target_parameter};
    const target_clone_parameters = [_]ir.ValueId{target_clone_parameter};

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = source_root, .arguments = &.{alternate} },
            .else_edge = .{ .target = source_clone, .arguments = &.{alternate} },
        } } },
        .{ .id = source_root, .function = function_id, .parameters = &source_root_parameters, .terminator = .{ .jump = .{
            .target = target_clone,
            .arguments = &.{alternate},
        } } },
        .{ .id = target_root, .function = function_id, .parameters = &target_root_parameters, .terminator = .{ .jump = .{
            .target = exit,
        } } },
        .{ .id = source_clone, .function = function_id, .parameters = &source_clone_parameters, .terminator = .{ .jump = .{
            .target = target_clone,
            .arguments = &.{alternate},
        } } },
        .{ .id = target_clone, .function = function_id, .parameters = &target_clone_parameters, .terminator = .{ .jump = .{
            .target = exit,
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &function_parameters,
        .blocks = &.{ entry, source_root, target_root, source_clone, target_clone, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = source_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_root, .index = 0 } } },
        .{ .id = source_clone_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source_clone, .index = 0 } } },
        .{ .id = target_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_root, .index = 0 } } },
        .{ .id = target_clone_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_clone, .index = 0 } } },
        .{ .id = alternate, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
    };
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .branch_else,
            .from = .{ .target = source_root, .arguments = &.{alternate} },
            .to = .{ .target = source_clone, .arguments = &.{alternate} },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = source_clone,
            .kind = .jump,
            .from = .{ .target = target_root, .arguments = &.{alternate} },
            .to = .{ .target = target_clone, .arguments = &.{alternate} },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = source_root,
            .kind = .jump,
            .from = .{ .target = target_root, .arguments = &.{alternate} },
            .to = .{ .target = target_clone, .arguments = &.{alternate} },
            .rule = .node_split,
            .node_split_group = group,
        },
    };
    const program = ir.Program{
        .program_id = "cross-root-authenticated-edge",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(std.testing.allocator, &program, &replay_index);
    defer replay_cache.deinit();

    const incoming = ir.CfgEdgeRef{ .source = source_clone, .kind = .jump, .target = target_clone };
    try std.testing.expect(try hasAuthenticatedComposedCloneBridgeAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        incoming,
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));

    var wrong_root_blocks = blocks;
    wrong_root_blocks[source_root.index()].terminator = .{ .jump = .{ .target = exit, .arguments = &.{alternate} } };
    var wrong_root_program = program;
    wrong_root_program.blocks = &wrong_root_blocks;
    var wrong_root_analysis = try cfg.Analysis.init(std.testing.allocator, &wrong_root_program, functions[0]);
    defer wrong_root_analysis.deinit();
    var wrong_root_lineage = try CloneLineageIndex.init(std.testing.allocator, &wrong_root_program);
    defer wrong_root_lineage.deinit();
    var wrong_root_replay = try node_split.ReplayIndex.init(std.testing.allocator, &wrong_root_program);
    defer wrong_root_replay.deinit();
    var wrong_root_cache = ReplayCache.init(std.testing.allocator, &wrong_root_program, &wrong_root_replay);
    defer wrong_root_cache.deinit();
    try std.testing.expect(!try hasAuthenticatedComposedCloneBridgeAlloc(
        std.testing.allocator,
        &wrong_root_program,
        &wrong_root_analysis,
        incoming,
        &wrong_root_lineage,
        &wrong_root_replay,
        &wrong_root_cache,
    ));

    const wrong_kind = ir.CfgEdgeRef{ .source = source_clone, .kind = .branch_then, .target = target_clone };
    try std.testing.expect(!try hasAuthenticatedComposedCloneBridgeAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        wrong_kind,
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));

    var tampered_rewrites = rewrites;
    tampered_rewrites[1].to.arguments = &.{selector};
    var tampered_program = program;
    tampered_program.edge_rewrites = &tampered_rewrites;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, functions[0]);
    defer tampered_analysis.deinit();
    var tampered_lineage = try CloneLineageIndex.init(std.testing.allocator, &tampered_program);
    defer tampered_lineage.deinit();
    var tampered_replay = try node_split.ReplayIndex.init(std.testing.allocator, &tampered_program);
    defer tampered_replay.deinit();
    var tampered_cache = ReplayCache.init(std.testing.allocator, &tampered_program, &tampered_replay);
    defer tampered_cache.deinit();
    try std.testing.expect(!try hasAuthenticatedComposedCloneBridgeAlloc(
        std.testing.allocator,
        &tampered_program,
        &tampered_analysis,
        incoming,
        &tampered_lineage,
        &tampered_replay,
        &tampered_cache,
    ));
}

test "owner composed bridge replays the source clone edge tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source_root = ir.BlockId.fromIndex(1);
    const target_root = ir.BlockId.fromIndex(2);
    const source_clone = ir.BlockId.fromIndex(3);
    const target_clone = ir.BlockId.fromIndex(4);
    const exit = ir.BlockId.fromIndex(5);
    const selector = ir.ValueId.fromIndex(0);
    const alternate = ir.ValueId.fromIndex(1);
    const other = ir.ValueId.fromIndex(2);
    const source_result = ir.ValueId.fromIndex(3);
    const clone_result = ir.ValueId.fromIndex(4);
    const target_parameter = ir.ValueId.fromIndex(5);
    const target_clone_parameter = ir.ValueId.fromIndex(6);
    const source_instruction = ir.InstructionId.fromIndex(0);
    const clone_instruction = ir.InstructionId.fromIndex(1);
    const group_source = ir.NodeSplitGroupId.fromIndex(10);
    const group_target = ir.NodeSplitGroupId.fromIndex(20);
    const function_parameters = [_]ir.ValueId{ selector, alternate, other };
    const source_result_arguments = [_]ir.ValueId{source_result};
    const clone_result_arguments = [_]ir.ValueId{clone_result};
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = source_root },
            .else_edge = .{ .target = source_clone },
        } } },
        .{ .id = source_root, .function = function_id, .instructions = &.{source_instruction}, .terminator = .{ .jump = .{
            .target = target_clone,
            .arguments = source_result_arguments[0..],
        } } },
        .{ .id = target_root, .function = function_id, .parameters = &.{target_parameter}, .terminator = .{ .jump = .{
            .target = exit,
        } } },
        .{ .id = source_clone, .function = function_id, .instructions = &.{clone_instruction}, .terminator = .{ .jump = .{
            .target = target_clone,
            .arguments = clone_result_arguments[0..],
        } } },
        .{ .id = target_clone, .function = function_id, .parameters = &.{target_clone_parameter}, .terminator = .{ .jump = .{
            .target = exit,
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = function_parameters[0..],
        .blocks = &.{ entry, source_root, target_root, source_clone, target_clone, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = alternate, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = other, .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = source_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = source_instruction, .index = 0 } } },
        .{ .id = clone_result, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = clone_instruction, .index = 0 } } },
        .{ .id = target_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_root, .index = 0 } } },
        .{ .id = target_clone_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_clone, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = source_instruction, .block = source_root, .operation = .{ .constant = .{ .number = 7 } }, .results = &.{source_result}, .effects = .pure },
        .{ .id = clone_instruction, .block = source_clone, .operation = .{ .constant = .{ .number = 7 } }, .results = &.{clone_result}, .effects = .pure },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .branch_else,
            .from = .{ .target = source_root },
            .to = .{ .target = source_clone },
            .rule = .node_split,
            .node_split_group = group_source,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = source_root,
            .kind = .jump,
            .from = .{ .target = target_root, .arguments = source_result_arguments[0..] },
            .to = .{ .target = target_clone, .arguments = source_result_arguments[0..] },
            .rule = .node_split,
            .node_split_group = group_target,
        },
    };
    const program = ir.Program{
        .program_id = "generic-owner-edge-tuple-replay",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var lineage = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer lineage.deinit();
    var replay = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer replay.deinit();
    var cache = ReplayCache.init(std.testing.allocator, &program, &replay);
    defer cache.deinit();

    const incoming = ir.CfgEdgeRef{ .source = source_clone, .kind = .jump, .target = target_clone };
    try std.testing.expect(try hasAuthenticatedComposedCloneBridgeAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        incoming,
        &lineage,
        &replay,
        &cache,
    ));

    var tampered_blocks = blocks;
    tampered_blocks[source_clone.index()].terminator = .{ .jump = .{
        .target = target_clone,
        .arguments = &.{selector},
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, functions[0]);
    defer tampered_analysis.deinit();
    var tampered_lineage = try CloneLineageIndex.init(std.testing.allocator, &tampered_program);
    defer tampered_lineage.deinit();
    var tampered_replay = try node_split.ReplayIndex.init(std.testing.allocator, &tampered_program);
    defer tampered_replay.deinit();
    var tampered_cache = ReplayCache.init(std.testing.allocator, &tampered_program, &tampered_replay);
    defer tampered_cache.deinit();
    try std.testing.expect(!try hasAuthenticatedComposedCloneBridgeAlloc(
        std.testing.allocator,
        &tampered_program,
        &tampered_analysis,
        incoming,
        &tampered_lineage,
        &tampered_replay,
        &tampered_cache,
    ));
}

test "boundary mapping rejects downstream identities and preserves available originals" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const incoming_source = ir.BlockId.fromIndex(1);
    const producer = ir.BlockId.fromIndex(2);
    const closure = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const selector = ir.ValueId.fromIndex(0);
    const seed = ir.ValueId.fromIndex(1);
    const callee = ir.ValueId.fromIndex(2);
    const downstream_value = ir.ValueId.fromIndex(3);
    const mapped_value = ir.ValueId.fromIndex(4);
    const source_pack = ir.ValuePackId.fromIndex(0);
    const mapped_pack = ir.ValuePackId.fromIndex(1);
    const produce_instruction = ir.InstructionId.fromIndex(0);

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = incoming_source },
            .else_edge = .{ .target = producer, .arguments = &.{seed} },
        } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{ .target = closure } } },
        .{ .id = producer, .function = function_id, .parameters = &.{downstream_value}, .instructions = &.{produce_instruction}, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = closure, .function = function_id, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, seed, callee },
        .blocks = &.{ entry, incoming_source, producer, closure, exit },
        .entry_block = entry,
        .is_variadic = true,
        .vararg_pack = source_pack,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = seed, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = callee, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } },
        .{ .id = downstream_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer, .index = 0 } } },
        .{ .id = mapped_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = produce_instruction, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = produce_instruction,
        .block = producer,
        .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .variadic = {} } } },
        .results = &.{mapped_value},
        .pack_result = mapped_pack,
        .effects = ir.EffectSummary.dynamic_call,
    }};
    const packs = [_]ir.ValuePack{
        .{ .id = source_pack, .function = function_id, .origin = .{ .varargs = function_id } },
        .{ .id = mapped_pack, .function = function_id, .origin = .{ .instruction_result = produce_instruction } },
    };
    const program: ir.Program = .{
        .program_id = "downstream-boundary-mapping",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = incoming_source,
        .kind = .jump,
        .target = closure,
    }};

    try std.testing.expect(!valueAvailableAtIncomingSources(&program, &analysis, mapped_value, &incoming));
    try std.testing.expect(valueAvailableAtIncomingSources(&program, &analysis, seed, &incoming));
    try std.testing.expectEqual(seed, selectBoundaryValueMapping(
        &program,
        &analysis,
        seed,
        mapped_value,
        &incoming,
    ).?);
    try std.testing.expect(selectBoundaryValueMapping(
        &program,
        &analysis,
        downstream_value,
        mapped_value,
        &incoming,
    ) == null);

    try std.testing.expect(!packAvailableAtIncomingSources(&program, &analysis, mapped_pack, &incoming));
    try std.testing.expect(packAvailableAtIncomingSources(&program, &analysis, source_pack, &incoming));
    try std.testing.expectEqual(source_pack, selectBoundaryPackMapping(
        &program,
        &analysis,
        source_pack,
        mapped_pack,
        &incoming,
    ).?);
}

fn cloneLineageAllocCached(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.BlockId,
    clone: ir.BlockId,
    index: ?*const CloneLineageIndex,
) std.mem.Allocator.Error!?[]CloneLineageStep {
    if (source.index() >= program.blocks.len or clone.index() >= program.blocks.len) return null;
    if (program.blocks[source.index()].id != source or program.blocks[clone.index()].id != clone or
        program.blocks[source.index()].function != program.blocks[clone.index()].function)
    {
        return null;
    }
    var reversed: std.ArrayList(CloneLineageStep) = .empty;
    // A malformed or incomplete lineage returns null after collecting
    // partial steps; unconditional cleanup covers that path as well as OOM.
    defer reversed.deinit(allocator);
    const visited = try allocator.alloc(bool, program.blocks.len);
    defer allocator.free(visited);
    @memset(visited, false);
    var current = clone;
    while (current != source) {
        if (current.index() >= visited.len or visited[current.index()]) return null;
        visited[current.index()] = true;
        if (index) |cached| if (cached.isMalformed(current)) return null;
        const step = cloneStepForTargetCached(program, current, index) orelse return null;
        try reversed.append(allocator, step);
        current = step.source;
    }
    std.mem.reverse(CloneLineageStep, reversed.items);
    return try reversed.toOwnedSlice(allocator);
}

fn blockLineageContainsCached(
    program: *const ir.Program,
    descendant: ir.BlockId,
    ancestor: ir.BlockId,
    index: ?*const CloneLineageIndex,
) bool {
    if (descendant.index() >= program.blocks.len or ancestor.index() >= program.blocks.len) return false;
    if (program.blocks[descendant.index()].function != program.blocks[ancestor.index()].function) return false;
    var current = descendant;
    var steps: usize = 0;
    while (steps <= program.blocks.len) : (steps += 1) {
        if (current == ancestor) return true;
        if (index) |cached| if (cached.isMalformed(current)) return false;
        const step = cloneStepForTargetCached(program, current, index) orelse return false;
        current = step.source;
    }
    return false;
}

fn hasIncomingCloneBridgeCached(
    program: *const ir.Program,
    reference: ir.CfgEdgeRef,
    candidate: ir.BlockId,
    index: ?*const CloneLineageIndex,
) bool {
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.rule != .node_split or rewrite.to.target.index() >= program.blocks.len or
            rewrite.source != reference.source or
            rewrite.to.target != candidate and
                !blockLineageContainsCached(program, candidate, rewrite.to.target, index))
        {
            continue;
        }
        if (!nodeSplitRewriteArgumentsAreStable(program, rewrite)) continue;
        const bridge_step = cloneStepForTargetCached(program, rewrite.to.target, index) orelse continue;
        if (bridge_step.source == rewrite.from.target and bridge_step.group == rewrite.node_split_group) return true;
    }
    return false;
}

// Independently cloned source and target blocks can preserve one original
// edge without retaining a direct node-split record whose source is the live
// predecessor.  Authenticate that composition through the original root
// edge: both endpoint lineages must replay, the edge kind and root target
// must agree, and the complete argument/formal tuples must map through the
// corresponding clone lineages.  Reachability alone is deliberately not
// used as evidence here.
fn hasAuthenticatedComposedCloneBridgeAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    reference: ir.CfgEdgeRef,
    lineage_index: *const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!bool {
    if (!incomingEdgeIsCanonical(program, analysis, reference)) return false;
    const current_edge = cfg_edge.value(program, reference) orelse return false;
    const source_position = cloneLineagePositionCached(program, reference.source, lineage_index) orelse return false;
    const target_position = cloneLineagePositionCached(program, reference.target, lineage_index) orelse return false;
    if (source_position.depth == 0 or target_position.depth == 0) {
        return false;
    }
    if (try hasAuthenticatedOwnerComposedCloneBridgeAlloc(
        allocator,
        program,
        analysis,
        reference,
        lineage_index,
        replay_index,
        replay_cache,
    )) return true;

    // The source root may itself have been split after the original edge was
    // recorded.  In that case the live CFG deliberately exposes `to`, so
    // looking up the root edge by kind returns the rewritten target and loses
    // the edge that authenticated this cross-root composition.  Prefer the
    // unique active rewrite's `from` edge, while retaining the live-edge path
    // for an unchanged root.
    var root_reference: ir.CfgEdgeRef = undefined;
    var root_edge: ir.Edge = undefined;
    var found_root_rewrite = false;
    const source_step = cloneStepForTargetCached(program, reference.source, lineage_index) orelse return false;
    for (program.edge_rewrites) |rewrite| {
        const same_clone_edge = rewrite.rule == .node_split and
            rewrite.kind == reference.kind and
            rewrite.from.target == target_position.root and
            rewrite.to.target == reference.target;
        if (!same_clone_edge) continue;
        if (rewrite.source != source_position.root and
            rewrite.source != source_step.source and
            rewrite.source != reference.source and
            activeNodeSplitRewrite(program, rewrite))
        {
            // A live edge from an unrelated owner cannot stand in for the
            // parent edge that establishes this clone's lineage.
            return false;
        }
        if (rewrite.rule != .node_split or
            rewrite.source != source_position.root or
            rewrite.kind != reference.kind or
            rewrite.from.target != target_position.root or
            rewrite.to.target != reference.target)
        {
            continue;
        }
        if (found_root_rewrite or
            !nodeSplitRewriteArgumentsAreStable(program, rewrite) or
            !activeNodeSplitRewrite(program, rewrite))
        {
            return false;
        }
        const rewrite_source = program.blocks[rewrite.source.index()];
        const rewrite_from = program.blocks[rewrite.from.target.index()];
        const rewrite_to = program.blocks[rewrite.to.target.index()];
        if (rewrite_source.id != rewrite.source or
            rewrite_from.id != rewrite.from.target or
            rewrite_to.id != rewrite.to.target or
            rewrite_source.function != rewrite_from.function or
            rewrite_from.function != rewrite_to.function or
            rewrite.from.arguments.len != rewrite_from.parameters.len or
            rewrite.to.arguments.len != rewrite_to.parameters.len)
        {
            return false;
        }
        root_reference = .{
            .source = rewrite.source,
            .kind = rewrite.kind,
            .target = rewrite.from.target,
        };
        root_edge = rewrite.from;
        found_root_rewrite = true;
    }
    if (!found_root_rewrite) {
        root_reference = edgeReferenceForKind(program, source_position.root, reference.kind) orelse return false;
        if (root_reference.kind != reference.kind or root_reference.target != target_position.root or
            !incomingEdgeIsCanonical(program, analysis, root_reference))
        {
            return false;
        }
        root_edge = cfg_edge.value(program, root_reference) orelse return false;
    }
    const source_lineage_valid = cloneLineageArgumentsAreStableCached(
        program,
        reference.source,
        lineage_index,
    ) and cloneLineageArgumentsAreStableCached(program, reference.target, lineage_index);
    const source_replay_valid = try cloneLineageArgumentsMatchReplayCached(
        allocator,
        program,
        source_position.root,
        reference.source,
        lineage_index,
        replay_index,
        replay_cache,
    );
    const target_replay_valid = try cloneLineageArgumentsMatchReplayCached(
        allocator,
        program,
        target_position.root,
        reference.target,
        lineage_index,
        replay_index,
        replay_cache,
    );
    if (!source_lineage_valid or !source_replay_valid or !target_replay_valid) {
        return false;
    }

    // The current edge cannot authenticate its own replay mapping: a changed
    // live tuple would otherwise be learned as the clone's new external use.
    // Require the candidate source to own the exact target-clone rewrite and
    // compare the live edge with that persisted rewrite before projecting any
    // parent arguments.
    const target_step = cloneStepForTargetCached(program, reference.target, lineage_index) orelse return false;
    var found_composed_edge = false;
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.rule != .node_split or
            rewrite.source != reference.source or
            rewrite.kind != reference.kind or
            rewrite.from.target != target_position.root or
            rewrite.to.target != reference.target or
            rewrite.node_split_group != target_step.group)
        {
            continue;
        }
        if (found_composed_edge or
            !nodeSplitRewriteArgumentsAreStable(program, rewrite) or
            !activeNodeSplitRewrite(program, rewrite))
        {
            return false;
        }
        const rewrite_replay_valid = if (replay_cache) |cache| blk: {
            const replay = (try cache.get(target_step.source, target_step.clone, target_step.group)) orelse break :blk false;
            break :blk nodeSplitRewriteArgumentsMatchReplay(program, rewrite, replay.*);
        } else blk: {
            const index = replay_index orelse break :blk false;
            var replay = (try node_split.replayMappingsForCloneAllocWithIndex(
                allocator,
                program,
                index,
                target_step.source,
                target_step.clone,
                target_step.group,
            )) orelse break :blk false;
            defer replay.deinit();
            break :blk nodeSplitRewriteArgumentsMatchReplay(program, rewrite, replay);
        };
        if (!rewrite_replay_valid) return false;
        if (current_edge.target != rewrite.to.target or
            !std.mem.eql(ir.ValueId, current_edge.arguments, rewrite.to.arguments))
        {
            return false;
        }
        found_composed_edge = true;
    }
    if (!found_composed_edge) return false;

    if (root_edge.arguments.len != current_edge.arguments.len) return false;
    for (root_edge.arguments, current_edge.arguments) |root_value, current_value| {
        const mapped = try mapValueThroughCloneLineageAllocCachedWithReplayCache(
            allocator,
            program,
            source_position.root,
            reference.source,
            root_value,
            lineage_index,
            replay_index,
            replay_cache,
        ) orelse return false;
        if (mapped != current_value) return false;
    }

    const root_target = program.blocks[target_position.root.index()];
    const current_target = program.blocks[reference.target.index()];
    if (root_target.id != target_position.root or current_target.id != reference.target or
        root_target.parameters.len != current_target.parameters.len)
    {
        return false;
    }
    for (root_target.parameters, current_target.parameters) |root_formal, current_formal| {
        const mapped = try mapValueThroughCloneLineageAllocCachedWithReplayCache(
            allocator,
            program,
            target_position.root,
            reference.target,
            root_formal,
            lineage_index,
            replay_index,
            replay_cache,
        ) orelse return false;
        if (mapped != current_formal) return false;
    }
    return true;
}

// A cloned source continuation can carry an edge whose target clone was
// authenticated by a different split group.  The durable owner is the
// source/target parent pair recorded by that target rewrite, not the current
// cloned source block.  Require the parent-owned rewrite and its stable tuple
// before accepting the live handoff.
fn hasAuthenticatedOwnerComposedCloneBridgeAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    reference: ir.CfgEdgeRef,
    lineage_index: *const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!bool {
    if (!incomingEdgeIsCanonical(program, analysis, reference)) return false;
    const current_edge = cfg_edge.value(program, reference) orelse return false;
    const source_step = cloneStepForTargetCached(program, reference.source, lineage_index) orelse return false;
    const target_step = cloneStepForTargetCached(program, reference.target, lineage_index) orelse return false;
    if (source_step.clone != reference.source or target_step.clone != reference.target or
        source_step.source == reference.source or target_step.source == reference.target)
    {
        return false;
    }
    if (!try cloneLineageArgumentsMatchReplayCached(
        allocator,
        program,
        source_step.source,
        reference.source,
        lineage_index,
        replay_index,
        replay_cache,
    ) or !try cloneLineageArgumentsMatchReplayCached(
        allocator,
        program,
        target_step.source,
        reference.target,
        lineage_index,
        replay_index,
        replay_cache,
    )) return false;

    var found = false;
    for (program.edge_rewrites) |rewrite| {
        const source_boundary = rewrite.source == source_step.source;
        if (rewrite.rule != .node_split or
            !source_boundary or
            rewrite.kind != reference.kind or
            rewrite.from.target != target_step.source or
            rewrite.to.target != reference.target or
            rewrite.node_split_group != target_step.group)
        {
            continue;
        }
        if (found or
            !nodeSplitRewriteArgumentsAreStable(program, rewrite) or
            !activeNodeSplitRewrite(program, rewrite))
        {
            return false;
        }
        const rewrite_replay_valid = if (replay_cache) |cache| blk: {
            const replay = (try cache.get(target_step.source, target_step.clone, target_step.group)) orelse break :blk false;
            break :blk nodeSplitRewriteArgumentsMatchReplay(program, rewrite, replay.*);
        } else blk: {
            const index = replay_index orelse break :blk false;
            var replay = (try node_split.replayMappingsForCloneAllocWithIndex(
                allocator,
                program,
                index,
                target_step.source,
                target_step.clone,
                target_step.group,
            )) orelse break :blk false;
            defer replay.deinit();
            break :blk nodeSplitRewriteArgumentsMatchReplay(program, rewrite, replay);
        };
        if (!rewrite_replay_valid or
            current_edge.target != rewrite.to.target or
            current_edge.arguments.len != rewrite.to.arguments.len)
        {
            return false;
        }
        for (rewrite.to.arguments, current_edge.arguments) |owner_value, current_value| {
            if (!ownerTupleReplayValueOriginIsCompatible(program, owner_value, current_value)) return false;
            const mapped = try mapValueThroughCloneLineageAllocCachedWithReplayCache(
                allocator,
                program,
                source_step.source,
                reference.source,
                owner_value,
                lineage_index,
                replay_index,
                replay_cache,
            ) orelse return false;
            if (mapped != current_value) return false;
        }
        found = true;
    }
    return found;
}

fn cloneContextMatchesIncomingWithReplayCached(
    allocator: ?std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    candidate: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!bool {
    if (candidate.index() >= program.blocks.len or incoming.len == 0) return false;
    const candidate_block = program.blocks[candidate.index()];
    if (candidate_block.id != candidate) return false;
    if (!cloneLineageArgumentsAreStableCached(program, candidate, index)) return false;
    const candidate_position = cloneLineagePositionCached(program, candidate, index) orelse return false;
    for (incoming) |reference| {
        if (!incomingEdgeIsCanonical(program, analysis, reference)) return false;
        if (!cloneLineageArgumentsAreStableCached(program, reference.source, index)) return false;
        const incoming_position = cloneLineagePositionCached(program, reference.source, index) orelse return false;
        // CFG reachability is not an authentication channel. A loop can make
        // unrelated clone roots mutually reachable while carrying different
        // replay mappings into the same continuation. A separate root is only
        // valid when either the incoming source records an explicit node-split
        // bridge or replay-aware root composition proves the corresponding
        // original edge.
        if (candidate_position.root != incoming_position.root) {
            if (!hasIncomingCloneBridgeCached(program, reference, candidate, index)) {
                const proof_allocator = allocator orelse return false;
                if (!try hasAuthenticatedComposedCloneBridgeAlloc(
                    proof_allocator,
                    program,
                    analysis,
                    reference,
                    index orelse return false,
                    replay_index,
                    replay_cache,
                )) return false;
            }
        } else if (!blockLineageContainsCached(program, reference.source, candidate, index) and
            !blockLineageContainsCached(program, candidate, reference.source, index)) return false;
        if (blockLineageContainsCached(program, reference.source, candidate, index)) continue;
        if (!cloneLineagesCompatibleCached(program, reference.source, candidate, index)) return false;
        if (analysis.blockIndex(reference.source) == null or analysis.blockIndex(candidate) == null) return false;
        if (!try analysis.canReach(reference.source, candidate)) return false;
        if (!try analysis.canReach(candidate, reference.target)) return false;
    }
    return true;
}

fn cloneContextRankCached(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    candidate: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!u8 {
    const normalized = try normalizeIncomingThroughForwardingAlloc(allocator, program, analysis, incoming);
    defer allocator.free(normalized);
    if (!try cloneContextMatchesIncomingWithReplayCached(
        allocator,
        program,
        analysis,
        candidate,
        normalized,
        index,
        replay_index,
        replay_cache,
    )) return 0;

    var same_group = cloneStepForTargetCached(program, candidate, index) != null;
    if (same_group) {
        const candidate_step = cloneStepForTargetCached(program, candidate, index).?;
        for (normalized) |reference| {
            const incoming_step = cloneStepForTargetCached(program, reference.source, index) orelse {
                same_group = false;
                break;
            };
            if (incoming_step.group != candidate_step.group) {
                same_group = false;
                break;
            }
        }
    }
    return if (same_group) 2 else 1;
}

fn mapValueThroughCloneLineageAllocCachedWithReplayCache(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.BlockId,
    clone: ir.BlockId,
    value: ir.ValueId,
    index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!?ir.ValueId {
    const lineage = try cloneLineageAllocCached(allocator, program, source, clone, index) orelse return null;
    defer allocator.free(lineage);
    var current = value;
    for (lineage) |step| {
        const mapped = if (replay_cache) |cache| blk: {
            const replay = (try cache.get(step.source, step.clone, step.group)) orelse return null;
            break :blk mapValueFromReplay(program, step.source, step.clone, current, replay.*);
        } else blk: {
            var replay = if (replay_index) |cached|
                (try node_split.replayMappingsForCloneAllocWithIndex(allocator, program, cached, step.source, step.clone, step.group)) orelse return null
            else
                (try node_split.replayMappingsForCloneAlloc(allocator, program, step.source, step.clone, step.group)) orelse return null;
            defer replay.deinit();
            break :blk mapValueFromReplay(program, step.source, step.clone, current, replay);
        };
        current = mapped orelse return null;
    }
    return current;
}

fn nodeSplitRewriteArgumentsMatchReplay(
    program: *const ir.Program,
    rewrite: ir.CfgEdgeRewrite,
    replay: node_split.ReplayMappings,
) bool {
    if (rewrite.rule != .node_split or rewrite.from.target.index() >= program.blocks.len or
        rewrite.to.target.index() >= program.blocks.len)
    {
        return false;
    }
    const source = program.blocks[rewrite.from.target.index()];
    const clone = program.blocks[rewrite.to.target.index()];
    if (source.id != rewrite.from.target or clone.id != rewrite.to.target or
        source.function != clone.function or
        rewrite.from.arguments.len != source.parameters.len or
        rewrite.to.arguments.len != clone.parameters.len or
        rewrite.from.arguments.len != rewrite.to.arguments.len)
    {
        return false;
    }
    for (rewrite.from.arguments, rewrite.to.arguments) |from, to| {
        if (from == to) continue;
        const mapped = mapValueFromReplay(program, source.id, clone.id, from, replay) orelse return false;
        if (mapped != to) return false;
    }
    return true;
}

// Replay entries may include external uses discovered while inspecting an
// edge.  Owner-tuple authentication cannot allow that inspection to invent a
// value of a different origin class; function parameters in particular are
// shared identities and may never be renamed by a block clone.
fn ownerTupleReplayValueOriginIsCompatible(
    program: *const ir.Program,
    source: ir.ValueId,
    mapped: ir.ValueId,
) bool {
    if (source == mapped) return true;
    if (source.index() >= program.values.len or mapped.index() >= program.values.len) return false;
    const source_value = program.values[source.index()];
    const mapped_value = program.values[mapped.index()];
    if (source_value.id != source or mapped_value.id != mapped or
        source_value.function != mapped_value.function)
    {
        return false;
    }
    return switch (source_value.origin) {
        .parameter => false,
        .block_parameter => switch (mapped_value.origin) {
            .block_parameter => true,
            else => false,
        },
        .instruction_result => switch (mapped_value.origin) {
            .instruction_result => true,
            else => false,
        },
        .capture => switch (mapped_value.origin) {
            .capture => true,
            else => false,
        },
    };
}

fn cloneLineageArgumentsMatchReplayCached(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    producer: ir.BlockId,
    clone: ir.BlockId,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!bool {
    const lineage = try cloneLineageAllocCached(allocator, program, producer, clone, lineage_index) orelse return false;
    defer allocator.free(lineage);
    for (lineage) |step| {
        var found_step = false;
        for (program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.from.target != step.source or
                rewrite.to.target != step.clone or rewrite.node_split_group != step.group)
            {
                continue;
            }
            found_step = true;
            const matches = if (replay_cache) |cache| blk: {
                const replay = (try cache.get(step.source, step.clone, step.group)) orelse break :blk false;
                break :blk nodeSplitRewriteArgumentsMatchReplay(program, rewrite, replay.*);
            } else blk: {
                var replay = if (replay_index) |cached|
                    (try node_split.replayMappingsForCloneAllocWithIndex(
                        allocator,
                        program,
                        cached,
                        step.source,
                        step.clone,
                        step.group,
                    )) orelse break :blk false
                else
                    (try node_split.replayMappingsForCloneAlloc(
                        allocator,
                        program,
                        step.source,
                        step.clone,
                        step.group,
                    )) orelse break :blk false;
                defer replay.deinit();
                break :blk nodeSplitRewriteArgumentsMatchReplay(program, rewrite, replay);
            };
            if (!matches) return false;
        }
        if (!found_step) return false;
    }
    return true;
}

// A cloned continuation may enter through a clone of the value's producer.
// In that shape the producer clone is the incoming edge target, while the
// predecessor is only a carrier of the corresponding edge argument.  Project
// the block-parameter slot through the authenticated target lineage and read
// the value from the live edge; reachability or same-type substitution is not
// sufficient.
fn findIncomingTargetCloneBlockParameterMappingAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    producer: ir.BlockId,
    source_value: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!ContextualMapping {
    var result = ContextualMapping{};
    if (incoming.len == 0 or source_value.index() >= program.values.len) return result;

    const value = program.values[source_value.index()];
    const parameter_index: usize = switch (value.origin) {
        .block_parameter => |origin| if (origin.block == producer) @intCast(origin.index) else return result,
        .parameter, .capture, .instruction_result => return result,
    };

    for (incoming) |reference| {
        const canonical = incomingEdgeIsCanonical(program, analysis, reference);
        if (!canonical or
            reference.target.index() >= program.blocks.len)
        {
            continue;
        }
        const target_block = program.blocks[reference.target.index()];
        if (target_block.id != reference.target or
            target_block.function != analysis.function.id or
            parameter_index >= target_block.parameters.len)
        {
            continue;
        }

        // Most incoming targets are ordinary continuation blocks.  Reject
        // those before allocating a lineage slice or replaying clone history;
        // the expensive proof below is only meaningful for a descendant of
        // this producer.
        if (lineage_index) |index| {
            const contains = blockLineageContainsCached(program, reference.target, producer, index);
            if (!contains) continue;
        }

        const lineage = try cloneLineageAllocCached(
            allocator,
            program,
            producer,
            reference.target,
            lineage_index,
        ) orelse continue;
        defer allocator.free(lineage);
        if (lineage.len == 0) continue;

        const replay_valid = if (replay_index != null or replay_cache != null)
            try cloneLineageArgumentsMatchReplayCached(
                allocator,
                program,
                producer,
                reference.target,
                lineage_index,
                replay_index,
                replay_cache,
            )
        else
            cloneLineageArgumentsAreStableCached(program, reference.target, lineage_index);
        const context_match = try cloneContextMatchesIncomingWithReplayCached(
            allocator,
            program,
            analysis,
            reference.target,
            &.{reference},
            lineage_index,
            replay_index,
            replay_cache,
        );
        if (!replay_valid or
            !node_split.parametersAreCanonical(program.values, target_block) or
            !context_match) continue;

        const mapped_formal = mapValueThroughCloneLineageAllocCachedWithReplayCache(
            allocator,
            program,
            producer,
            reference.target,
            source_value,
            lineage_index,
            replay_index,
            replay_cache,
        ) catch |err| return err;
        if (mapped_formal == null or mapped_formal.? != target_block.parameters[parameter_index]) continue;

        const edge = cfg_edge.value(program, reference) orelse continue;
        if (edge.arguments.len != target_block.parameters.len or
            !continuationParameterAcceptsValueType(
                program,
                target_block.parameters[parameter_index],
                edge.arguments[parameter_index],
            )) continue;

        const mapped = edge.arguments[parameter_index];
        if (result.value) |existing| {
            if (existing != mapped) result.ambiguous = true;
        } else {
            result.value = mapped;
        }
    }
    return result;
}

fn findIncomingCloneLineageValueMappingAllocWithReplayCache(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    producer: ir.BlockId,
    source_value: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!ContextualMapping {
    var result = ContextualMapping{};
    if (incoming.len == 0) return result;

    const normalized = try normalizeIncomingThroughForwardingAlloc(allocator, program, analysis, incoming);
    defer allocator.free(normalized);
    for (incoming, normalized) |reference, ownership_reference| {
        if (!incomingEdgeIsCanonical(program, analysis, reference)) continue;
        const arguments_match = if (replay_index != null or replay_cache != null)
            try cloneLineageArgumentsMatchReplayCached(
                allocator,
                program,
                producer,
                ownership_reference.source,
                lineage_index,
                replay_index,
                replay_cache,
            )
        else
            cloneLineageArgumentsAreStableCached(program, ownership_reference.source, lineage_index);
        if (!arguments_match) continue;
        const lineage = try cloneLineageAllocCached(
            allocator,
            program,
            producer,
            ownership_reference.source,
            lineage_index,
        ) orelse continue;
        const has_clone_context = lineage.len != 0;
        allocator.free(lineage);
        if (!has_clone_context) continue;

        const mapped = try mapValueThroughCloneLineageAllocCachedWithReplayCache(
            allocator,
            program,
            producer,
            ownership_reference.source,
            source_value,
            lineage_index,
            replay_index,
            replay_cache,
        ) orelse continue;
        const edge = cfg_edge.value(program, reference) orelse continue;
        var carried = false;
        for (edge.arguments) |argument| {
            if (argument == mapped) {
                carried = true;
                break;
            }
        }
        if (!carried) continue;

        if (result.value) |existing| {
            if (existing != mapped) result.ambiguous = true;
        } else {
            result.value = mapped;
        }
    }
    return result;
}

fn cloneCandidateIsMoreSpecificCached(
    program: *const ir.Program,
    candidate: ir.BlockId,
    existing: ir.BlockId,
    index: ?*const CloneLineageIndex,
) ?bool {
    if (candidate == existing) return false;
    if (blockLineageContainsCached(program, candidate, existing, index)) return true;
    if (blockLineageContainsCached(program, existing, candidate, index)) return false;
    return null;
}

fn uniquePredecessorEdgeToBlock(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    target: ir.BlockId,
) ?ir.CfgEdgeRef {
    if (target.index() >= program.blocks.len or analysis.blockIndex(target) == null or
        !analysis.isReachable(target) or analysis.predecessorCount(target) != 1)
    {
        return null;
    }
    const source = analysis.predecessorAt(target, 0) orelse return null;
    if (source.index() >= program.blocks.len or !analysis.isReachable(source)) return null;
    const block = program.blocks[source.index()];
    if (block.id != source or block.function != analysis.function.id) return null;
    return switch (block.terminator) {
        .jump => |edge| if (edge.target == target)
            .{ .source = source, .kind = .jump, .target = target }
        else
            null,
        .branch => |branch| if (branch.then_edge.target == target)
            .{ .source = source, .kind = .branch_then, .target = target }
        else if (branch.else_edge.target == target)
            .{ .source = source, .kind = .branch_else, .target = target }
        else
            null,
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => null,
    };
}

fn isTransparentForwardingBlock(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    block_id: ir.BlockId,
) bool {
    if (block_id.index() >= program.blocks.len or analysis.blockIndex(block_id) == null or
        !analysis.isReachable(block_id))
    {
        return false;
    }
    const block = program.blocks[block_id.index()];
    return block.id == block_id and block.function == analysis.function.id and
        block.parameters.len == 0 and block.instructions.len == 0 and
        switch (block.terminator) {
            .jump => |edge| edge.arguments.len == 0 and
                edge.target.index() < program.blocks.len and
                analysis.blockIndex(edge.target) != null and
                program.blocks[edge.target.index()].function == block.function,
            .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => false,
        };
}

// Context authentication may enter a shared continuation through a short
// chain of transparent blocks. Collapse only that chain: every hop has one
// reachable predecessor, no parameters, no instructions, and a canonical
// jump. This preserves the edge's proof boundary without treating arbitrary
// reachability as clone provenance.
fn normalizeIncomingThroughForwardingAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    incoming: []const ir.CfgEdgeRef,
) std.mem.Allocator.Error![]ir.CfgEdgeRef {
    const normalized = try allocator.alloc(ir.CfgEdgeRef, incoming.len);
    errdefer allocator.free(normalized);
    for (incoming, normalized) |reference, *out| {
        var current = reference.source;
        var selected = reference;
        var steps: usize = 0;
        while (isTransparentForwardingBlock(program, analysis, current)) {
            if (steps >= analysis.function.blocks.len) break;
            const predecessor = uniquePredecessorEdgeToBlock(program, analysis, current) orelse break;
            selected = predecessor;
            current = predecessor.source;
            steps += 1;
        }
        out.* = selected;
    }
    return normalized;
}

const IterationTransitionResult = struct {
    instruction: ir.Instruction,
    block: ir.BlockId,
    index: usize,
};

fn iterationTransitionResult(
    program: *const ir.Program,
    value_id: ir.ValueId,
) ?IterationTransitionResult {
    if (value_id.index() >= program.values.len) return null;
    const origin = switch (program.values[value_id.index()].origin) {
        .instruction_result => |value| value,
        .parameter, .capture, .block_parameter => return null,
    };
    if (origin.instruction.index() >= program.instructions.len) return null;
    const instruction = program.instructions[origin.instruction.index()];
    if (instruction.id != origin.instruction or origin.index >= instruction.results.len or
        instruction.results[origin.index] != value_id or instruction.block.index() >= program.blocks.len)
    {
        return null;
    }
    switch (instruction.operation) {
        .numeric_for_next => if (instruction.results.len != 4) return null,
        .generic_for_next => |operation| if (instruction.results.len != @as(usize, operation.variable_count) + 3) return null,
        else => return null,
    }
    const block = program.blocks[instruction.block.index()];
    if (block.id != instruction.block) return null;
    return .{ .instruction = instruction, .block = instruction.block, .index = origin.index };
}

fn sameIterationTransitionKind(
    left: ir.Instruction,
    right: ir.Instruction,
) bool {
    return switch (left.operation) {
        .numeric_for_next => |left_operation| switch (right.operation) {
            .numeric_for_next => |right_operation| left_operation.mode == right_operation.mode and
                left.results.len == right.results.len,
            else => false,
        },
        .generic_for_next => |left_operation| switch (right.operation) {
            .generic_for_next => |right_operation| left_operation.variable_count == right_operation.variable_count and
                left.results.len == right.results.len,
            else => false,
        },
        else => false,
    };
}

fn iterationStateArgumentIndex(
    instruction: ir.Instruction,
    result_index: usize,
) ?usize {
    return switch (instruction.operation) {
        .numeric_for_next => switch (result_index) {
            1 => 1,
            2 => 2,
            3 => 0,
            else => null,
        },
        .generic_for_next => switch (result_index) {
            1 => 0,
            2 => 1,
            3 => 2,
            else => null,
        },
        else => null,
    };
}

fn iterationTransitionInstructionAtBlock(
    program: *const ir.Program,
    block_id: ir.BlockId,
) ?ir.Instruction {
    if (block_id.index() >= program.blocks.len) return null;
    const block = program.blocks[block_id.index()];
    if (block.id != block_id or block.instructions.len != 1) return null;
    const instruction_id = block.instructions[0];
    if (instruction_id.index() >= program.instructions.len) return null;
    const instruction = program.instructions[instruction_id.index()];
    if (instruction.id != instruction_id or instruction.block != block_id) return null;
    return switch (instruction.operation) {
        .numeric_for_next, .generic_for_next => instruction,
        else => null,
    };
}

fn authenticatedIterationCloneReentryEdgeAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    transition: IterationTransitionResult,
    reference: ir.CfgEdgeRef,
    edge: ir.Edge,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    if (!incomingEdgeIsCanonical(program, analysis, reference) or
        !isIterationTransitionHeader(program, reference.target)) return false;
    const candidate_transition = iterationTransitionInstructionAtBlock(program, reference.target) orelse return false;
    if (!sameIterationTransitionKind(transition.instruction, candidate_transition)) return false;
    const position = cloneLineagePositionCached(program, reference.target, lineage_index) orelse return false;
    if (position.depth == 0 or position.root != transition.block) return false;
    if (!try cloneLineageArgumentsMatchReplayCached(
        allocator,
        program,
        transition.block,
        reference.target,
        lineage_index,
        replay_index,
        replay_cache,
    )) return false;

    for (program.edge_rewrites) |rewrite| {
        const group = rewrite.node_split_group orelse continue;
        if (rewrite.rule != .node_split or rewrite.source != reference.source or
            rewrite.kind != reference.kind or rewrite.from.target != transition.block or
            rewrite.to.target != reference.target or
            !std.mem.eql(ir.ValueId, rewrite.to.arguments, edge.arguments))
        {
            continue;
        }
        if (!activeNodeSplitRewrite(program, rewrite)) continue;
        const replay = (try replay_cache.get(
            rewrite.from.target,
            rewrite.to.target,
            group,
        )) orelse continue;
        if (!nodeSplitRewriteArgumentsMatchReplay(program, rewrite, replay.*)) continue;
        if (!try cloneLineageArgumentsMatchReplayCached(
            allocator,
            program,
            rewrite.from.target,
            rewrite.to.target,
            lineage_index,
            replay_index,
            replay_cache,
        )) continue;
        return true;
    }
    return false;
}

fn authenticatedIterationStateReentry(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    transition: IterationTransitionResult,
    allocator: std.mem.Allocator,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
    trace: bool,
    required_target: ?ir.BlockId,
) std.mem.Allocator.Error!bool {
    const consider = struct {
        fn edge(
            allocator_: std.mem.Allocator,
            program_: *const ir.Program,
            analysis_: *const cfg.Analysis,
            source_: ir.BlockId,
            kind_: ir.CfgEdgeKind,
            edge_: ir.Edge,
            transition_: IterationTransitionResult,
            lineage_index_: *const CloneLineageIndex,
            replay_index_: *const node_split.ReplayIndex,
            replay_cache_: *ReplayCache,
            trace_: bool,
            required_target_: ?ir.BlockId,
        ) std.mem.Allocator.Error!bool {
            if (required_target_) |target| if (edge_.target != target) return false;
            const shape_match = edge_.arguments.len == 4 and
                edge_.target.index() < program_.blocks.len and
                program_.blocks[edge_.target.index()].parameters.len == edge_.arguments.len and
                node_split.parametersAreCanonical(program_.values, program_.blocks[edge_.target.index()]);
            const state_match = shape_match and
                iteration_state.transitionStateMatches(program_, transition_.instruction, edge_.arguments);
            const reference: ir.CfgEdgeRef = .{ .source = source_, .kind = kind_, .target = edge_.target };
            const canonical = state_match and incomingEdgeIsCanonical(program_, analysis_, reference);
            const source_path = canonical and try analysis_.canReach(transition_.block, source_);
            const target_path = canonical and try analysis_.canReach(edge_.target, transition_.block);
            const clone_reentry = canonical and try authenticatedIterationCloneReentryEdgeAlloc(
                allocator_,
                program_,
                analysis_,
                transition_,
                reference,
                edge_,
                lineage_index_,
                replay_index_,
                replay_cache_,
            );
            if (trace_ and state_match) {
                std.debug.print("iteration_bridge_reentry_candidate transition_block={} source={} target={} canonical={} source_path={} target_path={} clone_reentry={}\\n", .{
                    transition_.block.index(),
                    source_.index(),
                    edge_.target.index(),
                    canonical,
                    source_path,
                    target_path,
                    clone_reentry,
                });
            }
            return canonical and ((source_path and target_path) or clone_reentry);
        }
    };

    for (analysis.function.blocks) |source| {
        if (!analysis.isReachable(source)) continue;
        switch (program.blocks[source.index()].terminator) {
            .jump => |edge| if (try consider.edge(
                allocator,
                program,
                analysis,
                source,
                .jump,
                edge,
                transition,
                lineage_index,
                replay_index,
                replay_cache,
                trace,
                required_target,
            )) return true,
            .branch => |branch| {
                if (try consider.edge(
                    allocator,
                    program,
                    analysis,
                    source,
                    .branch_then,
                    branch.then_edge,
                    transition,
                    lineage_index,
                    replay_index,
                    replay_cache,
                    trace,
                    required_target,
                )) return true;
                if (try consider.edge(
                    allocator,
                    program,
                    analysis,
                    source,
                    .branch_else,
                    branch.else_edge,
                    transition,
                    lineage_index,
                    replay_index,
                    replay_cache,
                    trace,
                    required_target,
                )) return true;
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }
    return false;
}

fn authenticatedIterationCandidate(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    candidate: IterationTransitionResult,
    reference: ir.CfgEdgeRef,
    edge: ir.Edge,
    source_transition: IterationTransitionResult,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
    trace: bool,
) std.mem.Allocator.Error!bool {
    const kind_match = sameIterationTransitionKind(source_transition.instruction, candidate.instruction);
    const result_match = candidate.index == source_transition.index;
    const header_match = isIterationTransitionHeader(program, candidate.block);
    const state_match = iteration_state.transitionStateMatches(program, candidate.instruction, edge.arguments);
    const edge_match = incomingEdgeIsCanonical(program, analysis, reference);
    const candidate_path = try analysis.canReach(candidate.block, reference.source);
    const source_path = try analysis.canReach(reference.source, source_transition.block);
    if (trace) {
        std.debug.print("iteration_bridge_candidate source_value={} source_block={} candidate_block={} incoming_source={} target={} kind={} result={} header={} state={} edge={} candidate_path={} source_path={}\\n", .{
            source_transition.instruction.results[source_transition.index].index(),
            source_transition.block.index(),
            candidate.block.index(),
            reference.source.index(),
            reference.target.index(),
            kind_match,
            result_match,
            header_match,
            state_match,
            edge_match,
            candidate_path,
            source_path,
        });
    }
    if (!kind_match or !result_match or !header_match or !state_match or !edge_match or
        !candidate_path or !source_path) return false;
    if (cloneLineagePositionCached(program, candidate.block, lineage_index)) |position| {
        if (position.depth != 0 and
            (!cloneLineageArgumentsAreStableCached(program, candidate.block, lineage_index) or
                !try cloneLineageArgumentsMatchReplayCached(
                    allocator,
                    program,
                    position.root,
                    candidate.block,
                    lineage_index,
                    replay_index,
                    replay_cache,
                )))
        {
            return false;
        }
    }
    return true;
}

// An iteration result can be carried through a parameterized continuation by
// its authenticated state slot even when the producer block is outside the
// clone lineage of the selected continuation. The source transition must have
// a real re-entry edge, and the selected edge must carry a matching transition
// tuple; result type alone is never sufficient.
fn findAuthenticatedIterationStateResultMappingAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source_value: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
    trace: bool,
) std.mem.Allocator.Error!ContextualMapping {
    var result = ContextualMapping{};
    const source_transition = iterationTransitionResult(program, source_value) orelse return result;
    const source_slot = iterationStateArgumentIndex(source_transition.instruction, source_transition.index) != null;
    const source_header = isIterationTransitionHeader(program, source_transition.block);
    const source_reentry = source_header and try authenticatedIterationStateReentry(
        program,
        analysis,
        source_transition,
        allocator,
        lineage_index,
        replay_index,
        replay_cache,
        trace,
        null,
    );
    if (trace) {
        std.debug.print("iteration_bridge_source value={} block={} slot={} header={} reentry={} incoming_count={}\\n", .{
            source_value.index(),
            source_transition.block.index(),
            source_slot,
            source_header,
            source_reentry,
            incoming.len,
        });
    }
    if (!source_slot or !source_header or !source_reentry) {
        return result;
    }

    for (incoming) |reference| {
        const edge = cfg_edge.value(program, reference) orelse return result;
        if (reference.target.index() >= program.blocks.len or
            program.blocks[reference.target.index()].parameters.len != edge.arguments.len or
            !node_split.parametersAreCanonical(program.values, program.blocks[reference.target.index()]))
        {
            return result;
        }
        var mapped: ?ir.ValueId = null;
        for (edge.arguments) |argument| {
            const candidate = iterationTransitionResult(program, argument) orelse continue;
            if (iterationStateArgumentIndex(candidate.instruction, candidate.index) == null or
                !try authenticatedIterationCandidate(
                    allocator,
                    program,
                    analysis,
                    candidate,
                    reference,
                    edge,
                    source_transition,
                    lineage_index,
                    replay_index,
                    replay_cache,
                    trace,
                ))
            {
                continue;
            }
            if (mapped) |existing| {
                if (existing != argument) return .{ .ambiguous = true };
            } else {
                mapped = argument;
            }
        }
        const selected = mapped orelse return result;
        if (result.value) |existing| {
            if (existing != selected) return .{ .ambiguous = true };
        } else {
            result.value = selected;
        }
    }
    return result;
}

fn findExistingValueCloneAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    producer: ir.BlockId,
    source_value: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    closure: []const ir.BlockId,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!?ir.ValueId {
    const trace_external_mapping = trace_structural_phases and closure.len >= 30;
    if (lineage_index) |lineage| if (replay_cache) |cache| {
        const iteration_context = try findAuthenticatedIterationStateResultMappingAlloc(
            allocator,
            program,
            analysis,
            source_value,
            incoming,
            lineage,
            replay_index,
            cache,
            trace_external_mapping,
        );
        if (trace_external_mapping) {
            std.debug.print("external_mapping_lookup value={} producer={} path=iteration_state result={any}\n", .{
                source_value.index(),
                producer.index(),
                iteration_context,
            });
        }
        if (iteration_context.ambiguous) return null;
        if (iteration_context.value) |mapped| return mapped;
    };
    const incoming_context = try findIncomingCloneLineageValueMappingAllocWithReplayCache(
        allocator,
        program,
        analysis,
        producer,
        source_value,
        incoming,
        lineage_index,
        replay_index,
        replay_cache,
    );
    if (trace_external_mapping) {
        std.debug.print("external_mapping_lookup value={} producer={} path=incoming_lineage result={any}\n", .{
            source_value.index(),
            producer.index(),
            incoming_context,
        });
    }
    if (incoming_context.ambiguous) return null;
    if (incoming_context.value) |mapped| return mapped;

    const carried_context = try findCarriedLineageValueMappingAlloc(
        allocator,
        program,
        analysis,
        source_value,
        incoming,
        lineage_index,
        replay_index,
        replay_cache,
        trace_external_mapping,
    );
    if (trace_external_mapping) {
        std.debug.print("external_mapping_carried value={} producer={} context={any}\n", .{
            source_value.index(),
            producer.index(),
            carried_context,
        });
        std.debug.print("external_mapping_lookup value={} producer={} path=carried_lineage result={any}\n", .{
            source_value.index(),
            producer.index(),
            carried_context,
        });
    }
    if (carried_context.ambiguous) return null;
    if (carried_context.value) |mapped| return mapped;

    const group_context = try findGroupContextValueMappingAlloc(
        allocator,
        program,
        analysis,
        source_value,
        incoming,
        lineage_index,
        replay_index,
        replay_cache,
    );
    if (trace_external_mapping) {
        std.debug.print("external_mapping_context value={} producer={} incoming={any} incoming_context={any} group_context={any}\n", .{
            source_value.index(),
            producer.index(),
            incoming,
            incoming_context,
            group_context,
        });
        std.debug.print("external_mapping_lookup value={} producer={} path=group_context result={any}\n", .{
            source_value.index(),
            producer.index(),
            group_context,
        });
    }
    if (group_context.ambiguous) return null;
    if (group_context.value) |mapped| return mapped;

    // A target clone whose formals carry the producer's block parameter is a
    // precise boundary mapping, but it is more expensive than the ordinary
    // incoming, carried, and group-context indexes above.  Keep it behind
    // those cheaper authenticated paths so large feedback closures do not
    // replay target lineage for every block-parameter use.
    const target_context = try findIncomingTargetCloneBlockParameterMappingAlloc(
        allocator,
        program,
        analysis,
        producer,
        source_value,
        incoming,
        lineage_index,
        replay_index,
        replay_cache,
    );
    if (trace_external_mapping) {
        std.debug.print("external_mapping_lookup value={} producer={} path=target_formal result={any}\n", .{
            source_value.index(),
            producer.index(),
            target_context,
        });
    }
    if (target_context.ambiguous) return null;
    if (target_context.value) |mapped| return mapped;

    var authenticated: ?ir.ValueId = null;
    var authenticated_candidate: ?ir.BlockId = null;
    var authenticated_rank: u8 = 0;
    var authenticated_ambiguous = false;
    var fallback: ?ir.ValueId = null;
    var fallback_ambiguous = false;
    for (replay_index.candidateCloneTargetsForSource(program, producer)) |candidate| {
        if (candidate == producer or analysis.blockIndex(candidate) == null or candidate.index() >= program.blocks.len) continue;
        if (!blockLineageContainsCached(program, candidate, producer, lineage_index)) continue;
        if (!try cloneLineageArgumentsMatchReplayCached(
            allocator,
            program,
            producer,
            candidate,
            lineage_index,
            replay_index,
            replay_cache,
        )) continue;
        const context_rank = try cloneContextRankCached(
            allocator,
            program,
            analysis,
            candidate,
            incoming,
            lineage_index,
            replay_index,
            replay_cache,
        );
        // A producer clone inside the closure is not available at the closure
        // boundary.  It may only remap an external use when that clone itself
        // dominates every incoming context, or when the incoming clone group
        // authenticates the same context explicitly above.
        const dominated = definitionDominatesIncoming(analysis, candidate, incoming);
        if (context_rank == 0 and !dominated) continue;
        const clone_value = try mapValueThroughCloneLineageAllocCachedWithReplayCache(
            allocator,
            program,
            producer,
            candidate,
            source_value,
            lineage_index,
            replay_index,
            replay_cache,
        ) orelse continue;
        if (trace_external_mapping) {
            std.debug.print("external_mapping_candidate value={} producer={} candidate={} context_rank={} clone_value={} dominated={}\n", .{
                source_value.index(),
                producer.index(),
                candidate.index(),
                context_rank,
                clone_value.index(),
                dominated,
            });
        }
        if (context_rank != 0) {
            const rank = context_rank;
            if (authenticated == null or rank > authenticated_rank) {
                authenticated = clone_value;
                authenticated_candidate = candidate;
                authenticated_rank = rank;
                authenticated_ambiguous = false;
            } else if (rank == authenticated_rank) {
                const existing = authenticated.?;
                if (existing != clone_value) {
                    const existing_candidate = authenticated_candidate orelse return null;
                    if (cloneCandidateIsMoreSpecificCached(program, candidate, existing_candidate, lineage_index)) |more_specific| {
                        if (more_specific) {
                            authenticated = clone_value;
                            authenticated_candidate = candidate;
                            // An earlier incomparable candidate remains an
                            // unresolved sibling even when this candidate is
                            // more specific than the current representative.
                        }
                    } else {
                        authenticated_ambiguous = true;
                    }
                }
            }
        } else if (fallback) |existing| {
            if (existing != clone_value) fallback_ambiguous = true;
        } else fallback = clone_value;
    }
    if (trace_external_mapping) {
        std.debug.print("external_mapping_lookup value={} producer={} path=ranked_clone authenticated={?} authenticated_ambiguous={} fallback={?} fallback_ambiguous={}\n", .{
            source_value.index(),
            producer.index(),
            authenticated,
            authenticated_ambiguous,
            fallback,
            fallback_ambiguous,
        });
    }
    if (authenticated) |mapped| return if (authenticated_ambiguous) null else mapped;
    return if (fallback_ambiguous) null else fallback;
}

fn mapValueFromReplay(
    program: *const ir.Program,
    source_block_id: ir.BlockId,
    clone_block_id: ir.BlockId,
    source_value_id: ir.ValueId,
    replay: node_split.ReplayMappings,
) ?ir.ValueId {
    // Definitions in the cloned block are structural evidence.  Prefer it
    // over use-derived replay entries so an edge cannot authenticate itself
    // by contributing a forged source/clone pair to the replay table.
    if (mapValueByCloneShape(program, source_block_id, clone_block_id, source_value_id)) |mapped| {
        return mapped;
    }
    for (replay.source_values, replay.clone_values) |source_value, clone_value| {
        if (source_value == source_value_id) return clone_value;
    }
    return null;
}

fn mapValueByCloneShape(
    program: *const ir.Program,
    source_block_id: ir.BlockId,
    clone_block_id: ir.BlockId,
    source_value_id: ir.ValueId,
) ?ir.ValueId {
    if (source_block_id.index() >= program.blocks.len or clone_block_id.index() >= program.blocks.len) return null;
    const source_block = program.blocks[source_block_id.index()];
    const clone_block = program.blocks[clone_block_id.index()];
    if (source_block.id != source_block_id or clone_block.id != clone_block_id or
        source_block.function != clone_block.function or source_value_id.index() >= program.values.len)
    {
        return null;
    }
    const source_value = program.values[source_value_id.index()];
    if (source_value.id != source_value_id or source_value.function != source_block.function) return null;
    return switch (source_value.origin) {
        .block_parameter => |origin| if (origin.block == source_block_id and origin.index < clone_block.parameters.len)
            clone_block.parameters[origin.index]
        else
            null,
        .instruction_result => |origin| mapInstructionResultClone(
            program,
            source_block,
            clone_block,
            source_value_id,
            origin.instruction,
            origin.index,
        ),
        .parameter, .capture => null,
    };
}

fn mapInstructionResultClone(
    program: *const ir.Program,
    source_block: ir.Block,
    clone_block: ir.Block,
    source_value_id: ir.ValueId,
    source_instruction_id: ir.InstructionId,
    result_index: u32,
) ?ir.ValueId {
    for (source_block.instructions, 0..) |source_id, instruction_index| {
        if (source_id != source_instruction_id or instruction_index >= clone_block.instructions.len) continue;
        if (source_id.index() >= program.instructions.len or clone_block.instructions[instruction_index].index() >= program.instructions.len) return null;
        const source_instruction = program.instructions[source_id.index()];
        const clone_instruction = program.instructions[clone_block.instructions[instruction_index].index()];
        const index: usize = @intCast(result_index);
        if (source_instruction.id != source_id or clone_instruction.id != clone_block.instructions[instruction_index] or
            index >= source_instruction.results.len or index >= clone_instruction.results.len or
            source_instruction.results[index] != source_value_id or
            clone_instruction.results[index].index() >= program.values.len)
        {
            return null;
        }
        const clone_value = program.values[clone_instruction.results[index].index()];
        if (clone_value.id != clone_instruction.results[index] or clone_value.function != clone_block.function) return null;
        return clone_instruction.results[index];
    }
    return null;
}

const DirectValueUseDetector = struct {
    target: ir.ValueId,
    found: bool = false,

    pub fn value(self: *DirectValueUseDetector, value_id: ir.ValueId) void {
        if (value_id == self.target) self.found = true;
    }

    pub fn pack(_: *DirectValueUseDetector, _: ir.ValuePackId) void {}
    pub fn place(_: *DirectValueUseDetector, _: ir.PlaceId) void {}
};

const ContextualMapping = struct {
    value: ?ir.ValueId = null,
    pack: ?ir.ValuePackId = null,
    ambiguous: bool = false,
};

// An instruction result may be produced by a loop header but carried by a
// descendant body edge before a shared continuation is entered.  The result
// is authentic only when the carrier is an ancestor in the selected clone
// lineage, every replay step validates, and the final mapped identity is on
// the incoming edge itself.
fn findCarriedLineageValueMappingAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source_value: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
    trace: bool,
) std.mem.Allocator.Error!ContextualMapping {
    var result = ContextualMapping{};
    if (incoming.len == 0) return result;

    const normalized = try normalizeIncomingThroughForwardingAlloc(allocator, program, analysis, incoming);
    defer allocator.free(normalized);
    for (incoming, normalized) |reference, ownership_reference| {
        if (!incomingEdgeIsCanonical(program, analysis, reference)) continue;
        const edge = cfg_edge.value(program, reference) orelse continue;
        var current = ownership_reference.source;
        var depth: usize = 0;
        while (true) {
            if (current.index() >= program.blocks.len or
                analysis.blockIndex(current) == null or
                program.blocks[current.index()].id != current or
                program.blocks[current.index()].function != analysis.function.id)
            {
                break;
            }

            const carrier = program.blocks[current.index()];
            var detector = DirectValueUseDetector{ .target = source_value };
            for (carrier.instructions) |instruction_id| {
                if (instruction_id.index() >= program.instructions.len) {
                    detector.found = true;
                    break;
                }
                const instruction = program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or instruction.block != current) {
                    detector.found = true;
                    break;
                }
                runtime_uses.visitOperationUses(instruction.operation, &detector);
                if (detector.found) break;
            }
            if (!detector.found) runtime_uses.visitTerminatorUses(carrier.terminator, &detector);

            if (trace) {
                std.debug.print("external_mapping_carrier_step incoming_source={} current={} depth={} direct_use={} edge_args={any}\n", .{
                    reference.source.index(),
                    current.index(),
                    depth,
                    detector.found,
                    edge.arguments,
                });
            }

            if (detector.found) {
                const replay_valid = try cloneLineageArgumentsMatchReplayCached(
                    allocator,
                    program,
                    current,
                    ownership_reference.source,
                    lineage_index,
                    replay_index,
                    replay_cache,
                );
                if (replay_valid) {
                    const mapped = try mapValueThroughCloneLineageAllocCachedWithReplayCache(
                        allocator,
                        program,
                        current,
                        ownership_reference.source,
                        source_value,
                        lineage_index,
                        replay_index,
                        replay_cache,
                    );
                    if (trace) {
                        std.debug.print("external_mapping_carrier_replay current={} replay_valid={} mapped={?d}\n", .{
                            current.index(),
                            replay_valid,
                            if (mapped) |candidate| candidate.index() else null,
                        });
                    }
                    if (mapped) |candidate| {
                        var carried = false;
                        for (edge.arguments) |argument| {
                            if (argument == candidate) {
                                carried = true;
                                break;
                            }
                        }
                        if (carried) {
                            if (result.value) |existing| {
                                if (existing != candidate) result.ambiguous = true;
                            } else {
                                result.value = candidate;
                            }
                        }
                    }
                }
            }

            const step = cloneStepForTargetCached(program, current, lineage_index) orelse break;
            if (trace) {
                std.debug.print("external_mapping_carrier_parent current={} parent={} group={}\n", .{
                    current.index(),
                    step.source.index(),
                    step.group.index(),
                });
            }
            current = step.source;
            depth += 1;
            if (depth > program.blocks.len) break;
        }
    }
    return result;
}

fn findGroupContextValueMappingAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source_value: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!ContextualMapping {
    var result = ContextualMapping{};
    if (incoming.len == 0) return result;
    const normalized = try normalizeIncomingThroughForwardingAlloc(allocator, program, analysis, incoming);
    defer allocator.free(normalized);
    for (normalized) |reference| {
        const incoming_step = cloneStepForTargetCached(program, reference.source, lineage_index) orelse continue;
        for (replay_index.nodeSplitRewriteIndicesForGroup(incoming_step.group)) |rewrite_index| {
            if (rewrite_index >= program.edge_rewrites.len) continue;
            const rewrite = program.edge_rewrites[rewrite_index];
            const source_id = rewrite.from.target;
            const clone_id = rewrite.to.target;
            if (source_id.index() >= program.blocks.len or clone_id.index() >= program.blocks.len or
                analysis.blockIndex(clone_id) == null or !try analysis.canReach(clone_id, reference.source)) continue;
            const source_block = program.blocks[source_id.index()];
            if (source_block.id != source_id) continue;
            var detector = DirectValueUseDetector{ .target = source_value };
            for (source_block.instructions) |instruction_id| {
                if (instruction_id.index() >= program.instructions.len) continue;
                runtime_uses.visitOperationUses(program.instructions[instruction_id.index()].operation, &detector);
            }
            runtime_uses.visitTerminatorUses(source_block.terminator, &detector);
            if (!detector.found) continue;
            const mapped = if (replay_cache) |cache| blk: {
                const replay = (try cache.get(source_id, clone_id, incoming_step.group)) orelse continue;
                if (!nodeSplitRewriteArgumentsMatchReplay(program, rewrite, replay.*)) continue;
                break :blk mapValueFromReplay(program, source_id, clone_id, source_value, replay.*);
            } else blk: {
                var replay = (try node_split.replayMappingsForCloneAllocWithIndex(
                    allocator,
                    program,
                    replay_index,
                    source_id,
                    clone_id,
                    incoming_step.group,
                )) orelse continue;
                defer replay.deinit();
                if (!nodeSplitRewriteArgumentsMatchReplay(program, rewrite, replay)) continue;
                break :blk mapValueFromReplay(program, source_id, clone_id, source_value, replay);
            };
            const mapped_value = mapped orelse continue;
            if (result.value) |existing| {
                if (existing != mapped_value) result.ambiguous = true;
            } else {
                result.value = mapped_value;
            }
        }
    }
    return result;
}

test "multi-result carrier maps through every authenticated clone step" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const bridge = ir.BlockId.fromIndex(1);
    const first_clone = ir.BlockId.fromIndex(2);
    const carrier = ir.BlockId.fromIndex(3);
    const second_clone = ir.BlockId.fromIndex(4);
    const continuation = ir.BlockId.fromIndex(5);
    const producer = ir.BlockId.fromIndex(6);

    const control = ir.ValueId.fromIndex(0);
    const limit = ir.ValueId.fromIndex(1);
    const step = ir.ValueId.fromIndex(2);
    const initial = ir.ValueId.fromIndex(3);
    const source_has = ir.ValueId.fromIndex(4);
    const source_limit = ir.ValueId.fromIndex(5);
    const source_step = ir.ValueId.fromIndex(6);
    const source_next = ir.ValueId.fromIndex(7);
    const first_has = ir.ValueId.fromIndex(8);
    const first_limit = ir.ValueId.fromIndex(9);
    const first_step = ir.ValueId.fromIndex(10);
    const first_next = ir.ValueId.fromIndex(11);
    const second_has = ir.ValueId.fromIndex(12);
    const second_limit = ir.ValueId.fromIndex(13);
    const second_step = ir.ValueId.fromIndex(14);
    const second_next = ir.ValueId.fromIndex(15);
    const continuation_has = ir.ValueId.fromIndex(16);
    const continuation_limit = ir.ValueId.fromIndex(17);
    const continuation_step = ir.ValueId.fromIndex(18);
    const continuation_next = ir.ValueId.fromIndex(19);
    const transition = ir.InstructionId.fromIndex(0);

    const function_parameters = [_]ir.ValueId{
        control,
        limit,
        step,
        initial,
        first_has,
        first_limit,
        first_step,
        first_next,
        second_has,
        second_limit,
        second_step,
        second_next,
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = bridge } } },
        .{ .id = bridge, .function = function_id, .terminator = .{ .jump = .{ .target = second_clone } } },
        .{ .id = first_clone, .function = function_id, .terminator = .{ .jump = .{ .target = continuation, .arguments = &.{ first_has, first_limit, first_step, first_next } } } },
        .{ .id = carrier, .function = function_id, .terminator = .{ .jump = .{ .target = continuation, .arguments = &.{ source_has, source_limit, source_step, source_next } } } },
        .{ .id = second_clone, .function = function_id, .terminator = .{ .jump = .{ .target = continuation, .arguments = &.{ second_has, second_limit, second_step, second_next } } } },
        .{ .id = continuation, .function = function_id, .parameters = &.{ continuation_has, continuation_limit, continuation_step, continuation_next }, .terminator = .{ .return_values = &.{} } },
        .{ .id = producer, .function = function_id, .instructions = &.{transition}, .terminator = .{ .jump = .{ .target = carrier } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = function_parameters[0..],
        .blocks = &.{ entry, bridge, first_clone, carrier, second_clone, continuation, producer },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = control, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = limit, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = step, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } },
        .{ .id = initial, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 3 } },
        .{ .id = source_has, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition, .index = 0 } } },
        .{ .id = source_limit, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition, .index = 1 } } },
        .{ .id = source_step, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition, .index = 2 } } },
        .{ .id = source_next, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition, .index = 3 } } },
        .{ .id = first_has, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 4 } },
        .{ .id = first_limit, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 5 } },
        .{ .id = first_step, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 6 } },
        .{ .id = first_next, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 7 } },
        .{ .id = second_has, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 8 } },
        .{ .id = second_limit, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 9 } },
        .{ .id = second_step, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 10 } },
        .{ .id = second_next, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 11 } },
        .{ .id = continuation_has, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = continuation, .index = 0 } } },
        .{ .id = continuation_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = continuation, .index = 1 } } },
        .{ .id = continuation_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = continuation, .index = 2 } } },
        .{ .id = continuation_next, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = continuation, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = transition,
        .block = producer,
        .operation = .{ .numeric_for_next = .{
            .control = control,
            .limit = limit,
            .step = step,
            .initial = initial,
            .mode = .semantic_normalized,
        } },
        .results = &.{ source_has, source_limit, source_step, source_next },
        .effects = .numeric_for_next,
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .jump,
            .from = .{ .target = carrier },
            .to = .{ .target = first_clone },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = bridge,
            .kind = .jump,
            .from = .{ .target = first_clone },
            .to = .{ .target = second_clone },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
    };
    var program: ir.Program = .{
        .program_id = "multi-result-carrier-lineage",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(std.testing.allocator, &program, &replay_index);
    defer replay_cache.deinit();

    const incoming = [_]ir.CfgEdgeRef{.{ .source = second_clone, .kind = .jump, .target = continuation }};
    const mapped = try findExistingValueCloneAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        producer,
        source_limit,
        &incoming,
        &.{continuation},
        &lineage_index,
        &replay_index,
        &replay_cache,
    );
    try std.testing.expect(mapped != null);
    try std.testing.expectEqual(second_limit, mapped.?);

    var tampered_blocks = blocks;
    tampered_blocks[second_clone.index()].terminator = .{ .jump = .{
        .target = continuation,
        .arguments = &.{ second_has, control, second_step, second_next },
    } };
    program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer tampered_analysis.deinit();
    var tampered_lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer tampered_lineage_index.deinit();
    var tampered_replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer tampered_replay_index.deinit();
    var tampered_replay_cache = ReplayCache.init(std.testing.allocator, &program, &tampered_replay_index);
    defer tampered_replay_cache.deinit();
    try std.testing.expect((try findExistingValueCloneAlloc(
        std.testing.allocator,
        &program,
        &tampered_analysis,
        producer,
        source_limit,
        &incoming,
        &.{continuation},
        &tampered_lineage_index,
        &tampered_replay_index,
        &tampered_replay_cache,
    )) == null);
}

pub fn isIterationTransitionHeader(program: *const ir.Program, block_id: ir.BlockId) bool {
    if (block_id.index() >= program.blocks.len) return false;
    const block = program.blocks[block_id.index()];
    if (block.id != block_id or block.instructions.len != 1 or block.parameters.len != 4) return false;
    const instruction_id = block.instructions[0];
    if (instruction_id.index() >= program.instructions.len) return false;
    const instruction = program.instructions[instruction_id.index()];
    if (instruction.id != instruction_id or instruction.block != block_id or instruction.results.len == 0) return false;
    const branch = switch (block.terminator) {
        .branch => |value| value,
        else => return false,
    };
    if (branch.condition != instruction.results[0]) return false;
    return switch (instruction.operation) {
        .numeric_for_next => |operation| instruction.results.len == 4 and
            operation.control == block.parameters[0] and
            operation.limit == block.parameters[1] and
            operation.step == block.parameters[2] and
            operation.initial == block.parameters[3],
        .generic_for_next => |operation| operation.variable_count != 0 and
            instruction.results.len == @as(usize, operation.variable_count) + 3 and
            operation.iterator == block.parameters[0] and
            operation.state == block.parameters[1] and
            operation.control == block.parameters[2] and
            operation.initial == block.parameters[3],
        else => false,
    };
}

const ContinuationValueContext = enum {
    available,
    contextual,
    unavailable,
};

const ContinuationValuePolicy = enum {
    ordinary,
    authenticated_parameter,
    incoming_parameter_bridge,
};

// A dynamic block formal is an open Luau parameter contract.  It can receive
// a concretely typed owner value or a dynamic value, while a concrete formal
// must not be matched by an unresolved dynamic value.
pub fn continuationParameterAcceptsValueType(
    program: *const ir.Program,
    formal: ir.ValueId,
    argument: ir.ValueId,
) bool {
    if (formal.index() >= program.values.len or argument.index() >= program.values.len) return false;
    const formal_value = program.values[formal.index()];
    const argument_value = program.values[argument.index()];
    if (formal_value.id != formal or argument_value.id != argument or
        formal_value.function != argument_value.function)
    {
        return false;
    }
    if (formal_value.type.kind == .dynamic) return true;
    if (argument_value.type.kind == .dynamic) return false;
    return formal_value.type.kind == argument_value.type.kind and
        formal_value.type.bit_width == argument_value.type.bit_width and
        formal_value.type.signed == argument_value.type.signed;
}
