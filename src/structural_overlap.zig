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

pub fn structuralPhaseNow() i96 {
    if (!trace_structural_phases) return 0;
    return Io.Clock.awake.now(Io.Threaded.global_single_threaded.io()).nanoseconds;
}

pub fn structuralPhaseMillis(start: i96) i64 {
    if (!trace_structural_phases) return 0;
    return @intCast(@divTrunc(structuralPhaseNow() - start, std.time.ns_per_ms));
}

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

pub fn collectExternalCloneMappingsAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
) std.mem.Allocator.Error!?ExternalCloneMappings {
    var lineage_index = try CloneLineageIndex.initForFunction(allocator, program, analysis.function.id);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.initForFunction(allocator, program, analysis.function.id);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(allocator, program, &replay_index);
    defer replay_cache.deinit();
    return collectExternalCloneMappingsAllocWithReplayState(
        allocator,
        program,
        analysis,
        closure,
        incoming,
        &lineage_index,
        &replay_index,
        &replay_cache,
    );
}

fn collectExternalCloneMappingsAllocWithReplayState(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!?ExternalCloneMappings {
    if (closure.len == 0 or incoming.len == 0) return null;
    var used_values: std.ArrayList(ir.ValueId) = .empty;
    defer used_values.deinit(allocator);
    var used_packs: std.ArrayList(ir.ValuePackId) = .empty;
    defer used_packs.deinit(allocator);
    const trace_mapping_failure = trace_structural_phases and closure.len >= 140 and incoming.len == 1;
    var out_of_memory = false;
    const collector = UseCollector{
        .allocator = allocator,
        .values = &used_values,
        .packs = &used_packs,
        .out_of_memory = &out_of_memory,
    };

    for (closure) |block_id| {
        if (block_id.index() >= program.blocks.len or analysis.blockIndex(block_id) == null) return null;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id or block.function != analysis.function.id) return null;
        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) return null;
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or instruction.block != block_id) return null;
            runtime_uses.visitOperationUses(instruction.operation, collector);
        }
        runtime_uses.visitTerminatorUses(block.terminator, collector);
    }
    if (out_of_memory) return error.OutOfMemory;

    if (trace_mapping_failure) {
        std.debug.print("external_mapping_begin closure={} incoming={any} used_values={any} used_packs={any}\n", .{
            closure.len,
            incoming,
            used_values.items,
            used_packs.items,
        });
    }

    for (incoming) |reference| {
        if (!incomingEdgeIsCanonical(program, analysis, reference) or
            !containsBlock(closure, reference.target)) return null;
    }

    var values: std.ArrayList(ir.ValueId) = .empty;
    errdefer values.deinit(allocator);
    var clone_values: std.ArrayList(ir.ValueId) = .empty;
    errdefer clone_values.deinit(allocator);
    for (used_values.items) |value_id| {
        if (closureContainsValue(program, closure, value_id)) continue;
        if (value_id.index() >= program.values.len) return null;
        const value = program.values[value_id.index()];
        if (value.id != value_id or value.function != analysis.function.id) return null;
        switch (value.origin) {
            .parameter, .capture => {
                if (!valueAvailableAtIncomingSources(program, analysis, value_id, incoming)) {
                    if (trace_mapping_failure) std.debug.print("external_mapping_reject value={} reason=parameter_unavailable\n", .{value_id.index()});
                    return null;
                }
            },
            .block_parameter => |origin| {
                const producer = externalBlockParameterBlock(program, analysis, value_id, origin.block, origin.index) orelse {
                    if (trace_mapping_failure) std.debug.print("external_mapping_reject value={} reason=invalid_block_parameter producer={} index={}\n", .{ value_id.index(), origin.block.index(), origin.index });
                    return null;
                };
                // A dominating source definition is only a fallback.  A prior
                // authenticated split may provide the value for this incoming
                // context even when the original producer still dominates it.
                const clone_value = if (incomingEdgesOriginateAtProducer(incoming, producer))
                    value_id
                else
                    (try findExistingValueCloneAlloc(
                        allocator,
                        program,
                        analysis,
                        producer,
                        value_id,
                        incoming,
                        closure,
                        lineage_index,
                        replay_index,
                        replay_cache,
                    )) orelse (try authenticatedBlockParameterIncomingValueAlloc(
                        allocator,
                        program,
                        analysis,
                        value_id,
                        producer,
                        origin.index,
                        incoming,
                        closure,
                        lineage_index,
                        replay_index,
                        replay_cache,
                    )) orelse if (definitionDominatesIncoming(analysis, producer, incoming))
                        value_id
                    else {
                        if (trace_mapping_failure) std.debug.print("external_mapping_reject value={} reason=no_block_parameter_mapping producer={} index={}\n", .{ value_id.index(), producer.index(), origin.index });
                        return null;
                    };
                const boundary_clone = selectBoundaryValueMapping(
                    program,
                    analysis,
                    value_id,
                    clone_value,
                    incoming,
                ) orelse {
                    if (trace_mapping_failure) std.debug.print("external_mapping_reject value={} reason=boundary_unavailable mapped={} producer={}\n", .{ value_id.index(), clone_value.index(), producer.index() });
                    return null;
                };
                if (!try appendValueMapping(allocator, program, &values, &clone_values, value_id, boundary_clone, false)) {
                    if (!try isAuthenticatedValueAliasAlloc(
                        allocator,
                        program,
                        analysis,
                        producer,
                        value_id,
                        boundary_clone,
                        incoming,
                        lineage_index,
                        replay_index,
                        replay_cache,
                    ) or !try appendValueMapping(allocator, program, &values, &clone_values, value_id, boundary_clone, true)) {
                        if (trace_mapping_failure) std.debug.print("external_mapping_reject value={} reason=mapping_collision mapped={} producer={}\n", .{ value_id.index(), boundary_clone.index(), producer.index() });
                        return null;
                    }
                    if (trace_mapping_failure) std.debug.print("external_mapping_authenticated_alias value={} mapped={} producer={}\n", .{ value_id.index(), boundary_clone.index(), producer.index() });
                }
            },
            .instruction_result => |origin| {
                const producer = externalInstructionProducerBlock(program, analysis.function.id, value_id, origin) orelse {
                    if (trace_mapping_failure) std.debug.print("external_mapping_reject value={} reason=invalid_instruction_result instruction={} index={}\n", .{ value_id.index(), origin.instruction.index(), origin.index });
                    return null;
                };
                const clone_value = if (incomingEdgesOriginateAtProducer(incoming, producer))
                    value_id
                else
                    (try findExistingValueCloneAlloc(
                        allocator,
                        program,
                        analysis,
                        producer,
                        value_id,
                        incoming,
                        closure,
                        lineage_index,
                        replay_index,
                        replay_cache,
                    )) orelse (try authenticatedInstructionResultIncomingValueAlloc(
                        allocator,
                        program,
                        analysis,
                        value_id,
                        producer,
                        incoming,
                        closure,
                        lineage_index,
                        replay_index,
                        replay_cache,
                    )) orelse if (isRematerializableConstant(program, value_id, analysis.function.id))
                        value_id
                    else if (definitionDominatesIncoming(analysis, producer, incoming))
                        value_id
                    else {
                        if (trace_mapping_failure) std.debug.print("external_mapping_reject value={} reason=no_instruction_mapping producer={} instruction={} index={}\n", .{ value_id.index(), producer.index(), origin.instruction.index(), origin.index });
                        return null;
                    };
                const boundary_clone = selectBoundaryValueMapping(
                    program,
                    analysis,
                    value_id,
                    clone_value,
                    incoming,
                ) orelse {
                    if (trace_mapping_failure) std.debug.print("external_mapping_reject value={} reason=boundary_unavailable mapped={} producer={}\n", .{ value_id.index(), clone_value.index(), producer.index() });
                    return null;
                };
                if (!try appendValueMapping(allocator, program, &values, &clone_values, value_id, boundary_clone, false)) {
                    if (!try isAuthenticatedValueAliasAlloc(
                        allocator,
                        program,
                        analysis,
                        producer,
                        value_id,
                        boundary_clone,
                        incoming,
                        lineage_index,
                        replay_index,
                        replay_cache,
                    ) or !try appendValueMapping(allocator, program, &values, &clone_values, value_id, boundary_clone, true)) {
                        if (trace_mapping_failure) std.debug.print("external_mapping_reject value={} reason=mapping_collision mapped={} producer={}\n", .{ value_id.index(), boundary_clone.index(), producer.index() });
                        return null;
                    }
                    if (trace_mapping_failure) std.debug.print("external_mapping_authenticated_alias value={} mapped={} producer={}\n", .{ value_id.index(), boundary_clone.index(), producer.index() });
                }
            },
        }
    }

    var packs: std.ArrayList(ir.ValuePackId) = .empty;
    errdefer packs.deinit(allocator);
    var clone_packs: std.ArrayList(ir.ValuePackId) = .empty;
    errdefer clone_packs.deinit(allocator);
    for (used_packs.items) |pack_id| {
        if (closureContainsPack(program, closure, pack_id)) continue;
        if (pack_id.index() >= program.value_packs.len) return null;
        const pack = program.value_packs[pack_id.index()];
        if (pack.id != pack_id or pack.function != analysis.function.id) return null;
        switch (pack.origin) {
            .varargs => {
                if (!packAvailableAtIncomingSources(program, analysis, pack_id, incoming)) {
                    if (trace_mapping_failure) std.debug.print("external_mapping_reject pack={} reason=varargs_unavailable\n", .{pack_id.index()});
                    return null;
                }
            },
            .instruction_result => |instruction_id| {
                const producer = externalPackProducerBlock(program, analysis.function.id, pack_id, instruction_id) orelse {
                    if (trace_mapping_failure) std.debug.print("external_mapping_reject pack={} reason=invalid_instruction_result instruction={}\n", .{ pack_id.index(), instruction_id.index() });
                    return null;
                };
                const clone_pack = if (incomingEdgesOriginateAtProducer(incoming, producer))
                    pack_id
                else
                    (try findExistingPackCloneAlloc(
                        allocator,
                        program,
                        analysis,
                        producer,
                        pack_id,
                        incoming,
                        closure,
                        lineage_index,
                        replay_index,
                        replay_cache,
                    )) orelse if (definitionDominatesIncoming(analysis, producer, incoming))
                        pack_id
                    else {
                        if (trace_mapping_failure) std.debug.print("external_mapping_reject pack={} reason=no_pack_mapping producer={} instruction={}\n", .{ pack_id.index(), producer.index(), instruction_id.index() });
                        return null;
                    };
                const boundary_clone = selectBoundaryPackMapping(
                    program,
                    analysis,
                    pack_id,
                    clone_pack,
                    incoming,
                ) orelse {
                    if (trace_mapping_failure) std.debug.print("external_mapping_reject pack={} reason=boundary_unavailable mapped={} producer={}\n", .{ pack_id.index(), clone_pack.index(), producer.index() });
                    return null;
                };
                if (!try appendPackMapping(allocator, &packs, &clone_packs, pack_id, boundary_clone)) {
                    if (trace_mapping_failure) std.debug.print("external_mapping_reject pack={} reason=mapping_collision mapped={} producer={}\n", .{ pack_id.index(), boundary_clone.index(), producer.index() });
                    return null;
                }
            },
        }
    }

    return .{
        .allocator = allocator,
        .values = try values.toOwnedSlice(allocator),
        .clone_values = try clone_values.toOwnedSlice(allocator),
        .packs = try packs.toOwnedSlice(allocator),
        .clone_packs = try clone_packs.toOwnedSlice(allocator),
    };
}

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

const ContinuationBridgeKey = struct {
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    target: ir.BlockId,
};

const ProjectionValueMatch = enum {
    same,
    forward,
    reverse,
    none,
};

const ComposedParameterProjectionResult = enum {
    not_applicable,
    matched,
    rejected,
};

/// Immutable clone/replay state used by structure building.  A structured
/// continuation may compare different SSA ids only when the complete entry
/// tuple is authenticated by the same replay machinery used for external
/// clone mappings.
pub const ReplayProjectionContext = struct {
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    lineage_index: CloneLineageIndex,
    replay_index: node_split.ReplayIndex,
    replay_cache: ReplayCache,
    continuation_bridge_cache: std.AutoHashMapUnmanaged(ContinuationBridgeKey, bool) = .empty,
    owner_composed_bridge_cache: std.AutoHashMapUnmanaged(ContinuationBridgeKey, bool) = .empty,
    one_parameter_trace_budget: usize = 512,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program) std.mem.Allocator.Error!ReplayProjectionContext {
        return initForFunction(allocator, program, null);
    }

    pub fn initForFunction(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        function_id: ?ir.FunctionId,
    ) std.mem.Allocator.Error!ReplayProjectionContext {
        var lineage_index = if (function_id) |selected|
            try CloneLineageIndex.initForFunction(allocator, program, selected)
        else
            try CloneLineageIndex.init(allocator, program);
        errdefer lineage_index.deinit();
        var replay_index = if (function_id) |selected|
            try node_split.ReplayIndex.initForFunction(allocator, program, selected)
        else
            try node_split.ReplayIndex.init(allocator, program);
        errdefer replay_index.deinit();
        return .{
            .allocator = allocator,
            .program = program,
            .lineage_index = lineage_index,
            .replay_index = replay_index,
            .replay_cache = ReplayCache.init(allocator, program, &replay_index),
        };
    }

    pub fn deinit(self: *ReplayProjectionContext) void {
        self.continuation_bridge_cache.deinit(self.allocator);
        self.owner_composed_bridge_cache.deinit(self.allocator);
        self.replay_cache.deinit();
        self.replay_index.deinit();
        self.lineage_index.deinit();
        self.* = undefined;
    }

    pub const CloneLineageParent = struct {
        block: ir.BlockId,
        group: ir.NodeSplitGroupId,
    };

    /// Return one authenticated clone parent from the immutable feedback
    /// lineage. A malformed or conflicting target is deliberately absent.
    pub fn cloneLineageParent(
        self: *const ReplayProjectionContext,
        block: ir.BlockId,
    ) ?CloneLineageParent {
        const step = self.lineage_index.step(self.program, block) orelse return null;
        return .{ .block = step.source, .group = step.group };
    }

    pub fn cloneLineageRoot(
        self: *const ReplayProjectionContext,
        block: ir.BlockId,
    ) ?ir.BlockId {
        if (block.index() >= self.program.blocks.len or
            self.program.blocks[block.index()].id != block or
            self.lineage_index.isMalformed(block)) return null;
        var current = block;
        var depth: usize = 0;
        while (true) {
            const parent = self.cloneLineageParent(current) orelse return current;
            if (parent.block == current or depth >= self.program.blocks.len) return null;
            current = parent.block;
            depth += 1;
        }
    }

    pub fn blockCount(self: *const ReplayProjectionContext) usize {
        return self.program.blocks.len;
    }

    pub fn sameCloneLineage(
        self: *const ReplayProjectionContext,
        left: ir.BlockId,
        right: ir.BlockId,
    ) bool {
        const left_root = self.cloneLineageRoot(left) orelse return false;
        const right_root = self.cloneLineageRoot(right) orelse return false;
        if (left_root != right_root) return false;

        var left_current = left;
        var right_current = right;
        var depth: usize = 0;
        while (depth <= self.program.blocks.len) : (depth += 1) {
            const left_parent = self.cloneLineageParent(left_current);
            const right_parent = self.cloneLineageParent(right_current);
            if (left_parent == null or right_parent == null) return left_parent == null and right_parent == null;
            if (left_parent.?.block != right_parent.?.block or
                left_parent.?.group != right_parent.?.group) return false;
            left_current = left_parent.?.block;
            right_current = right_parent.?.block;
        }
        return false;
    }

    /// Test exact split-edge ownership using the function-scoped rewrite
    /// index. This is metadata lookup only; callers still perform replay and
    /// live-edge authentication before consuming the result.
    pub fn hasNodeSplitArmEdge(
        self: *const ReplayProjectionContext,
        source: ir.BlockId,
        kind: ir.CfgEdgeKind,
        from: ir.BlockId,
        to: ir.BlockId,
        group: ?ir.NodeSplitGroupId,
    ) bool {
        const rewrite_indices = if (group) |selected_group|
            self.replay_index.nodeSplitRewriteIndicesForGroup(selected_group)
        else
            self.replay_index.nodeSplitRewriteIndices();
        for (rewrite_indices) |rewrite_index| {
            const rewrite = self.program.edge_rewrites[rewrite_index];
            if (rewrite.source == source and rewrite.kind == kind and
                rewrite.from.target == from and rewrite.to.target == to and
                (group == null or rewrite.node_split_group == group)) return true;
        }
        return false;
    }

    /// Return the function-scoped rewrite records for one authenticated
    /// node-split group.  Structure coverage uses this immutable index when
    /// repeatedly validating clone-group boundaries.
    pub fn nodeSplitRewriteIndicesForGroup(
        self: *const ReplayProjectionContext,
        group: ir.NodeSplitGroupId,
    ) []const usize {
        return self.replay_index.nodeSplitRewriteIndicesForGroup(group);
    }

    pub fn hasNodeSplitEntryEdge(
        self: *const ReplayProjectionContext,
        source: ir.BlockId,
        kind: ir.CfgEdgeKind,
        target: ir.BlockId,
        group: ir.NodeSplitGroupId,
    ) bool {
        for (self.nodeSplitRewriteIndicesForGroup(group)) |rewrite_index| {
            const rewrite = self.program.edge_rewrites[rewrite_index];
            if (rewrite.source == source and rewrite.kind == kind and rewrite.to.target == target) return true;
        }
        return false;
    }

    /// Reuse the function-scoped lineage and replay indexes for bridge
    /// authentication.  Structure building asks this question repeatedly;
    /// rebuilding the indexes for each edge turns a bounded proof into a
    /// quadratic allocation cost on large irreducible functions.
    pub fn hasAuthenticatedContinuationBridgeForEdge(
        self: *ReplayProjectionContext,
        analysis: *const cfg.Analysis,
        reference: ir.CfgEdgeRef,
    ) std.mem.Allocator.Error!bool {
        const key = ContinuationBridgeKey{
            .source = reference.source,
            .kind = reference.kind,
            .target = reference.target,
        };
        if (self.continuation_bridge_cache.get(key)) |cached| return cached;
        const result = try self.hasAuthenticatedContinuationBridgeForEdgeUncached(analysis, reference);
        try self.continuation_bridge_cache.put(self.allocator, key, result);
        return result;
    }

    /// Authenticate a cloned effectful-prefix handoff into an already-owned
    /// parameterized continuation. The live handoff edge is outside the
    /// continuation's SCC in this shape, so SCC reachability is not evidence;
    /// the incoming source must be a replay-authenticated descendant of the
    /// owner's edge source and carry the owner's mapped tuple.
    pub fn hasAuthenticatedParameterizedCloneHandoffForEdge(
        self: *ReplayProjectionContext,
        analysis: *const cfg.Analysis,
        owner_reference: ir.CfgEdgeRef,
        incoming_reference: ir.CfgEdgeRef,
    ) std.mem.Allocator.Error!bool {
        if (owner_reference.source == incoming_reference.source or
            owner_reference.kind != incoming_reference.kind or
            owner_reference.target != incoming_reference.target or
            !incomingEdgeIsCanonical(self.program, analysis, owner_reference) or
            !incomingEdgeIsCanonical(self.program, analysis, incoming_reference))
        {
            return false;
        }

        const owner_edge = cfg_edge.value(self.program, owner_reference) orelse return false;
        const incoming_edge = cfg_edge.value(self.program, incoming_reference) orelse return false;
        if (owner_edge.target != owner_reference.target or
            incoming_edge.target != incoming_reference.target or
            owner_edge.arguments.len != incoming_edge.arguments.len or
            incoming_reference.target.index() >= self.program.blocks.len)
        {
            return false;
        }

        const target = self.program.blocks[incoming_reference.target.index()];
        if (target.id != incoming_reference.target or target.parameters.len == 0 or
            !node_split.parametersAreCanonical(self.program.values, target) or
            owner_edge.arguments.len != target.parameters.len)
        {
            return false;
        }

        const lineage = (try cloneLineageAllocCached(
            self.allocator,
            self.program,
            owner_reference.source,
            incoming_reference.source,
            &self.lineage_index,
        )) orelse return false;
        defer self.allocator.free(lineage);
        if (lineage.len == 0 or
            !cloneLineageArgumentsAreStableCached(self.program, incoming_reference.source, &self.lineage_index) or
            !try cloneLineageArgumentsMatchReplayCached(
                self.allocator,
                self.program,
                owner_reference.source,
                incoming_reference.source,
                &self.lineage_index,
                &self.replay_index,
                &self.replay_cache,
            ))
        {
            return false;
        }

        for (lineage) |step| {
            const source_reference = edgeReferenceForKind(
                self.program,
                step.source,
                owner_reference.kind,
            ) orelse return false;
            const clone_reference = edgeReferenceForKind(
                self.program,
                step.clone,
                incoming_reference.kind,
            ) orelse return false;
            const source_edge = cfg_edge.value(self.program, source_reference) orelse return false;
            const clone_edge = cfg_edge.value(self.program, clone_reference) orelse return false;
            if (source_edge.target != owner_reference.target or
                clone_edge.target != incoming_reference.target)
            {
                return false;
            }
            const replay = (try self.replay_cache.get(step.source, step.clone, step.group)) orelse return false;
            if (!replayedEdgeArgumentsMatch(
                self.program,
                step.source,
                step.clone,
                source_edge,
                clone_edge,
                replay.*,
                true,
            )) return false;
        }

        for (owner_edge.arguments, incoming_edge.arguments) |owner_value, incoming_value| {
            const mapped = try mapValueThroughCloneLineageAllocCachedWithReplayCache(
                self.allocator,
                self.program,
                owner_reference.source,
                incoming_reference.source,
                owner_value,
                &self.lineage_index,
                &self.replay_index,
                &self.replay_cache,
            ) orelse return false;
            if (mapped != incoming_value) return false;
        }

        const closure = [_]ir.BlockId{incoming_reference.target};
        const incoming = [_]ir.CfgEdgeRef{incoming_reference};
        var external = try collectExternalCloneMappingsAllocWithReplayState(
            self.allocator,
            self.program,
            analysis,
            &closure,
            &incoming,
            &self.lineage_index,
            &self.replay_index,
            &self.replay_cache,
        );
        if (external) |*owned| {
            owned.deinit();
            return true;
        }
        return false;
    }

    /// Owner-composed collision history needs the stricter bridge proof.  The
    /// general continuation predicate also admits unchanged shared suffixes,
    /// which is correct for structure reuse but cannot authenticate a new
    /// collision arm's complete external tuple.
    pub fn hasAuthenticatedOwnerComposedContinuationBridgeForEdge(
        self: *ReplayProjectionContext,
        analysis: *const cfg.Analysis,
        reference: ir.CfgEdgeRef,
    ) std.mem.Allocator.Error!bool {
        const key = ContinuationBridgeKey{
            .source = reference.source,
            .kind = reference.kind,
            .target = reference.target,
        };
        if (self.owner_composed_bridge_cache.get(key)) |cached| return cached;
        const result = try hasAuthenticatedOwnerComposedCloneBridgeAlloc(
            self.allocator,
            self.program,
            analysis,
            reference,
            &self.lineage_index,
            &self.replay_index,
            &self.replay_cache,
        );
        try self.owner_composed_bridge_cache.put(self.allocator, key, result);
        return result;
    }

    fn hasAuthenticatedContinuationBridgeForEdgeUncached(
        self: *ReplayProjectionContext,
        analysis: *const cfg.Analysis,
        reference: ir.CfgEdgeRef,
    ) std.mem.Allocator.Error!bool {
        if (!incomingEdgeIsCanonical(self.program, analysis, reference)) return false;
        const current_edge = cfg_edge.value(self.program, reference) orelse return false;
        const closure = [_]ir.BlockId{reference.target};
        const incoming = [_]ir.CfgEdgeRef{reference};

        var found = false;
        var selected_source: ?ir.BlockId = null;
        var selected_group: ?ir.NodeSplitGroupId = null;
        for (self.program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.source != reference.source or
                rewrite.kind != reference.kind or rewrite.to.target != reference.target or
                rewrite.from.target == rewrite.to.target or rewrite.node_split_group == null)
            {
                continue;
            }
            found = true;
            if (!std.mem.eql(ir.ValueId, current_edge.arguments, rewrite.to.arguments)) return false;
            const group = rewrite.node_split_group.?;
            var replay = (try node_split.replayMappingsForCloneAllocWithIndex(
                self.allocator,
                self.program,
                &self.replay_index,
                rewrite.from.target,
                rewrite.to.target,
                group,
            )) orelse return false;
            defer replay.deinit();
            if (!nodeSplitRewriteArgumentsMatchReplay(self.program, rewrite, replay)) return false;
            if (!try cloneLineageArgumentsMatchReplayCached(
                self.allocator,
                self.program,
                rewrite.from.target,
                rewrite.to.target,
                &self.lineage_index,
                &self.replay_index,
                &self.replay_cache,
            )) return false;
            var external = try collectExternalCloneMappingsAllocWithReplayState(
                self.allocator,
                self.program,
                analysis,
                &closure,
                &incoming,
                &self.lineage_index,
                &self.replay_index,
                &self.replay_cache,
            );
            if (external) |*owned| {
                owned.deinit();
            } else return false;

            if (selected_source) |source| {
                if (source != rewrite.from.target or selected_group.? != group) return false;
            } else {
                selected_source = rewrite.from.target;
                selected_group = group;
            }
        }
        if (found) return true;
        if (try hasAuthenticatedComposedCloneBridgeAlloc(
            self.allocator,
            self.program,
            analysis,
            reference,
            &self.lineage_index,
            &self.replay_index,
            &self.replay_cache,
        )) return true;
        if (try hasAuthenticatedNestedCloneTargetBridgeForEdgeAlloc(
            self.allocator,
            self.program,
            analysis,
            reference,
            &self.lineage_index,
            &self.replay_index,
            &self.replay_cache,
        )) return true;
        return try hasAuthenticatedUnchangedCloneBridgeForEdgeAlloc(
            self.allocator,
            self.program,
            analysis,
            reference,
            &self.lineage_index,
            &self.replay_index,
            &self.replay_cache,
        );
    }

    pub const ContinuationCloneProjection = struct {
        root: ir.BlockId,
        group: ir.NodeSplitGroupId,
    };

    // Return the canonical root and split group for a live cloned entry only
    // after the same edge-level replay proof used by continuation reuse has
    // succeeded.  The group is needed by structure building to cover the
    // cloned body when the canonical boundary already owns its semantics.
    pub fn authenticatedContinuationCloneForEdge(
        self: *ReplayProjectionContext,
        analysis: *const cfg.Analysis,
        reference: ir.CfgEdgeRef,
    ) std.mem.Allocator.Error!?ContinuationCloneProjection {
        const current_edge = cfg_edge.value(self.program, reference) orelse return null;
        var selected_group: ?ir.NodeSplitGroupId = null;
        var has_direct_split = false;
        for (self.program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.source != reference.source or
                rewrite.kind != reference.kind or rewrite.to.target != reference.target or
                rewrite.node_split_group == null or
                !std.mem.eql(ir.ValueId, rewrite.to.arguments, current_edge.arguments))
            {
                continue;
            }
            has_direct_split = true;
            if (selected_group) |group| {
                if (group != rewrite.node_split_group.?) return null;
            } else {
                selected_group = rewrite.node_split_group.?;
            }
        }
        if (!has_direct_split) return null;
        if (!try self.hasAuthenticatedContinuationBridgeForEdge(analysis, reference)) return null;
        const group = selected_group orelse return null;
        const position = cloneLineagePositionCached(self.program, reference.target, &self.lineage_index) orelse return null;
        if (position.depth == 0 or position.root == reference.target) return null;
        return .{ .root = position.root, .group = group };
    }

    /// Authenticate a zero-parameter entry into a shared clone target when
    /// the incoming source is a nested clone of one target arm and the owner
    /// context came through another arm of the same split group.  A unique
    /// clone parent is insufficient here: several authenticated edge arms
    /// may intentionally converge on one cloned block.  Require the shared
    /// target replay, every arm's live edge, and the complete nested lineage.
    pub fn hasAuthenticatedSharedCloneTargetArmForEdge(
        self: *ReplayProjectionContext,
        analysis: *const cfg.Analysis,
        owner: ir.BlockId,
        reference: ir.CfgEdgeRef,
    ) std.mem.Allocator.Error!bool {
        if (owner == reference.source or
            !incomingEdgeIsCanonical(self.program, analysis, reference) or
            reference.target.index() >= self.program.blocks.len)
        {
            return false;
        }
        const target = self.program.blocks[reference.target.index()];
        const current_edge = cfg_edge.value(self.program, reference) orelse return false;
        if (target.id != reference.target or target.parameters.len != 0 or
            current_edge.arguments.len != 0)
        {
            return false;
        }

        var selected_group: ?ir.NodeSplitGroupId = null;
        var selected_source: ?ir.BlockId = null;
        var selected_arguments: ?[]const ir.ValueId = null;
        var found_arm = false;
        var owner_arm = false;
        for (self.program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.to.target != reference.target) continue;
            const group = rewrite.node_split_group orelse return false;
            if (rewrite.kind != reference.kind or
                !nodeSplitRewriteArgumentsAreStable(self.program, rewrite) or
                !activeNodeSplitRewrite(self.program, rewrite))
            {
                return false;
            }
            if (selected_group) |existing| {
                if (existing != group or selected_source.? != rewrite.from.target or
                    !std.mem.eql(ir.ValueId, selected_arguments.?, rewrite.to.arguments))
                {
                    return false;
                }
            } else {
                selected_group = group;
                selected_source = rewrite.from.target;
                selected_arguments = rewrite.to.arguments;
            }
            const arm_reference = edgeReferenceForKind(self.program, rewrite.source, rewrite.kind) orelse return false;
            const arm_edge = cfg_edge.value(self.program, arm_reference) orelse return false;
            if (arm_reference.target != reference.target or
                !std.mem.eql(ir.ValueId, arm_edge.arguments, rewrite.to.arguments))
            {
                return false;
            }
            var replay = (try node_split.replayMappingsForCloneAllocWithIndex(
                self.allocator,
                self.program,
                &self.replay_index,
                rewrite.from.target,
                rewrite.to.target,
                group,
            )) orelse return false;
            defer replay.deinit();
            if (!nodeSplitRewriteArgumentsMatchReplay(self.program, rewrite, replay)) return false;
            found_arm = true;
            owner_arm = owner_arm or rewrite.source == owner;
        }
        const group = selected_group orelse return false;
        const source = selected_source orelse return false;
        if (!found_arm or !owner_arm or
            !std.mem.eql(ir.ValueId, selected_arguments.?, current_edge.arguments))
        {
            return false;
        }
        const target_parent = self.cloneLineageParent(reference.target) orelse return false;
        if (target_parent.block != source or target_parent.group != group) return false;

        const closure = [_]ir.BlockId{reference.target};
        const incoming = [_]ir.CfgEdgeRef{reference};
        var external = try collectExternalCloneMappingsAllocWithReplayState(
            self.allocator,
            self.program,
            analysis,
            &closure,
            &incoming,
            &self.lineage_index,
            &self.replay_index,
            &self.replay_cache,
        );
        if (external) |*owned| {
            owned.deinit();
        } else return false;

        for (self.replay_index.nodeSplitRewriteIndicesForGroup(group)) |rewrite_index| {
            const rewrite = self.program.edge_rewrites[rewrite_index];
            if (rewrite.to.target != reference.target or rewrite.kind != reference.kind) continue;
            var lineage_valid = true;
            if (rewrite.source != reference.source) {
                const lineage = try cloneLineageAllocCached(
                    self.allocator,
                    self.program,
                    rewrite.source,
                    reference.source,
                    &self.lineage_index,
                ) orelse continue;
                defer self.allocator.free(lineage);
                if (!try cloneLineageArgumentsMatchReplayCached(
                    self.allocator,
                    self.program,
                    rewrite.source,
                    reference.source,
                    &self.lineage_index,
                    &self.replay_index,
                    &self.replay_cache,
                )) continue;
                for (lineage) |step| {
                    const source_reference = edgeReferenceForKind(self.program, step.source, reference.kind) orelse {
                        lineage_valid = false;
                        break;
                    };
                    const clone_reference = edgeReferenceForKind(self.program, step.clone, reference.kind) orelse {
                        lineage_valid = false;
                        break;
                    };
                    const source_edge = cfg_edge.value(self.program, source_reference) orelse {
                        lineage_valid = false;
                        break;
                    };
                    const clone_edge = cfg_edge.value(self.program, clone_reference) orelse {
                        lineage_valid = false;
                        break;
                    };
                    if (source_edge.target != reference.target or clone_edge.target != reference.target) {
                        lineage_valid = false;
                        break;
                    }
                    const replay = (try self.replay_cache.get(step.source, step.clone, step.group)) orelse {
                        lineage_valid = false;
                        break;
                    };
                    if (!replayedEdgeArgumentsMatch(
                        self.program,
                        step.source,
                        step.clone,
                        source_edge,
                        clone_edge,
                        replay.*,
                        true,
                    )) {
                        lineage_valid = false;
                        break;
                    }
                }
            } else {
                const arm_reference = edgeReferenceForKind(self.program, rewrite.source, reference.kind) orelse continue;
                const arm_edge = cfg_edge.value(self.program, arm_reference) orelse continue;
                lineage_valid = arm_edge.target == reference.target and
                    std.mem.eql(ir.ValueId, arm_edge.arguments, current_edge.arguments);
            }
            if (lineage_valid) return true;
        }
        return false;
    }

    /// A loop-carried transition can authenticate a contextual entry even
    /// when the incoming edge has no standalone clone-bridge record. Keep the
    /// expected owner tuple explicit so this cannot become a reachability or
    /// type-only bridge.
    pub fn hasAuthenticatedIterationContextualProjectionForEdge(
        self: *ReplayProjectionContext,
        analysis: *const cfg.Analysis,
        reference: ir.CfgEdgeRef,
        expected: []const ir.ValueId,
    ) std.mem.Allocator.Error!bool {
        if (expected.len == 0) return false;
        return try hasAuthenticatedIterationContextualProjectionAlloc(
            self.allocator,
            self.program,
            analysis,
            reference.target,
            reference,
            expected,
            &self.lineage_index,
            &self.replay_index,
            &self.replay_cache,
        );
    }

    /// Authenticate a distinct tuple entering a numeric transition through a
    /// parameterized carrier.  The carrier formal tuple must be the incoming
    /// tuple, and the existing iteration-state re-entry proof must identify
    /// that same carrier as the target of the normalized state edge.
    pub fn hasAuthenticatedNumericIterationCarrierReentryForEdge(
        self: *ReplayProjectionContext,
        analysis: *const cfg.Analysis,
        header: ir.BlockId,
        incoming: ir.CfgEdgeRef,
    ) std.mem.Allocator.Error!bool {
        if (!isIterationTransitionHeader(self.program, header) or
            header.index() >= self.program.blocks.len or
            !incomingEdgeIsCanonical(self.program, analysis, incoming) or
            incoming.target != header or
            !analysis.isReachable(incoming.source))
        {
            return false;
        }
        const header_block = self.program.blocks[header.index()];
        if (header_block.id != header or
            !node_split.parametersAreCanonical(self.program.values, header_block) or
            header_block.instructions.len != 1)
        {
            return false;
        }
        const transition_id = header_block.instructions[0];
        if (transition_id.index() >= self.program.instructions.len) return false;
        const transition = self.program.instructions[transition_id.index()];
        if (transition.id != transition_id or transition.results.len == 0) return false;
        switch (transition.operation) {
            .numeric_for_next => {},
            else => return false,
        }
        const transition_result = iterationTransitionResult(
            self.program,
            transition.results[0],
        ) orelse return false;
        const incoming_edge = cfg_edge.value(self.program, incoming) orelse return false;
        if (incoming_edge.target != header or
            incoming_edge.arguments.len != header_block.parameters.len)
        {
            return false;
        }

        var selected_carrier: ?ir.BlockId = null;
        for (analysis.function.blocks) |carrier_id| {
            if (carrier_id == header or
                carrier_id.index() >= self.program.blocks.len or
                !analysis.isReachable(carrier_id)) continue;
            const carrier = self.program.blocks[carrier_id.index()];
            if (carrier.id != carrier_id or
                carrier.function != analysis.function.id or
                carrier.parameters.len != incoming_edge.arguments.len or
                !node_split.parametersAreCanonical(self.program.values, carrier) or
                !std.mem.eql(ir.ValueId, carrier.parameters, incoming_edge.arguments) or
                !try analysis.canReach(carrier_id, incoming.source)) continue;
            if (!try authenticatedIterationStateReentry(
                self.program,
                analysis,
                transition_result,
                self.allocator,
                &self.lineage_index,
                &self.replay_index,
                &self.replay_cache,
                false,
                carrier_id,
            )) continue;
            if (selected_carrier != null) return false;
            selected_carrier = carrier_id;
        }
        return selected_carrier != null;
    }

    /// Authenticate a non-iteration parameterized continuation whose live
    /// edge carries a replay-equivalent tuple from a distinct incoming
    /// context. This is narrower than `parametersEquivalent`: equal tuples
    /// still need an ordinary bridge or an identity proof, while a changed
    /// tuple must have both live entry evidence and positional replay proof.
    pub fn hasAuthenticatedParameterizedContinuationProjectionForEdge(
        self: *ReplayProjectionContext,
        analysis: *const cfg.Analysis,
        reference: ir.CfgEdgeRef,
        expected: []const ir.ValueId,
    ) std.mem.Allocator.Error!bool {
        if (expected.len == 0 or
            !incomingEdgeIsCanonical(self.program, analysis, reference) or
            reference.target.index() >= self.program.blocks.len)
        {
            return false;
        }
        const block = self.program.blocks[reference.target.index()];
        if (block.id != reference.target or block.parameters.len != expected.len) return false;
        const edge = cfg_edge.value(self.program, reference) orelse return false;
        if (edge.target != reference.target or edge.arguments.len != block.parameters.len or
            std.mem.eql(ir.ValueId, expected, edge.arguments) or
            !hasLiveIncomingEdgeWithArguments(self.program, reference.target, expected))
        {
            return false;
        }
        // A parameterized clone may be an effectful prefix whose formal
        // tuple is consumed only by a nested numeric transition.  The
        // incoming tuple is intentionally not itself a transition-result
        // tuple in that shape; authenticate the complete prefix and its
        // positional handoff before trying value-level replay projection.
        const compound_projection = try hasAuthenticatedCompoundIterationContextualProjectionAlloc(
            self.program,
            analysis,
            reference.target,
            reference,
            expected,
        );
        const mixed_iteration_projection = try hasAuthenticatedMixedParameterizedIterationProjectionAlloc(
            self.program,
            analysis,
            reference.target,
            reference,
            expected,
        );
        const numeric_projection = try authenticatedNumericLoopCarriedTupleProjection(
            self.program,
            analysis,
            reference,
            expected,
            edge.arguments,
        );
        const equivalent = try self.parametersEquivalent(reference.target, expected, edge.arguments);
        traceStructural(
            "structural_phase parameterized_projection target={} source={} compound={} mixed_iteration={} numeric={} equivalent={} expected={any} actual={any}\n",
            .{
                reference.target.index(),
                reference.source.index(),
                compound_projection,
                mixed_iteration_projection,
                numeric_projection,
                equivalent,
                expected,
                edge.arguments,
            },
        );
        return compound_projection or mixed_iteration_projection or numeric_projection or equivalent;
    }

    fn rejectOneParameterProof(
        self: *ReplayProjectionContext,
        reference: ir.CfgEdgeRef,
        reason: []const u8,
    ) bool {
        if (trace_structural_phases and self.one_parameter_trace_budget != 0) {
            self.one_parameter_trace_budget -= 1;
            traceStructural("one_parameter_proof target={} source={} kind={s} reason={s}\n", .{
                reference.target.index(),
                reference.source.index(),
                @tagName(reference.kind),
                reason,
            });
        }
        return false;
    }

    fn rejectOneParameterSuccessorReplay(
        self: *ReplayProjectionContext,
        analysis: *const cfg.Analysis,
        reference: ir.CfgEdgeRef,
        source_block: ir.BlockId,
        target_block: ir.BlockId,
        source_edge: ir.Edge,
        target_edge: ir.Edge,
        replay: node_split.ReplayMappings,
    ) bool {
        if (trace_structural_phases and self.one_parameter_trace_budget != 0) {
            traceStructural("one_parameter_successor_replay source_target={} target_target={} source_args={any} target_args={any} replay_values={} replay_packs={}\n", .{
                source_edge.target.index(),
                target_edge.target.index(),
                source_edge.arguments,
                target_edge.arguments,
                replay.source_values.len,
                replay.source_packs.len,
            });
            traceStructural("one_parameter_successor_state source_reachable={} target_reachable={} source_function_matches={} target_function_matches={}\n", .{
                source_edge.target.index() < self.program.blocks.len and analysis.isReachable(source_edge.target),
                target_edge.target.index() < self.program.blocks.len and analysis.isReachable(target_edge.target),
                source_edge.target.index() < self.program.blocks.len and
                    self.program.blocks[source_edge.target.index()].function == self.program.blocks[target_block.index()].function,
                target_edge.target.index() < self.program.blocks.len and
                    self.program.blocks[target_edge.target.index()].function == self.program.blocks[target_block.index()].function,
            });
            for (source_edge.arguments, target_edge.arguments) |source_value, target_value| {
                traceStructural("one_parameter_successor_argument source={} target={} mapped={?d}\n", .{
                    source_value.index(),
                    target_value.index(),
                    mapValueFromReplay(self.program, source_block, target_block, source_value, replay),
                });
            }
        }
        return self.rejectOneParameterProof(reference, "successor_edge_replay_mismatch");
    }

    /// Authenticate the narrow one-parameter continuation shape used when a
    /// cloned effectful prefix has no distinct external value mapping.  The
    /// edge tuple must be preserved by a direct split rewrite, the one
    /// instruction must replay exactly, and its successor must have its own
    /// authenticated lineage.  The successor must either re-enter the
    /// numeric header that supplied the tuple or be a terminal block.
    pub fn hasAuthenticatedOneParameterContinuationForEdge(
        self: *ReplayProjectionContext,
        analysis: *const cfg.Analysis,
        reference: ir.CfgEdgeRef,
        expected: []const ir.ValueId,
    ) std.mem.Allocator.Error!bool {
        if (expected.len != 1 or
            !incomingEdgeIsCanonical(self.program, analysis, reference) or
            !analysis.isReachable(reference.source) or
            !analysis.isReachable(reference.target))
        {
            return self.rejectOneParameterProof(reference, "entry_shape");
        }

        const target = self.program.blocks[reference.target.index()];
        const incoming_edge = cfg_edge.value(self.program, reference) orelse
            return self.rejectOneParameterProof(reference, "incoming_edge_missing");
        if (target.id != reference.target or target.function != analysis.function.id or
            target.parameters.len != 1 or
            !node_split.parametersAreCanonical(self.program.values, target) or
            incoming_edge.target != reference.target or
            incoming_edge.arguments.len != 1 or
            incoming_edge.arguments[0] != expected[0] or
            !continuationParameterAcceptsValueType(self.program, target.parameters[0], expected[0]))
        {
            return self.rejectOneParameterProof(reference, "incoming_shape");
        }

        var source_id: ?ir.BlockId = null;
        var selected_group: ?ir.NodeSplitGroupId = null;
        for (self.program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.node_split_group == null or
                rewrite.source != reference.source or rewrite.kind != reference.kind or
                rewrite.to.target != reference.target or
                rewrite.from.target == rewrite.to.target)
            {
                continue;
            }
            if (source_id != null or
                !nodeSplitRewriteArgumentsAreStable(self.program, rewrite) or
                !activeNodeSplitRewrite(self.program, rewrite) or
                !std.mem.eql(ir.ValueId, rewrite.from.arguments, expected) or
                !std.mem.eql(ir.ValueId, rewrite.to.arguments, expected))
            {
                return self.rejectOneParameterProof(reference, "ambiguous_or_unstable_clone_rewrite");
            }
            source_id = rewrite.from.target;
            selected_group = rewrite.node_split_group.?;
        }

        const source_block_id = source_id orelse
            return self.rejectOneParameterProof(reference, "clone_rewrite_missing");
        const group = selected_group orelse
            return self.rejectOneParameterProof(reference, "clone_group_missing");
        const lineage_parent = self.cloneLineageParent(reference.target) orelse
            return self.rejectOneParameterProof(reference, "lineage_parent_missing");
        if (lineage_parent.block != source_block_id or lineage_parent.group != group) {
            return self.rejectOneParameterProof(reference, "lineage_parent_mismatch");
        }

        const source = if (source_block_id.index() < self.program.blocks.len)
            self.program.blocks[source_block_id.index()]
        else
            return self.rejectOneParameterProof(reference, "source_block_missing");
        if (source.id != source_block_id or source.function != target.function or
            source.parameters.len != 1 or
            !node_split.parametersAreCanonical(self.program.values, source) or
            !continuationParameterAcceptsValueType(self.program, source.parameters[0], expected[0]) or
            source.instructions.len != 1 or target.instructions.len != 1)
        {
            return self.rejectOneParameterProof(reference, "source_target_shape");
        }

        if (!try cloneLineageArgumentsMatchReplayCached(
            self.allocator,
            self.program,
            source_block_id,
            reference.target,
            &self.lineage_index,
            &self.replay_index,
            &self.replay_cache,
        )) {
            return self.rejectOneParameterProof(reference, "lineage_replay_mismatch");
        }
        const replay = (try self.replay_cache.get(source_block_id, reference.target, group)) orelse
            return self.rejectOneParameterProof(reference, "clone_replay_missing");
        if (!nodeSplitRewriteArgumentsMatchReplay(self.program, .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = reference.source,
            .kind = reference.kind,
            .from = .{ .target = source_block_id, .arguments = expected },
            .to = .{ .target = reference.target, .arguments = expected },
            .rule = .node_split,
            .node_split_group = group,
        }, replay.*)) {
            return self.rejectOneParameterProof(reference, "clone_rewrite_replay_mismatch");
        }
        const mapped_parameter = mapValueFromReplay(
            self.program,
            source_block_id,
            reference.target,
            source.parameters[0],
            replay.*,
        ) orelse {
            return self.rejectOneParameterProof(reference, "parameter_mapping_missing");
        };
        if (mapped_parameter != target.parameters[0]) {
            return self.rejectOneParameterProof(reference, "parameter_mapping_mismatch");
        }

        const source_instruction_id = source.instructions[0];
        const target_instruction_id = target.instructions[0];
        if (source_instruction_id.index() >= self.program.instructions.len or
            target_instruction_id.index() >= self.program.instructions.len)
        {
            return self.rejectOneParameterProof(reference, "instruction_missing");
        }
        const source_instruction = self.program.instructions[source_instruction_id.index()];
        const target_instruction = self.program.instructions[target_instruction_id.index()];
        if (source_instruction.id != source_instruction_id or
            target_instruction.id != target_instruction_id or
            source_instruction.block != source.id or
            target_instruction.block != target.id or
            source_instruction.results.len != target_instruction.results.len or
            (source_instruction.pack_result == null) != (target_instruction.pack_result == null) or
            !proof_effect_closure.hasObservableEffects(source_instruction.effects) or
            !proof_effect_closure.hasObservableEffects(target_instruction.effects) or
            !node_split_instruction.sameEffects(source_instruction.effects, target_instruction.effects) or
            !std.mem.eql(ir.EvidenceId, source_instruction.evidence, target_instruction.evidence))
        {
            return self.rejectOneParameterProof(reference, "instruction_semantics_mismatch");
        }

        const mapped_operation = (try node_split_instruction.remapOperation(
            self.allocator,
            self.program,
            self.program.values,
            source.function,
            source_instruction.operation,
            replay.source_values,
            replay.clone_values,
            replay.source_packs,
            replay.clone_packs,
        )) orelse return self.rejectOneParameterProof(reference, "operation_remap_missing");
        defer node_split_instruction.deinitRemappedOperation(self.allocator, mapped_operation);
        if (!node_split_instruction.sameOperation(mapped_operation, target_instruction.operation)) {
            return self.rejectOneParameterProof(reference, "operation_mismatch");
        }
        for (source_instruction.results, target_instruction.results) |source_result, target_result| {
            const mapped_result = mapValueFromReplay(
                self.program,
                source_block_id,
                reference.target,
                source_result,
                replay.*,
            ) orelse return self.rejectOneParameterProof(reference, "result_mapping_missing");
            if (mapped_result != target_result) {
                return self.rejectOneParameterProof(reference, "result_mapping_mismatch");
            }
        }
        if (source_instruction.pack_result) |source_pack| {
            const mapped_pack = mapPackFromReplay(
                self.program,
                source_block_id,
                reference.target,
                source_pack,
                replay.*,
            ) orelse return self.rejectOneParameterProof(reference, "pack_mapping_missing");
            if (mapped_pack != target_instruction.pack_result.?) {
                return self.rejectOneParameterProof(reference, "pack_mapping_mismatch");
            }
        }

        const source_edge = switch (source.terminator) {
            .jump => |edge| edge,
            .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return self.rejectOneParameterProof(reference, "source_not_jump"),
        };
        const target_edge = switch (target.terminator) {
            .jump => |edge| edge,
            .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return self.rejectOneParameterProof(reference, "target_not_jump"),
        };
        // The source successor may be historical and unreachable after an
        // earlier authenticated split.  The active clone successor remains
        // live; its lineage and rewrite record provide the correspondence.
        if (source_edge.target.index() >= self.program.blocks.len or
            target_edge.target.index() >= self.program.blocks.len or
            !analysis.isReachable(target_edge.target) or
            self.program.blocks[source_edge.target.index()].function != target.function or
            self.program.blocks[target_edge.target.index()].function != target.function or
            !replayedEdgeArgumentsMatch(
                self.program,
                source.id,
                target.id,
                source_edge,
                target_edge,
                replay.*,
                true,
            ))
        {
            return self.rejectOneParameterSuccessorReplay(analysis, reference, source.id, target.id, source_edge, target_edge, replay.*);
        }

        const successor_parent = self.cloneLineageParent(target_edge.target) orelse
            return self.rejectOneParameterProof(reference, "successor_lineage_parent_missing");
        if (successor_parent.block != source_edge.target or successor_parent.group != group) {
            return self.rejectOneParameterProof(reference, "successor_lineage_parent_mismatch");
        }
        var successor_rewrite_found = false;
        for (self.program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.node_split_group != group or
                rewrite.source != reference.target or rewrite.kind != .jump or
                rewrite.from.target != source_edge.target or
                rewrite.to.target != target_edge.target)
            {
                continue;
            }
            if (successor_rewrite_found or
                !nodeSplitRewriteArgumentsAreStable(self.program, rewrite) or
                !activeNodeSplitRewrite(self.program, rewrite))
            {
                return self.rejectOneParameterProof(reference, "ambiguous_or_unstable_successor_rewrite");
            }
            const successor_replay = (try self.replay_cache.get(
                source_edge.target,
                target_edge.target,
                group,
            )) orelse return self.rejectOneParameterProof(reference, "successor_replay_missing");
            if (!nodeSplitRewriteArgumentsMatchReplay(self.program, rewrite, successor_replay.*) or
                !try cloneLineageArgumentsMatchReplayCached(
                    self.allocator,
                    self.program,
                    source_edge.target,
                    target_edge.target,
                    &self.lineage_index,
                    &self.replay_index,
                    &self.replay_cache,
                )) return self.rejectOneParameterProof(reference, "successor_replay_mismatch");
            successor_rewrite_found = true;
        }
        if (!successor_rewrite_found) {
            return self.rejectOneParameterProof(reference, "successor_rewrite_missing");
        }

        const successor = self.program.blocks[target_edge.target.index()];
        const numeric_reentry = isIterationTransitionHeader(self.program, reference.source) and
            try analysis.canReach(target_edge.target, reference.source);
        const terminal_exit = switch (successor.terminator) {
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => true,
            .jump, .branch => false,
        };
        if (numeric_reentry or terminal_exit) return true;
        return self.rejectOneParameterProof(reference, "not_numeric_reentry_or_terminal");
    }

    pub fn parametersEquivalent(
        self: *ReplayProjectionContext,
        block_id: ir.BlockId,
        expected: ?[]const ir.ValueId,
        actual: ?[]const ir.ValueId,
    ) std.mem.Allocator.Error!bool {
        if (block_id.index() >= self.program.blocks.len) return false;
        const block = self.program.blocks[block_id.index()];
        if (block.id != block_id) return false;
        if (block.parameters.len == 0) {
            return (expected == null or expected.?.len == 0) and
                (actual == null or actual.?.len == 0);
        }
        const expected_arguments = expected orelse return false;
        const actual_arguments = actual orelse return false;
        if (expected_arguments.len != block.parameters.len or
            actual_arguments.len != block.parameters.len)
        {
            return false;
        }
        if (std.mem.eql(ir.ValueId, expected_arguments, actual_arguments)) return true;

        // A parameterized continuation may re-enter through a loop-carried
        // edge that forwards the target's own canonical formal tuple.  This
        // is a semantic state transition, not a clone-value identity match.
        // Keep the incoming tuple and split lineage authenticated before
        // allowing the visit context to be reused.
        if (try parameterizedForwardingReentryMatches(
            self.allocator,
            self.program,
            block_id,
            expected_arguments,
            actual_arguments,
            &self.lineage_index,
            &self.replay_index,
            &self.replay_cache,
        )) {
            return true;
        }

        // A numeric loop's internal state is intentionally fresh on every
        // transition. Accept it only when the expected tuple is an
        // authenticated forwarding entry for the same transition. The edge
        // may be represented only in rewrite history after a node split.
        if (try self.numericHeaderReentryMatches(block_id, expected_arguments, actual_arguments)) {
            return true;
        }

        // A structured continuation may contain the iteration transition
        // alongside setup instructions. In that shape the block is not a
        // bare iteration header, but its four-argument context can still be
        // proven by composing the complete authenticated transition lineage.
        if (try authenticatedIterationStateTupleEquivalentAlloc(
            self.allocator,
            self.program,
            block_id,
            expected_arguments,
            actual_arguments,
            &self.lineage_index,
            &self.replay_index,
            &self.replay_cache,
        )) {
            return true;
        }

        switch (try authenticatedComposedParameterProjectionAlloc(
            self.allocator,
            self.program,
            block_id,
            expected_arguments,
            actual_arguments,
            &self.lineage_index,
            &self.replay_index,
            &self.replay_cache,
        )) {
            .matched => {
                return true;
            },
            .rejected => return false,
            .not_applicable => {},
        }

        // Clone lineage proves how values can be projected, but it does not
        // prove that this projection is the tuple entering the current
        // continuation. Require the expected tuple to remain on a live edge
        // (or its active split record) before using value-only fallback. A
        // canonical formal tuple is allowed to have no second edge because
        // that case was already authenticated by the reentry rule above.
        const expected_edge_authenticated =
            hasLiveIncomingEdgeWithArguments(self.program, block_id, expected_arguments) or
            hasActiveNodeSplitIntoTargetWithArguments(self.program, block_id, expected_arguments);
        if (!expected_edge_authenticated and hasLiveIncomingEdgeToTarget(self.program, block_id)) return false;
        const actual_is_formal_tuple = std.mem.eql(ir.ValueId, actual_arguments, block.parameters);
        const actual_edge_authenticated = actual_is_formal_tuple or
            hasLiveIncomingEdgeWithArguments(self.program, block_id, actual_arguments) or
            hasActiveNodeSplitIntoTargetWithArguments(self.program, block_id, actual_arguments);
        if (!actual_edge_authenticated and hasLiveIncomingEdgeToTarget(self.program, block_id)) return false;

        var direction: ?ProjectionValueMatch = null;
        for (expected_arguments, actual_arguments) |expected_value, actual_value| {
            const match = try authenticatedProjectionValueMatchAlloc(
                self.allocator,
                self.program,
                expected_value,
                actual_value,
                &self.lineage_index,
                &self.replay_index,
                &self.replay_cache,
            );
            switch (match) {
                .same => {},
                .none => return false,
                .forward, .reverse => |candidate_direction| {
                    if (direction) |selected| {
                        if (selected != candidate_direction) return false;
                    } else {
                        direction = candidate_direction;
                    }
                },
            }
        }
        return direction != null;
    }

    fn numericHeaderReentryMatches(
        self: *ReplayProjectionContext,
        block_id: ir.BlockId,
        expected: []const ir.ValueId,
        actual: []const ir.ValueId,
    ) std.mem.Allocator.Error!bool {
        if (block_id.index() >= self.program.blocks.len) return false;
        const block = self.program.blocks[block_id.index()];
        const candidate = iteration_state.numericHeaderReentryCandidate(
            self.program,
            block,
            expected,
            actual,
        ) orelse return false;
        if (candidate.has_direct_incoming) return true;
        return try self.hasAuthenticatedNumericReentryBridge(candidate.ancestor, block_id, expected);
    }

    fn hasAuthenticatedNumericReentryBridge(
        self: *ReplayProjectionContext,
        ancestor: ir.BlockId,
        current: ir.BlockId,
        arguments: []const ir.ValueId,
    ) std.mem.Allocator.Error!bool {
        const lineage = (try cloneLineageAllocCached(
            self.allocator,
            self.program,
            ancestor,
            current,
            &self.lineage_index,
        )) orelse return false;
        defer self.allocator.free(lineage);
        if (lineage.len == 0) return false;

        for (lineage) |step| {
            if (!try cloneLineageArgumentsMatchReplayCached(
                self.allocator,
                self.program,
                step.source,
                step.clone,
                &self.lineage_index,
                &self.replay_index,
                &self.replay_cache,
            )) return false;
        }

        var found_active_edge = false;
        const final_step = lineage[lineage.len - 1];
        for (self.program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or
                rewrite.from.target != final_step.source or
                rewrite.to.target != final_step.clone or
                rewrite.node_split_group != final_step.group or
                !std.mem.eql(ir.ValueId, rewrite.to.arguments, arguments)) continue;
            if (!activeNodeSplitRewrite(self.program, rewrite)) continue;
            if (found_active_edge) return false;
            found_active_edge = true;
        }
        return found_active_edge;
    }
};

fn authenticatedComposedParameterProjectionAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    target: ir.BlockId,
    expected: []const ir.ValueId,
    actual: []const ir.ValueId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!ComposedParameterProjectionResult {
    if (target.index() >= program.blocks.len) return .not_applicable;
    const target_block = program.blocks[target.index()];
    if (target_block.id != target or target_block.parameters.len == 0 or
        expected.len != target_block.parameters.len or
        actual.len != target_block.parameters.len or
        !node_split.parametersAreCanonical(program.values, target_block))
    {
        return .not_applicable;
    }

    // This rule applies only to the two live contexts being compared.  A
    // value-only match is insufficient because an unrelated producer can have
    // the same type and a valid clone root without carrying either edge into
    // this continuation.
    if (!hasLiveIncomingEdgeWithArguments(program, target, expected) or
        !hasLiveIncomingEdgeWithArguments(program, target, actual))
    {
        return .not_applicable;
    }

    var projected = false;
    for (target_block.parameters, expected, actual) |formal, expected_value, actual_value| {
        if (!sameContinuationValueType(program, formal, expected_value) or
            !sameContinuationValueType(program, formal, actual_value))
        {
            return .rejected;
        }
        if (expected_value == actual_value) continue;
        projected = true;
        if (!try authenticatedComposedCloneValueMatchAlloc(
            allocator,
            program,
            expected_value,
            actual_value,
            lineage_index,
            replay_index,
            replay_cache,
        )) return .rejected;
    }
    return if (projected) .matched else .matched;
}

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

// A node-split clone can retain an edge to a shared continuation when that
// continuation was outside the cloned closure.  There is no edge_rewrite for
// that unchanged successor edge, so authenticate the edge by replaying the
// complete block lineage and comparing the ancestor's corresponding edge.
fn hasAuthenticatedUnchangedCloneBridgeForEdgeAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    reference: ir.CfgEdgeRef,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    if (reference.source.index() >= program.blocks.len or reference.target.index() >= program.blocks.len) return false;
    const source_block = program.blocks[reference.source.index()];
    const target_block = program.blocks[reference.target.index()];
    if (source_block.id != reference.source or target_block.id != reference.target or
        source_block.function != analysis.function.id or target_block.function != source_block.function or
        !analysis.isReachable(reference.source) or !analysis.isReachable(reference.target))
    {
        return false;
    }

    const position = cloneLineagePositionCached(program, reference.source, lineage_index) orelse {
        return false;
    };
    if (position.depth == 0) {
        return false;
    }
    const lineage = try cloneLineageAllocCached(
        allocator,
        program,
        position.root,
        reference.source,
        lineage_index,
    ) orelse {
        return false;
    };
    defer allocator.free(lineage);
    if (lineage.len == 0 or !cloneLineageArgumentsAreStableCached(program, reference.source, lineage_index)) {
        return false;
    }
    if (!try cloneLineageArgumentsMatchReplayCached(
        allocator,
        program,
        position.root,
        reference.source,
        lineage_index,
        replay_index,
        replay_cache,
    )) {
        return false;
    }

    const current_edge = cfg_edge.value(program, reference) orelse {
        return false;
    };
    for (lineage) |step| {
        const source_reference = edgeReferenceForKind(program, step.source, reference.kind) orelse {
            return false;
        };
        const clone_reference = edgeReferenceForKind(program, step.clone, reference.kind) orelse {
            return false;
        };
        const source_edge = cfg_edge.value(program, source_reference) orelse {
            return false;
        };
        const clone_edge = cfg_edge.value(program, clone_reference) orelse {
            return false;
        };
        const target_equivalent = try authenticatedCloneBranchEquivalentAlloc(
            allocator,
            program,
            source_edge.target,
            clone_edge.target,
            lineage_index,
            replay_index,
            replay_cache,
            0,
        );
        if (!target_equivalent) {
            return false;
        }
        const replay = (try replay_cache.get(step.source, step.clone, step.group)) orelse {
            return false;
        };
        if (!replayedEdgeArgumentsMatch(
            program,
            step.source,
            step.clone,
            source_edge,
            clone_edge,
            replay.*,
            target_equivalent,
        )) {
            return false;
        }
    }

    const final_reference = edgeReferenceForKind(program, reference.source, reference.kind) orelse {
        return false;
    };
    const final_edge = cfg_edge.value(program, final_reference) orelse {
        return false;
    };
    if (final_reference.target != reference.target or
        !std.mem.eql(ir.ValueId, final_edge.arguments, current_edge.arguments))
    {
        return false;
    }

    const closure = [_]ir.BlockId{reference.target};
    const incoming = [_]ir.CfgEdgeRef{reference};
    var external = try collectExternalCloneMappingsAllocWithReplayState(
        allocator,
        program,
        analysis,
        &closure,
        &incoming,
        lineage_index,
        replay_index,
        replay_cache,
    );
    if (external) |*owned| {
        owned.deinit();
        return true;
    }
    return false;
}

// A continuation target may already be a clone when a later authenticated
// clone keeps an incoming edge unchanged.  The ordinary unchanged-edge proof
// compares the whole source lineage against one target lineage and can reject
// this valid owner handoff when nested split groups differ.  Authenticate the
// handoff from the target clone's own split owner instead: the owner/source
// suffix, target lineage, rewrite tuples, and external uses must all replay.
fn hasAuthenticatedNestedCloneTargetBridgeForEdgeAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    reference: ir.CfgEdgeRef,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    if (!incomingEdgeIsCanonical(program, analysis, reference)) return false;
    const current_edge = cfg_edge.value(program, reference) orelse return false;
    const target_position = cloneLineagePositionCached(program, reference.target, lineage_index) orelse return false;
    if (target_position.depth == 0) return false;
    if (!try cloneLineageArgumentsMatchReplayCached(
        allocator,
        program,
        target_position.root,
        reference.target,
        lineage_index,
        replay_index,
        replay_cache,
    )) return false;

    for (program.edge_rewrites) |rewrite| {
        if (rewrite.rule != .node_split or rewrite.node_split_group == null or
            rewrite.kind != reference.kind or rewrite.to.target != reference.target or
            rewrite.from.target == rewrite.to.target)
        {
            continue;
        }
        const owner = rewrite.source;
        const owner_edge_reference = edgeReferenceForKind(program, owner, rewrite.kind) orelse continue;
        const owner_edge = cfg_edge.value(program, owner_edge_reference) orelse continue;
        if (owner_edge_reference.target != reference.target or
            !std.mem.eql(ir.ValueId, owner_edge.arguments, rewrite.to.arguments))
        {
            continue;
        }

        const target_step = cloneStepForTargetCached(program, reference.target, lineage_index) orelse continue;
        if (target_step.source != rewrite.from.target or target_step.group != rewrite.node_split_group.?) continue;
        if (!try cloneLineageArgumentsMatchReplayCached(
            allocator,
            program,
            target_step.source,
            reference.target,
            lineage_index,
            replay_index,
            replay_cache,
        )) continue;

        const suffix = try cloneLineageAllocCached(
            allocator,
            program,
            owner,
            reference.source,
            lineage_index,
        ) orelse continue;
        defer allocator.free(suffix);
        if (!try cloneLineageArgumentsMatchReplayCached(
            allocator,
            program,
            owner,
            reference.source,
            lineage_index,
            replay_index,
            replay_cache,
        )) continue;

        var suffix_valid = true;
        for (suffix) |step| {
            const source_reference = edgeReferenceForKind(program, step.source, reference.kind) orelse {
                suffix_valid = false;
                break;
            };
            const clone_reference = edgeReferenceForKind(program, step.clone, reference.kind) orelse {
                suffix_valid = false;
                break;
            };
            const source_edge = cfg_edge.value(program, source_reference) orelse {
                suffix_valid = false;
                break;
            };
            const clone_edge = cfg_edge.value(program, clone_reference) orelse {
                suffix_valid = false;
                break;
            };
            if (source_edge.target != reference.target or clone_edge.target != reference.target) {
                suffix_valid = false;
                break;
            }
            const replay = (try replay_cache.get(step.source, step.clone, step.group)) orelse {
                suffix_valid = false;
                break;
            };
            if (!replayedEdgeArgumentsMatch(
                program,
                step.source,
                step.clone,
                source_edge,
                clone_edge,
                replay.*,
                true,
            )) {
                suffix_valid = false;
                break;
            }
        }
        if (!suffix_valid) continue;

        // The owner edge is expressed in the owner block's value namespace.
        // A later clone may carry the same edge through a renamed suffix, so
        // compare the owner tuple with the live tuple only after replaying
        // every suffix mapping.
        if (owner_edge.arguments.len != current_edge.arguments.len) continue;
        var suffix_arguments_valid = true;
        for (owner_edge.arguments, current_edge.arguments) |owner_value, current_value| {
            var mapped = owner_value;
            for (suffix) |step| {
                const replay = (try replay_cache.get(step.source, step.clone, step.group)) orelse {
                    suffix_arguments_valid = false;
                    break;
                };
                mapped = mapValueFromReplay(program, step.source, step.clone, mapped, replay.*) orelse {
                    suffix_arguments_valid = false;
                    break;
                };
            }
            if (!suffix_arguments_valid or mapped != current_value) {
                suffix_arguments_valid = false;
                break;
            }
        }
        if (!suffix_arguments_valid) continue;

        const closure = [_]ir.BlockId{reference.target};
        const incoming = [_]ir.CfgEdgeRef{reference};
        var external = try collectExternalCloneMappingsAllocWithReplayState(
            allocator,
            program,
            analysis,
            &closure,
            &incoming,
            lineage_index,
            replay_index,
            replay_cache,
        );
        if (external) |*owned| {
            owned.deinit();
            return true;
        }
    }
    return false;
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

test "numeric loop-carried tuple projection accepts a complete SCC state" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const header = ir.BlockId.fromIndex(2);
    const body = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const transition = ir.InstructionId.fromIndex(0);

    const selector = ir.ValueId.fromIndex(0);
    const expected_control = ir.ValueId.fromIndex(1);
    const expected_limit = ir.ValueId.fromIndex(2);
    const expected_step = ir.ValueId.fromIndex(3);
    const expected_initial = ir.ValueId.fromIndex(4);
    const actual_control = ir.ValueId.fromIndex(5);
    const actual_limit = ir.ValueId.fromIndex(6);
    const actual_step = ir.ValueId.fromIndex(7);
    const actual_initial = ir.ValueId.fromIndex(8);
    const formal_control = ir.ValueId.fromIndex(9);
    const formal_limit = ir.ValueId.fromIndex(10);
    const formal_step = ir.ValueId.fromIndex(11);
    const formal_initial = ir.ValueId.fromIndex(12);
    const has_next = ir.ValueId.fromIndex(13);
    const normalized_limit = ir.ValueId.fromIndex(14);
    const normalized_step = ir.ValueId.fromIndex(15);
    const next_control = ir.ValueId.fromIndex(16);

    const expected_arguments = [_]ir.ValueId{
        expected_control,
        expected_limit,
        expected_step,
        expected_initial,
    };
    const actual_arguments = [_]ir.ValueId{
        actual_control,
        actual_limit,
        actual_step,
        actual_initial,
    };
    const formal_parameters = [_]ir.ValueId{
        formal_control,
        formal_limit,
        formal_step,
        formal_initial,
    };
    const function_parameters = [_]ir.ValueId{
        selector,
        expected_control,
        expected_limit,
        expected_step,
        expected_initial,
        actual_control,
        actual_limit,
        actual_step,
        actual_initial,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = expected_control, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = expected_limit, .function = function_id, .origin = .{ .parameter = 2 } },
        .{ .id = expected_step, .function = function_id, .origin = .{ .parameter = 3 } },
        .{ .id = expected_initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } },
        .{ .id = actual_control, .function = function_id, .origin = .{ .parameter = 5 } },
        .{ .id = actual_limit, .function = function_id, .origin = .{ .parameter = 6 } },
        .{ .id = actual_step, .function = function_id, .origin = .{ .parameter = 7 } },
        .{ .id = actual_initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 8 } },
        .{ .id = formal_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = formal_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
        .{ .id = formal_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
        .{ .id = formal_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
        .{ .id = has_next, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = transition,
        .block = header,
        .operation = .{ .numeric_for_next = .{
            .control = formal_control,
            .limit = formal_limit,
            .step = formal_step,
            .initial = formal_initial,
            .mode = .semantic_normalized,
        } },
        .results = &.{ has_next, normalized_limit, normalized_step, next_control },
        .effects = .numeric_for_next,
    }};
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = header, .arguments = actual_arguments[0..] },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{
            .target = header,
            .arguments = expected_arguments[0..],
        } } },
        .{ .id = header, .function = function_id, .parameters = formal_parameters[0..], .instructions = &.{transition}, .terminator = .{ .branch = .{
            .condition = has_next,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{
            .target = header,
            .arguments = actual_arguments[0..],
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = function_parameters[0..],
        .blocks = &.{ entry, owner, header, body, exit },
        .entry_block = entry,
    };
    const program = ir.Program{
        .program_id = "numeric-loop-carried-tuple-projection",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var context = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer context.deinit();
    try std.testing.expect(try context.hasAuthenticatedParameterizedContinuationProjectionForEdge(
        &analysis,
        .{ .source = body, .kind = .jump, .target = header },
        expected_arguments[0..],
    ));

    var disconnected_blocks = blocks;
    disconnected_blocks[body.index()].terminator = .{ .return_values = &.{} };
    var disconnected_program = program;
    disconnected_program.blocks = &disconnected_blocks;
    var disconnected_analysis = try cfg.Analysis.init(std.testing.allocator, &disconnected_program, function);
    defer disconnected_analysis.deinit();
    var disconnected_context = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &disconnected_program,
        function_id,
    );
    defer disconnected_context.deinit();
    try std.testing.expect(!try disconnected_context.hasAuthenticatedParameterizedContinuationProjectionForEdge(
        &disconnected_analysis,
        .{ .source = body, .kind = .jump, .target = header },
        expected_arguments[0..],
    ));

    var non_numeric_instructions = instructions;
    non_numeric_instructions[transition.index()].operation = .{ .copy = formal_control };
    var non_numeric_program = program;
    non_numeric_program.instructions = &non_numeric_instructions;
    var non_numeric_analysis = try cfg.Analysis.init(std.testing.allocator, &non_numeric_program, function);
    defer non_numeric_analysis.deinit();
    var non_numeric_context = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &non_numeric_program,
        function_id,
    );
    defer non_numeric_context.deinit();
    try std.testing.expect(!try non_numeric_context.hasAuthenticatedParameterizedContinuationProjectionForEdge(
        &non_numeric_analysis,
        .{ .source = body, .kind = .jump, .target = header },
        expected_arguments[0..],
    ));
}

test "numeric reentry accepts only an active replay-authenticated node split" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const false_instruction = ir.InstructionId.fromIndex(0);
    const source_transition = ir.InstructionId.fromIndex(1);
    const clone_transition = ir.InstructionId.fromIndex(2);
    const source_control = ir.ValueId.fromIndex(0);
    const source_limit = ir.ValueId.fromIndex(1);
    const source_step = ir.ValueId.fromIndex(2);
    const source_initial = ir.ValueId.fromIndex(3);
    const false_value = ir.ValueId.fromIndex(4);
    const source_has = ir.ValueId.fromIndex(5);
    const source_normalized_limit = ir.ValueId.fromIndex(6);
    const source_normalized_step = ir.ValueId.fromIndex(7);
    const source_next_control = ir.ValueId.fromIndex(8);
    const clone_control = ir.ValueId.fromIndex(9);
    const clone_limit = ir.ValueId.fromIndex(10);
    const clone_step = ir.ValueId.fromIndex(11);
    const clone_initial = ir.ValueId.fromIndex(12);
    const clone_has = ir.ValueId.fromIndex(13);
    const clone_normalized_limit = ir.ValueId.fromIndex(14);
    const clone_normalized_step = ir.ValueId.fromIndex(15);
    const clone_next_control = ir.ValueId.fromIndex(16);

    const expected_arguments = [_]ir.ValueId{ source_control, source_limit, source_step, source_initial };
    const actual_arguments = [_]ir.ValueId{ clone_next_control, clone_normalized_limit, clone_normalized_step, false_value };
    const values = [_]ir.Value{
        .{ .id = source_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = source_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
        .{ .id = source_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
        .{ .id = source_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
        .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } },
        .{ .id = source_has, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = source_transition, .index = 0 } } },
        .{ .id = source_normalized_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = source_transition, .index = 1 } } },
        .{ .id = source_normalized_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = source_transition, .index = 2 } } },
        .{ .id = source_next_control, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = source_transition, .index = 3 } } },
        .{ .id = clone_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = clone, .index = 0 } } },
        .{ .id = clone_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = clone, .index = 1 } } },
        .{ .id = clone_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = clone, .index = 2 } } },
        .{ .id = clone_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = clone, .index = 3 } } },
        .{ .id = clone_has, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = clone_transition, .index = 0 } } },
        .{ .id = clone_normalized_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = clone_transition, .index = 1 } } },
        .{ .id = clone_normalized_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = clone_transition, .index = 2 } } },
        .{ .id = clone_next_control, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = clone_transition, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = false_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = source_transition, .block = header, .operation = .{ .numeric_for_next = .{
            .control = source_control,
            .limit = source_limit,
            .step = source_step,
            .initial = source_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ source_has, source_normalized_limit, source_normalized_step, source_next_control }, .effects = .numeric_for_next },
        .{ .id = clone_transition, .block = clone, .operation = .{ .numeric_for_next = .{
            .control = clone_control,
            .limit = clone_limit,
            .step = clone_step,
            .initial = clone_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ clone_has, clone_normalized_limit, clone_normalized_step, clone_next_control }, .effects = .numeric_for_next },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{false_instruction}, .terminator = .{ .jump = .{ .target = clone, .arguments = expected_arguments[0..] } } },
        .{ .id = header, .function = function_id, .parameters = expected_arguments[0..], .instructions = &.{source_transition}, .terminator = .{ .return_values = &.{} } },
        .{ .id = clone, .function = function_id, .parameters = &.{ clone_control, clone_limit, clone_step, clone_initial }, .instructions = &.{clone_transition}, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{ .id = function_id, .blocks = &.{ entry, header, clone }, .entry_block = entry };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = entry,
        .kind = .jump,
        .from = .{ .target = header, .arguments = expected_arguments[0..] },
        .to = .{ .target = clone, .arguments = expected_arguments[0..] },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program = ir.Program{
        .program_id = "numeric-reentry-replay-history",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .edge_rewrites = &rewrites,
    };

    var context = try ReplayProjectionContext.init(std.testing.allocator, &program);
    defer context.deinit();
    try std.testing.expect(try context.parametersEquivalent(clone, expected_arguments[0..], actual_arguments[0..]));

    var tampered_blocks = blocks;
    tampered_blocks[entry.index()].terminator = .{ .jump = .{
        .target = clone,
        .arguments = &.{ source_control, source_limit, source_step, false_value },
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_context = try ReplayProjectionContext.init(std.testing.allocator, &tampered_program);
    defer tampered_context.deinit();
    try std.testing.expect(!try tampered_context.parametersEquivalent(clone, expected_arguments[0..], actual_arguments[0..]));
}

test "compound continuation reuses authenticated iteration state across clone lineage" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const state_entry = ir.BlockId.fromIndex(3);
    const actual_entry = ir.BlockId.fromIndex(4);
    const false_instruction = ir.InstructionId.fromIndex(0);
    const source_extra_instruction = ir.InstructionId.fromIndex(1);
    const source_transition = ir.InstructionId.fromIndex(2);
    const clone_extra_instruction = ir.InstructionId.fromIndex(3);
    const clone_transition = ir.InstructionId.fromIndex(4);
    const source_control = ir.ValueId.fromIndex(0);
    const source_limit = ir.ValueId.fromIndex(1);
    const source_step = ir.ValueId.fromIndex(2);
    const source_initial = ir.ValueId.fromIndex(3);
    const false_value = ir.ValueId.fromIndex(4);
    const source_extra = ir.ValueId.fromIndex(5);
    const source_has = ir.ValueId.fromIndex(6);
    const source_normalized_limit = ir.ValueId.fromIndex(7);
    const source_normalized_step = ir.ValueId.fromIndex(8);
    const source_next_control = ir.ValueId.fromIndex(9);
    const clone_control = ir.ValueId.fromIndex(10);
    const clone_limit = ir.ValueId.fromIndex(11);
    const clone_step = ir.ValueId.fromIndex(12);
    const clone_initial = ir.ValueId.fromIndex(13);
    const clone_extra = ir.ValueId.fromIndex(14);
    const clone_has = ir.ValueId.fromIndex(15);
    const clone_normalized_limit = ir.ValueId.fromIndex(16);
    const clone_normalized_step = ir.ValueId.fromIndex(17);
    const clone_next_control = ir.ValueId.fromIndex(18);
    const expected_arguments = [_]ir.ValueId{
        source_next_control,
        source_normalized_limit,
        source_normalized_step,
        false_value,
    };
    const actual_arguments = [_]ir.ValueId{
        clone_next_control,
        clone_normalized_limit,
        clone_normalized_step,
        false_value,
    };
    const source_parameters = [_]ir.ValueId{ source_control, source_limit, source_step, source_initial };
    const clone_parameters = [_]ir.ValueId{ clone_control, clone_limit, clone_step, clone_initial };
    const values = [_]ir.Value{
        .{ .id = source_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = source, .index = 0 } } },
        .{ .id = source_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = source, .index = 1 } } },
        .{ .id = source_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = source, .index = 2 } } },
        .{ .id = source_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = source, .index = 3 } } },
        .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } },
        .{ .id = source_extra, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = source_extra_instruction, .index = 0 } } },
        .{ .id = source_has, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = source_transition, .index = 0 } } },
        .{ .id = source_normalized_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = source_transition, .index = 1 } } },
        .{ .id = source_normalized_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = source_transition, .index = 2 } } },
        .{ .id = source_next_control, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = source_transition, .index = 3 } } },
        .{ .id = clone_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = clone, .index = 0 } } },
        .{ .id = clone_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = clone, .index = 1 } } },
        .{ .id = clone_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = clone, .index = 2 } } },
        .{ .id = clone_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = clone, .index = 3 } } },
        .{ .id = clone_extra, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = clone_extra_instruction, .index = 0 } } },
        .{ .id = clone_has, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = clone_transition, .index = 0 } } },
        .{ .id = clone_normalized_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = clone_transition, .index = 1 } } },
        .{ .id = clone_normalized_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = clone_transition, .index = 2 } } },
        .{ .id = clone_next_control, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = clone_transition, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = false_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = source_extra_instruction, .block = source, .operation = .{ .copy = source_control }, .results = &.{source_extra}, .effects = .pure },
        .{ .id = source_transition, .block = source, .operation = .{ .numeric_for_next = .{
            .control = source_control,
            .limit = source_limit,
            .step = source_step,
            .initial = source_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ source_has, source_normalized_limit, source_normalized_step, source_next_control }, .effects = .numeric_for_next },
        .{ .id = clone_extra_instruction, .block = clone, .operation = .{ .copy = clone_control }, .results = &.{clone_extra}, .effects = .pure },
        .{ .id = clone_transition, .block = clone, .operation = .{ .numeric_for_next = .{
            .control = clone_control,
            .limit = clone_limit,
            .step = clone_step,
            .initial = clone_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ clone_has, clone_normalized_limit, clone_normalized_step, clone_next_control }, .effects = .numeric_for_next },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{false_instruction}, .terminator = .{ .branch = .{
            .condition = false_value,
            .then_edge = .{ .target = source, .arguments = source_parameters[0..] },
            .else_edge = .{ .target = clone, .arguments = source_parameters[0..] },
        } } },
        .{ .id = source, .function = function_id, .parameters = source_parameters[0..], .instructions = &.{ source_extra_instruction, source_transition }, .terminator = .{ .return_values = &.{} } },
        .{ .id = clone, .function = function_id, .parameters = clone_parameters[0..], .instructions = &.{ clone_extra_instruction, clone_transition }, .terminator = .{ .return_values = &.{} } },
        .{ .id = state_entry, .function = function_id, .terminator = .{ .jump = .{ .target = clone, .arguments = expected_arguments[0..] } } },
        .{ .id = actual_entry, .function = function_id, .terminator = .{ .jump = .{ .target = clone, .arguments = actual_arguments[0..] } } },
    };
    const function = ir.Function{ .id = function_id, .blocks = &.{ entry, source, clone, state_entry, actual_entry }, .entry_block = entry };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = entry,
        .kind = .branch_else,
        .from = .{ .target = source, .arguments = source_parameters[0..] },
        .to = .{ .target = clone, .arguments = source_parameters[0..] },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program = ir.Program{
        .program_id = "compound-iteration-context-replay",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .edge_rewrites = &rewrites,
    };

    var context = try ReplayProjectionContext.init(std.testing.allocator, &program);
    defer context.deinit();
    try std.testing.expect(try context.parametersEquivalent(clone, expected_arguments[0..], actual_arguments[0..]));

    var tampered_instructions = instructions;
    tampered_instructions[clone_transition.index()].operation = .{ .numeric_for_next = .{
        .control = clone_limit,
        .limit = clone_limit,
        .step = clone_step,
        .initial = clone_initial,
        .mode = .semantic_normalized,
    } };
    var tampered_program = program;
    tampered_program.instructions = &tampered_instructions;
    var tampered_context = try ReplayProjectionContext.init(std.testing.allocator, &tampered_program);
    defer tampered_context.deinit();
    try std.testing.expect(!try tampered_context.parametersEquivalent(
        clone,
        expected_arguments[0..],
        actual_arguments[0..],
    ));
}

test "parameterized forwarding reentry requires canonical formals and live owner edges" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const reentry = ir.BlockId.fromIndex(2);
    const owner_first = ir.ValueId.fromIndex(0);
    const owner_second = ir.ValueId.fromIndex(1);
    const formal_first = ir.ValueId.fromIndex(2);
    const formal_second = ir.ValueId.fromIndex(3);
    const unrelated_first = ir.ValueId.fromIndex(4);
    const unrelated_second = ir.ValueId.fromIndex(5);
    const condition = ir.ValueId.fromIndex(6);
    const expected_arguments = [_]ir.ValueId{ owner_first, owner_second };
    const actual_arguments = [_]ir.ValueId{ formal_first, formal_second };
    const unrelated_arguments = [_]ir.ValueId{ unrelated_first, unrelated_second };
    const target_parameters = [_]ir.ValueId{ formal_first, formal_second };
    const values = [_]ir.Value{
        .{ .id = owner_first, .function = function_id, .type = ir.ValueType.integer, .origin = .{ .parameter = 0 } },
        .{ .id = owner_second, .function = function_id, .type = ir.ValueType.integer, .origin = .{ .parameter = 1 } },
        .{ .id = formal_first, .function = function_id, .type = ir.ValueType.integer, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = formal_second, .function = function_id, .type = ir.ValueType.integer, .origin = .{ .block_parameter = .{ .block = target, .index = 1 } } },
        .{ .id = unrelated_first, .function = function_id, .type = ir.ValueType.integer, .origin = .{ .parameter = 0 } },
        .{ .id = unrelated_second, .function = function_id, .type = ir.ValueType.integer, .origin = .{ .parameter = 1 } },
        .{ .id = condition, .function = function_id, .type = ir.ValueType.boolean, .origin = .{ .parameter = 2 } },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = target, .arguments = expected_arguments[0..] },
            .else_edge = .{ .target = reentry },
        } } },
        .{ .id = target, .function = function_id, .parameters = target_parameters[0..], .terminator = .{ .return_values = &.{} } },
        .{ .id = reentry, .function = function_id, .terminator = .{ .jump = .{ .target = target, .arguments = actual_arguments[0..] } } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, target, reentry },
        .entry_block = entry,
    };
    const program = ir.Program{
        .program_id = "parameterized-forwarding-formal-contract",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };

    var context = try ReplayProjectionContext.init(std.testing.allocator, &program);
    defer context.deinit();
    try std.testing.expect(try context.parametersEquivalent(target, expected_arguments[0..], actual_arguments[0..]));
    try std.testing.expect(!try context.parametersEquivalent(target, expected_arguments[0..], unrelated_arguments[0..]));
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    try std.testing.expect(try context.hasAuthenticatedParameterizedContinuationProjectionForEdge(
        &analysis,
        .{ .source = reentry, .kind = .jump, .target = target },
        expected_arguments[0..],
    ));

    var missing_owner_blocks = blocks;
    missing_owner_blocks[entry.index()].terminator = .{ .branch = .{
        .condition = condition,
        .then_edge = .{ .target = target, .arguments = actual_arguments[0..] },
        .else_edge = .{ .target = reentry },
    } };
    var missing_owner_program = program;
    missing_owner_program.blocks = &missing_owner_blocks;
    var missing_owner_context = try ReplayProjectionContext.init(std.testing.allocator, &missing_owner_program);
    defer missing_owner_context.deinit();
    try std.testing.expect(!try missing_owner_context.parametersEquivalent(
        target,
        expected_arguments[0..],
        actual_arguments[0..],
    ));
    var missing_owner_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &missing_owner_program,
        function,
    );
    defer missing_owner_analysis.deinit();
    try std.testing.expect(!try missing_owner_context.hasAuthenticatedParameterizedContinuationProjectionForEdge(
        &missing_owner_analysis,
        .{ .source = reentry, .kind = .jump, .target = target },
        expected_arguments[0..],
    ));
}

test "parameterized forwarding reentry authenticates clone replay without a formal edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const reentry = ir.BlockId.fromIndex(3);
    const source_first = ir.ValueId.fromIndex(0);
    const source_second = ir.ValueId.fromIndex(1);
    const clone_first = ir.ValueId.fromIndex(2);
    const clone_second = ir.ValueId.fromIndex(3);
    const unrelated_first = ir.ValueId.fromIndex(4);
    const unrelated_second = ir.ValueId.fromIndex(5);
    const expected_arguments = [_]ir.ValueId{ source_first, source_second };
    const actual_arguments = [_]ir.ValueId{ clone_first, clone_second };
    const unrelated_arguments = [_]ir.ValueId{ unrelated_first, unrelated_second };
    const source_parameters = [_]ir.ValueId{ source_first, source_second };
    const clone_parameters = [_]ir.ValueId{ clone_first, clone_second };
    const values = [_]ir.Value{
        .{ .id = source_first, .function = function_id, .type = ir.ValueType.integer, .origin = .{ .block_parameter = .{ .block = source, .index = 0 } } },
        .{ .id = source_second, .function = function_id, .type = ir.ValueType.integer, .origin = .{ .block_parameter = .{ .block = source, .index = 1 } } },
        .{ .id = clone_first, .function = function_id, .type = ir.ValueType.integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 0 } } },
        .{ .id = clone_second, .function = function_id, .type = ir.ValueType.integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 1 } } },
        .{ .id = unrelated_first, .function = function_id, .type = ir.ValueType.integer, .origin = .{ .parameter = 0 } },
        .{ .id = unrelated_second, .function = function_id, .type = ir.ValueType.integer, .origin = .{ .parameter = 1 } },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = clone, .arguments = expected_arguments[0..] } } },
        .{ .id = source, .function = function_id, .parameters = source_parameters[0..], .terminator = .{ .return_values = &.{} } },
        .{ .id = clone, .function = function_id, .parameters = clone_parameters[0..], .terminator = .{ .return_values = &.{} } },
        // The clone's formal tuple is the actual projection. It does not need
        // a separate CFG edge that carries the formal value IDs.
        .{ .id = reentry, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, source, clone, reentry },
        .entry_block = entry,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = entry,
        .kind = .jump,
        .from = .{ .target = source, .arguments = expected_arguments[0..] },
        .to = .{ .target = clone, .arguments = expected_arguments[0..] },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program = ir.Program{
        .program_id = "parameterized-forwarding-clone-contract",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };

    var context = try ReplayProjectionContext.init(std.testing.allocator, &program);
    defer context.deinit();
    try std.testing.expect(try context.parametersEquivalent(clone, expected_arguments[0..], actual_arguments[0..]));

    var tampered_rewrites = rewrites;
    tampered_rewrites[0].from.arguments = unrelated_arguments[0..];
    var tampered_replay_program = program;
    tampered_replay_program.edge_rewrites = &tampered_rewrites;
    var tampered_replay_context = try ReplayProjectionContext.init(std.testing.allocator, &tampered_replay_program);
    defer tampered_replay_context.deinit();
    try std.testing.expect(!try parameterizedForwardingReentryMatches(
        std.testing.allocator,
        tampered_replay_context.program,
        clone,
        expected_arguments[0..],
        actual_arguments[0..],
        &tampered_replay_context.lineage_index,
        &tampered_replay_context.replay_index,
        &tampered_replay_context.replay_cache,
    ));

    var tampered_edge_blocks = blocks;
    tampered_edge_blocks[entry.index()].terminator = .{ .jump = .{
        .target = clone,
        .arguments = unrelated_arguments[0..],
    } };
    var tampered_edge_program = program;
    tampered_edge_program.blocks = &tampered_edge_blocks;
    var tampered_edge_context = try ReplayProjectionContext.init(std.testing.allocator, &tampered_edge_program);
    defer tampered_edge_context.deinit();
    try std.testing.expect(!try parameterizedForwardingReentryMatches(
        std.testing.allocator,
        tampered_edge_context.program,
        clone,
        expected_arguments[0..],
        actual_arguments[0..],
        &tampered_edge_context.lineage_index,
        &tampered_edge_context.replay_index,
        &tampered_edge_context.replay_cache,
    ));
}

test "parameterized projection composes authenticated clone lineage positionally" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const root = ir.BlockId.fromIndex(1);
    const expected_block = ir.BlockId.fromIndex(2);
    const middle = ir.BlockId.fromIndex(3);
    const actual_block = ir.BlockId.fromIndex(4);
    const target = ir.BlockId.fromIndex(5);

    const selector = ir.ValueId.fromIndex(0);
    const root_first = ir.ValueId.fromIndex(1);
    const root_second = ir.ValueId.fromIndex(2);
    const expected_first = ir.ValueId.fromIndex(3);
    const expected_second = ir.ValueId.fromIndex(4);
    const middle_first = ir.ValueId.fromIndex(5);
    const middle_second = ir.ValueId.fromIndex(6);
    const actual_first = ir.ValueId.fromIndex(7);
    const actual_second = ir.ValueId.fromIndex(8);
    const formal_first = ir.ValueId.fromIndex(9);
    const formal_second = ir.ValueId.fromIndex(10);
    const unrelated_first = ir.ValueId.fromIndex(11);
    const unrelated_second = ir.ValueId.fromIndex(12);

    const root_parameters = [_]ir.ValueId{ root_first, root_second };
    const expected_parameters = [_]ir.ValueId{ expected_first, expected_second };
    const middle_parameters = [_]ir.ValueId{ middle_first, middle_second };
    const actual_parameters = [_]ir.ValueId{ actual_first, actual_second };
    const target_parameters = [_]ir.ValueId{ formal_first, formal_second };

    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = root_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = root, .index = 0 } } },
        .{ .id = root_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = root, .index = 1 } } },
        .{ .id = expected_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = expected_block, .index = 0 } } },
        .{ .id = expected_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = expected_block, .index = 1 } } },
        .{ .id = middle_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = middle, .index = 0 } } },
        .{ .id = middle_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = middle, .index = 1 } } },
        .{ .id = actual_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = actual_block, .index = 0 } } },
        .{ .id = actual_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = actual_block, .index = 1 } } },
        .{ .id = formal_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = formal_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 1 } } },
        .{ .id = unrelated_first, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = unrelated_second, .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
    };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = expected_block, .arguments = root_parameters[0..] },
            .else_edge = .{ .target = middle, .arguments = root_parameters[0..] },
        } } },
        .{ .id = root, .function = function_id, .parameters = root_parameters[0..], .terminator = .{ .jump = .{ .target = target, .arguments = root_parameters[0..] } } },
        .{ .id = expected_block, .function = function_id, .parameters = expected_parameters[0..], .terminator = .{ .jump = .{ .target = target, .arguments = expected_parameters[0..] } } },
        .{ .id = middle, .function = function_id, .parameters = middle_parameters[0..], .terminator = .{ .jump = .{ .target = target, .arguments = middle_parameters[0..] } } },
        .{ .id = actual_block, .function = function_id, .parameters = actual_parameters[0..], .terminator = .{ .jump = .{ .target = target, .arguments = actual_parameters[0..] } } },
        .{ .id = target, .function = function_id, .parameters = target_parameters[0..], .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, unrelated_first, unrelated_second },
        .blocks = &.{ entry, root, expected_block, middle, actual_block, target },
        .entry_block = entry,
    };
    const group_final = ir.NodeSplitGroupId.fromIndex(0);
    const group_forward = ir.NodeSplitGroupId.fromIndex(1);
    const root_arguments = root_parameters[0..];
    const middle_arguments = middle_parameters[0..];
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .branch_then,
            .from = .{ .target = root, .arguments = root_arguments },
            .to = .{ .target = expected_block, .arguments = root_arguments },
            .rule = .node_split,
            .node_split_group = group_final,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = entry,
            .kind = .branch_else,
            .from = .{ .target = root, .arguments = root_arguments },
            .to = .{ .target = middle, .arguments = root_arguments },
            .rule = .node_split,
            .node_split_group = group_forward,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = middle,
            .kind = .jump,
            .from = .{ .target = middle, .arguments = middle_arguments },
            .to = .{ .target = actual_block, .arguments = middle_arguments },
            .rule = .node_split,
            .node_split_group = group_final,
        },
    };
    var program = ir.Program{
        .program_id = "authenticated-two-hop-positional-projection",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };

    var context = try ReplayProjectionContext.init(std.testing.allocator, &program);
    defer context.deinit();
    try std.testing.expect(try context.parametersEquivalent(
        target,
        expected_parameters[0..],
        actual_parameters[0..],
    ));
    try std.testing.expect(try authenticatedComposedCloneValueMatchAlloc(
        std.testing.allocator,
        &program,
        expected_first,
        actual_first,
        &context.lineage_index,
        &context.replay_index,
        &context.replay_cache,
    ));

    var tampered_rewrites = rewrites;
    tampered_rewrites[1].to.arguments = &.{ unrelated_first, unrelated_second };
    var tampered_replay_program = program;
    tampered_replay_program.edge_rewrites = &tampered_rewrites;
    var tampered_replay_context = try ReplayProjectionContext.init(std.testing.allocator, &tampered_replay_program);
    defer tampered_replay_context.deinit();
    try std.testing.expect(!try tampered_replay_context.parametersEquivalent(
        target,
        expected_parameters[0..],
        actual_parameters[0..],
    ));

    var tampered_blocks = blocks;
    tampered_blocks[actual_block.index()].terminator = .{ .jump = .{
        .target = target,
        .arguments = &.{ unrelated_first, unrelated_second },
    } };
    var tampered_edge_program = program;
    tampered_edge_program.blocks = &tampered_blocks;
    var tampered_edge_context = try ReplayProjectionContext.init(std.testing.allocator, &tampered_edge_program);
    defer tampered_edge_context.deinit();
    try std.testing.expect(!try tampered_edge_context.parametersEquivalent(
        target,
        expected_parameters[0..],
        &.{ unrelated_first, unrelated_second },
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

// Clone composition can produce equivalent sibling branches at one lineage
// depth and then continue cloning from only one sibling.  Ancestor checks are
// intentionally insufficient for that shape.  Match the final split group,
// recursively authenticate the source branches, and keep every replay step in
// the proof before allowing positional value mapping.
fn authenticatedCloneBranchEquivalentAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    left: ir.BlockId,
    right: ir.BlockId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
    depth: usize,
) std.mem.Allocator.Error!bool {
    if (left == right) return true;
    if (depth > program.blocks.len) return false;
    const left_position = cloneLineagePositionCached(program, left, lineage_index) orelse return false;
    const right_position = cloneLineagePositionCached(program, right, lineage_index) orelse return false;
    if (left_position.root != right_position.root) return false;

    const left_step = cloneStepForTargetCached(program, left, lineage_index);
    const right_step = cloneStepForTargetCached(program, right, lineage_index);
    if (left_step) |left_value| {
        if (right_step) |right_value| {
            if (left_value.group != right_value.group) return false;
            if (!try cloneLineageArgumentsMatchReplayCached(
                allocator,
                program,
                left_value.source,
                left_value.clone,
                lineage_index,
                replay_index,
                replay_cache,
            ) or !try cloneLineageArgumentsMatchReplayCached(
                allocator,
                program,
                right_value.source,
                right_value.clone,
                lineage_index,
                replay_index,
                replay_cache,
            )) return false;
            return try authenticatedCloneBranchEquivalentAlloc(
                allocator,
                program,
                left_value.source,
                right_value.source,
                lineage_index,
                replay_index,
                replay_cache,
                depth + 1,
            );
        }
        if (!try cloneLineageArgumentsMatchReplayCached(
            allocator,
            program,
            left_value.source,
            left_value.clone,
            lineage_index,
            replay_index,
            replay_cache,
        )) return false;
        return try authenticatedCloneBranchEquivalentAlloc(
            allocator,
            program,
            left_value.source,
            right,
            lineage_index,
            replay_index,
            replay_cache,
            depth + 1,
        );
    }
    const right_value = right_step orelse return false;
    if (!try cloneLineageArgumentsMatchReplayCached(
        allocator,
        program,
        right_value.source,
        right_value.clone,
        lineage_index,
        replay_index,
        replay_cache,
    )) return false;
    return try authenticatedCloneBranchEquivalentAlloc(
        allocator,
        program,
        left,
        right_value.source,
        lineage_index,
        replay_index,
        replay_cache,
        depth + 1,
    );
}

fn authenticatedBranchProjectionValueMapAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.BlockId,
    clone: ir.BlockId,
    value: ir.ValueId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!?ir.ValueId {
    if (!try authenticatedCloneBranchEquivalentAlloc(
        allocator,
        program,
        source,
        clone,
        lineage_index,
        replay_index,
        replay_cache,
        0,
    )) return null;
    return mapValueByCloneShape(program, source, clone, value);
}

fn authenticatedProjectionValueMatchAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    expected: ir.ValueId,
    actual: ir.ValueId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!ProjectionValueMatch {
    if (expected == actual) return .same;
    if (expected.index() >= program.values.len or actual.index() >= program.values.len) return .none;
    const expected_value = program.values[expected.index()];
    const actual_value = program.values[actual.index()];
    if (expected_value.id != expected or actual_value.id != actual or
        expected_value.function != actual_value.function)
    {
        return .none;
    }
    const expected_producer = projectionValueProducer(program, expected) orelse return .none;
    const actual_producer = projectionValueProducer(program, actual) orelse return .none;
    if (expected_producer == actual_producer) return .none;

    if (blockLineageContainsCached(program, actual_producer, expected_producer, lineage_index) and
        try cloneLineageArgumentsMatchReplayCached(
            allocator,
            program,
            expected_producer,
            actual_producer,
            lineage_index,
            replay_index,
            replay_cache,
        ))
    {
        const mapped = try mapValueThroughCloneLineageAllocCachedWithReplayCache(
            allocator,
            program,
            expected_producer,
            actual_producer,
            expected,
            lineage_index,
            replay_index,
            replay_cache,
        );
        if (mapped == actual) return .forward;
    }

    if (blockLineageContainsCached(program, expected_producer, actual_producer, lineage_index) and
        try cloneLineageArgumentsMatchReplayCached(
            allocator,
            program,
            actual_producer,
            expected_producer,
            lineage_index,
            replay_index,
            replay_cache,
        ))
    {
        const mapped = try mapValueThroughCloneLineageAllocCachedWithReplayCache(
            allocator,
            program,
            actual_producer,
            expected_producer,
            actual,
            lineage_index,
            replay_index,
            replay_cache,
        );
        if (mapped == expected) return .reverse;
    }

    if (try authenticatedBranchProjectionValueMapAlloc(
        allocator,
        program,
        expected_producer,
        actual_producer,
        expected,
        lineage_index,
        replay_index,
        replay_cache,
    )) |mapped| {
        if (mapped == actual) return .forward;
    }

    if (try authenticatedBranchProjectionValueMapAlloc(
        allocator,
        program,
        actual_producer,
        expected_producer,
        actual,
        lineage_index,
        replay_index,
        replay_cache,
    )) |mapped| {
        if (mapped == expected) return .reverse;
    }
    return .none;
}

fn cloneLineageArgumentsAreStable(
    program: *const ir.Program,
    block: ir.BlockId,
) bool {
    return cloneLineageArgumentsAreStableCached(program, block, null);
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

fn externalBlockParameterIsAvailable(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    value_id: ir.ValueId,
    block_id: ir.BlockId,
    parameter_index: u32,
    incoming: []const ir.CfgEdgeRef,
) bool {
    if (block_id.index() >= program.blocks.len) return false;
    const block = program.blocks[block_id.index()];
    const index: usize = @intCast(parameter_index);
    return block.id == block_id and block.function == analysis.function.id and
        index < block.parameters.len and block.parameters[index] == value_id and
        definitionDominatesIncoming(analysis, block_id, incoming);
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

fn authenticatedBlockParameterIncomingValueAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    value_id: ir.ValueId,
    producer: ir.BlockId,
    parameter_index: u32,
    incoming: []const ir.CfgEdgeRef,
    closure: []const ir.BlockId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!?ir.ValueId {
    if (producer.index() >= program.blocks.len or incoming.len == 0) return null;
    const producer_block = program.blocks[producer.index()];
    const index: usize = @intCast(parameter_index);
    if (producer_block.id != producer or producer_block.function != analysis.function.id or
        index >= producer_block.parameters.len or producer_block.parameters[index] != value_id)
    {
        return null;
    }
    for (incoming) |reference| {
        if (!incomingEdgeIsCanonical(program, analysis, reference)) return null;
    }

    var selected: ?ir.ValueId = null;
    for (analysis.function.blocks) |source_block_id| {
        if (source_block_id.index() >= program.blocks.len or
            program.blocks[source_block_id.index()].id != source_block_id or
            program.blocks[source_block_id.index()].function != analysis.function.id or
            !analysis.isReachable(source_block_id)) continue;
        const source_block = program.blocks[source_block_id.index()];

        switch (source_block.terminator) {
            .jump => |edge| {
                const candidate = try authenticatedBlockParameterEdgeValueAlloc(
                    allocator,
                    program,
                    analysis,
                    source_block_id,
                    producer,
                    edge,
                    incoming,
                    closure,
                    lineage_index,
                    replay_index,
                    replay_cache,
                    index,
                );
                if (candidate) |value| {
                    if (selected) |existing| {
                        if (existing != value) return null;
                    } else selected = value;
                }
            },
            .branch => |branch| for ([_]ir.Edge{ branch.then_edge, branch.else_edge }, 0..) |edge, edge_index| {
                const candidate = try authenticatedBlockParameterEdgeValueAlloc(
                    allocator,
                    program,
                    analysis,
                    source_block_id,
                    producer,
                    edge,
                    incoming,
                    closure,
                    lineage_index,
                    replay_index,
                    replay_cache,
                    index,
                );
                _ = edge_index;
                if (candidate) |value| {
                    if (selected) |existing| {
                        if (existing != value) return null;
                    } else selected = value;
                }
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }
    return selected;
}

fn authenticatedBlockParameterEdgeValueAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.BlockId,
    producer: ir.BlockId,
    edge: ir.Edge,
    incoming: []const ir.CfgEdgeRef,
    closure: []const ir.BlockId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
    parameter_index: usize,
) std.mem.Allocator.Error!?ir.ValueId {
    if (edge.target != producer or edge.arguments.len <= parameter_index or
        producer.index() >= program.blocks.len or
        edge.arguments.len != program.blocks[producer.index()].parameters.len)
    {
        return null;
    }
    for (incoming) |reference| {
        if (!try analysis.canReach(reference.target, source)) return null;
    }
    if (trace_structural_phases and closure.len >= 50) {
        if (cloneStepForTargetCached(program, source, lineage_index)) |step| {
            const context_match = try cloneContextMatchesIncomingWithReplayCached(
                allocator,
                program,
                analysis,
                source,
                incoming,
                lineage_index,
                replay_index,
                replay_cache,
            );
            const replay_match = try cloneLineageArgumentsMatchReplayCached(
                allocator,
                program,
                step.source,
                source,
                lineage_index,
                replay_index,
                replay_cache,
            );
            std.debug.print("parameter_bridge_source_lineage source={} parent={} group={} context={} replay={}\n", .{
                source.index(),
                step.source.index(),
                step.group.index(),
                context_match,
                replay_match,
            });
        } else {
            std.debug.print("parameter_bridge_source_lineage source={} parent=none\n", .{source.index()});
        }
    }
    const parameterized_authenticated = try parameterizedContinuationArgumentsAreAuthenticated(
        allocator,
        program,
        analysis,
        source,
        producer,
        edge.arguments,
        incoming,
        closure,
        &.{},
        lineage_index,
        replay_index,
        replay_cache,
        .incoming_parameter_bridge,
    );
    if (!parameterized_authenticated) {
        if (trace_structural_phases and closure.len >= 50) {
            std.debug.print("parameter_bridge_rejected source={} producer={} parameter_index={} closure={} edge_args={any} incoming={any}\n", .{
                source.index(),
                producer.index(),
                parameter_index,
                closure.len,
                edge.arguments,
                incoming,
            });
        }
        return null;
    }
    if (trace_structural_phases and closure.len >= 50) {
        std.debug.print("parameter_bridge_accept source={} producer={} parameter_index={} closure={} edge_args={any}\n", .{
            source.index(),
            producer.index(),
            parameter_index,
            closure.len,
            edge.arguments,
        });
    }
    return edge.arguments[parameter_index];
}

fn authenticatedInstructionResultIncomingValueAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    value_id: ir.ValueId,
    producer: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    closure: []const ir.BlockId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!?ir.ValueId {
    if (producer.index() >= program.blocks.len or incoming.len == 0) return null;
    const producer_block = program.blocks[producer.index()];
    if (producer_block.id != producer or producer_block.function != analysis.function.id) return null;

    var selected: ?ir.ValueId = null;
    const consider = struct {
        fn edge(
            allocator_: std.mem.Allocator,
            program_: *const ir.Program,
            analysis_: *const cfg.Analysis,
            source_: ir.BlockId,
            edge_: ir.Edge,
            value_: ir.ValueId,
            incoming_: []const ir.CfgEdgeRef,
            closure_: []const ir.BlockId,
            lineage_index_: *const CloneLineageIndex,
            replay_index_: *const node_split.ReplayIndex,
            replay_cache_: *ReplayCache,
        ) std.mem.Allocator.Error!?ir.ValueId {
            if (edge_.target.index() >= program_.blocks.len) return null;
            const target_block = program_.blocks[edge_.target.index()];
            if (target_block.id != edge_.target or target_block.parameters.len == 0 or
                edge_.arguments.len != target_block.parameters.len)
            {
                return null;
            }
            var selected_value: ?ir.ValueId = null;
            for (edge_.arguments, 0..) |argument, parameter_index| {
                if (argument != value_) continue;
                const mapped = try authenticatedBlockParameterEdgeValueAlloc(
                    allocator_,
                    program_,
                    analysis_,
                    source_,
                    edge_.target,
                    edge_,
                    incoming_,
                    closure_,
                    lineage_index_,
                    replay_index_,
                    replay_cache_,
                    parameter_index,
                ) orelse continue;
                if (selected_value) |existing| {
                    if (existing != mapped) return null;
                } else {
                    selected_value = mapped;
                }
            }
            return selected_value;
        }
    };

    switch (producer_block.terminator) {
        .jump => |edge| {
            if (try consider.edge(
                allocator,
                program,
                analysis,
                producer,
                edge,
                value_id,
                incoming,
                closure,
                lineage_index,
                replay_index,
                replay_cache,
            )) |mapped| selected = mapped;
        },
        .branch => |branch| for ([_]ir.Edge{ branch.then_edge, branch.else_edge }) |edge| {
            if (try consider.edge(
                allocator,
                program,
                analysis,
                producer,
                edge,
                value_id,
                incoming,
                closure,
                lineage_index,
                replay_index,
                replay_cache,
            )) |mapped| {
                if (selected) |existing| {
                    if (existing != mapped) return null;
                } else {
                    selected = mapped;
                }
            }
        },
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
    }
    return selected;
}

fn appendValueMapping(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    sources: *std.ArrayList(ir.ValueId),
    clones: *std.ArrayList(ir.ValueId),
    source: ir.ValueId,
    clone: ir.ValueId,
    allow_authenticated_alias: bool,
) std.mem.Allocator.Error!bool {
    for (sources.items, clones.items) |existing_source, existing_clone| {
        if (existing_source == source) return existing_clone == clone;
        if (source == clone and existing_clone == clone) return true;
        if (existing_clone == clone and !allow_authenticated_alias and !isRematerializableConstant(
            program,
            clone,
            if (clone.index() < program.values.len) program.values[clone.index()].function else return false,
        )) return false;
    }
    try sources.append(allocator, source);
    try clones.append(allocator, clone);
    return true;
}

// Distinct source values can denote one value at a clone boundary. Accept
// that convergence only when an existing replay-authenticated projection maps
// the source to this exact live edge value. This is intentionally evaluated
// only after the ordinary uniqueness check rejects the pair.
fn isAuthenticatedValueAliasAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    producer: ir.BlockId,
    source: ir.ValueId,
    mapped: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    if (source == mapped) return false;

    // A transparent carrier can sit immediately before a cloned producer.
    // Normalizing that carrier is correct for ordinary lineage lookup, but it
    // removes the exact edge on which the clone's block-parameter projection
    // is authenticated. Preserve that boundary proof for alias admission.
    const target_context = try findIncomingTargetCloneBlockParameterMappingAlloc(
        allocator,
        program,
        analysis,
        producer,
        source,
        incoming,
        lineage_index,
        replay_index,
        replay_cache,
    );
    if (!target_context.ambiguous and target_context.value != null and
        target_context.value.? == mapped)
    {
        return true;
    }

    const incoming_context = try findIncomingCloneLineageValueMappingAllocWithReplayCache(
        allocator,
        program,
        analysis,
        producer,
        source,
        incoming,
        lineage_index,
        replay_index,
        replay_cache,
    );
    if (!incoming_context.ambiguous and incoming_context.value != null and
        incoming_context.value.? == mapped)
    {
        return true;
    }

    const group_context = try findGroupContextValueMappingAlloc(
        allocator,
        program,
        analysis,
        source,
        incoming,
        lineage_index,
        replay_index,
        replay_cache,
    );
    if (!group_context.ambiguous and group_context.value != null and
        group_context.value.? == mapped)
    {
        return true;
    }

    // Distinct SSA results from a loop transition can also converge at a
    // re-entry boundary when the complete iteration-state proof selects this
    // exact live edge value.
    const context = try findAuthenticatedIterationStateResultMappingAlloc(
        allocator,
        program,
        analysis,
        source,
        incoming,
        lineage_index,
        replay_index,
        replay_cache,
        false,
    );
    return !context.ambiguous and context.value != null and context.value.? == mapped;
}

test "value alias convergence remains closed without authenticated proof" {
    const source_first = ir.ValueId.fromIndex(0);
    const source_second = ir.ValueId.fromIndex(1);
    const mapped = ir.ValueId.fromIndex(2);
    const program: ir.Program = .{
        .program_id = "unauthenticated-value-alias",
        .entry_function = ir.FunctionId.fromIndex(0),
        .functions = &.{},
        .blocks = &.{},
        .instructions = &.{},
        .values = &.{},
    };
    var sources: std.ArrayList(ir.ValueId) = .empty;
    defer sources.deinit(std.testing.allocator);
    var clones: std.ArrayList(ir.ValueId) = .empty;
    defer clones.deinit(std.testing.allocator);

    try std.testing.expect(try appendValueMapping(
        std.testing.allocator,
        &program,
        &sources,
        &clones,
        source_first,
        mapped,
        false,
    ));
    try std.testing.expect(!try appendValueMapping(
        std.testing.allocator,
        &program,
        &sources,
        &clones,
        source_second,
        mapped,
        false,
    ));
    try std.testing.expectEqual(@as(usize, 1), sources.items.len);
    try std.testing.expectEqual(@as(usize, 1), clones.items.len);
}

fn appendPackMapping(
    allocator: std.mem.Allocator,
    sources: *std.ArrayList(ir.ValuePackId),
    clones: *std.ArrayList(ir.ValuePackId),
    source: ir.ValuePackId,
    clone: ir.ValuePackId,
) std.mem.Allocator.Error!bool {
    for (sources.items, clones.items) |existing_source, existing_clone| {
        if (existing_source == source or existing_clone == clone) {
            return existing_source == source and existing_clone == clone;
        }
    }
    try sources.append(allocator, source);
    try clones.append(allocator, clone);
    return true;
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

fn cloneLineagePosition(program: *const ir.Program, block: ir.BlockId) ?CloneLineagePosition {
    return cloneLineagePositionCached(program, block, null);
}

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

fn cloneLineagesCompatible(
    program: *const ir.Program,
    left: ir.BlockId,
    right: ir.BlockId,
) bool {
    return cloneLineagesCompatibleCached(program, left, right, null);
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

test "clone context rejects a sibling lineage despite CFG reachability" {
    const function_id = ir.FunctionId.fromIndex(0);
    const root = ir.BlockId.fromIndex(0);
    const sibling = ir.BlockId.fromIndex(1);
    const selected = ir.BlockId.fromIndex(2);
    const descendant = ir.BlockId.fromIndex(3);
    const target = ir.BlockId.fromIndex(4);
    const blocks = [_]ir.Block{
        .{ .id = root, .function = function_id, .terminator = .{ .jump = .{ .target = sibling } } },
        .{ .id = sibling, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = selected, .function = function_id, .terminator = .{ .jump = .{ .target = descendant } } },
        .{ .id = descendant, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = root,
            .kind = .jump,
            .from = .{ .target = root },
            .to = .{ .target = sibling },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = root,
            .kind = .jump,
            .from = .{ .target = root },
            .to = .{ .target = selected },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = selected,
            .kind = .jump,
            .from = .{ .target = selected },
            .to = .{ .target = descendant },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(2),
        },
    };
    const program: ir.Program = .{
        .program_id = "clone-context-sibling-lineage",
        .entry_function = function_id,
        .functions = &.{.{
            .id = function_id,
            .blocks = &.{ root, sibling, selected, descendant, target },
            .entry_block = root,
        }},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    try std.testing.expect(!cloneLineagesCompatible(&program, descendant, sibling));
    try std.testing.expect(cloneLineagesCompatible(&program, descendant, selected));
}

test "clone context rejects unrelated roots despite CFG reachability" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const incoming_source = ir.BlockId.fromIndex(1);
    const producer = ir.BlockId.fromIndex(2);
    const candidate = ir.BlockId.fromIndex(3);
    const continuation = ir.BlockId.fromIndex(4);
    const exit = ir.BlockId.fromIndex(5);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = incoming_source },
            .else_edge = .{ .target = producer },
        } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{ .target = continuation } } },
        .{ .id = producer, .function = function_id, .terminator = .{ .jump = .{ .target = continuation } } },
        .{ .id = candidate, .function = function_id, .terminator = .{ .jump = .{ .target = continuation } } },
        .{ .id = continuation, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = candidate },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, incoming_source, producer, candidate, continuation, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = producer,
        .kind = .jump,
        .from = .{ .target = producer },
        .to = .{ .target = candidate },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "clone-context-unrelated-roots",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = incoming_source,
        .kind = .jump,
        .target = continuation,
    }};
    try std.testing.expect(try analysis.canReach(incoming_source, candidate));
    try std.testing.expect(try analysis.canReach(candidate, continuation));
    try std.testing.expect(!try cloneContextMatchesIncoming(&program, &analysis, candidate, &incoming));
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

test "external clone mapping rejects a closure-local producer without incoming context" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const producer_clone = ir.BlockId.fromIndex(2);
    const incoming_source = ir.BlockId.fromIndex(3);
    const closure_entry = ir.BlockId.fromIndex(4);
    const exit = ir.BlockId.fromIndex(5);
    const condition = ir.ValueId.fromIndex(0);
    const source_value = ir.ValueId.fromIndex(1);
    const clone_value = ir.ValueId.fromIndex(2);
    const exit_value = ir.ValueId.fromIndex(3);
    const rewrite_id = ir.EdgeRewriteId.fromIndex(0);
    const group_id = ir.NodeSplitGroupId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = producer },
            .else_edge = .{ .target = incoming_source },
        } } },
        .{ .id = producer, .function = function_id, .parameters = &.{source_value}, .terminator = .{ .jump = .{
            .target = producer_clone,
            .arguments = &.{source_value},
        } } },
        .{ .id = producer_clone, .function = function_id, .parameters = &.{clone_value}, .terminator = .{ .jump = .{
            .target = exit,
            .arguments = &.{clone_value},
        } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{ .target = closure_entry } } },
        .{ .id = closure_entry, .function = function_id, .terminator = .{ .jump = .{
            .target = exit,
            .arguments = &.{source_value},
        } } },
        .{ .id = exit, .function = function_id, .parameters = &.{exit_value}, .terminator = .{ .return_values = &.{exit_value} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, producer, producer_clone, incoming_source, closure_entry, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = source_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer, .index = 0 } } },
        .{ .id = clone_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer_clone, .index = 0 } } },
        .{ .id = exit_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = exit, .index = 0 } } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = rewrite_id,
        .source = entry,
        .kind = .branch_then,
        .from = .{ .target = producer },
        .to = .{ .target = producer_clone },
        .rule = .node_split,
        .node_split_group = group_id,
    }};
    const program: ir.Program = .{
        .program_id = "closure-local-producer-context",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = incoming_source,
        .kind = .jump,
        .target = closure_entry,
    }};
    const closure = [_]ir.BlockId{ producer_clone, closure_entry };

    var mappings = try collectExternalCloneMappingsAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        &closure,
        &incoming,
    );
    if (mappings) |*owned| owned.deinit();
    try std.testing.expect(mappings == null);
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

test "authenticated producer clone projects a block parameter from its incoming edge" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const incoming_source = ir.BlockId.fromIndex(2);
    const producer_clone = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const selector = ir.ValueId.fromIndex(0);
    const seed = ir.ValueId.fromIndex(1);
    const producer_value = ir.ValueId.fromIndex(2);
    const clone_value = ir.ValueId.fromIndex(3);
    const exit_value = ir.ValueId.fromIndex(4);

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = producer, .arguments = &.{seed} },
            .else_edge = .{ .target = incoming_source },
        } } },
        .{ .id = producer, .function = function_id, .parameters = &.{producer_value}, .terminator = .{ .jump = .{
            .target = exit,
            .arguments = &.{producer_value},
        } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{
            .target = producer_clone,
            .arguments = &.{seed},
        } } },
        .{ .id = producer_clone, .function = function_id, .parameters = &.{clone_value}, .terminator = .{ .jump = .{
            .target = exit,
            .arguments = &.{clone_value},
        } } },
        .{ .id = exit, .function = function_id, .parameters = &.{exit_value}, .terminator = .{ .return_values = &.{exit_value} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, seed },
        .blocks = &.{ entry, producer, incoming_source, producer_clone, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = seed, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = producer_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer, .index = 0 } } },
        .{ .id = clone_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer_clone, .index = 0 } } },
        .{ .id = exit_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = exit, .index = 0 } } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = incoming_source,
        .kind = .jump,
        .from = .{ .target = producer, .arguments = &.{seed} },
        .to = .{ .target = producer_clone, .arguments = &.{seed} },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    var program: ir.Program = .{
        .program_id = "authenticated-producer-parameter-projection",
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

    const incoming = [_]ir.CfgEdgeRef{.{
        .source = incoming_source,
        .kind = .jump,
        .target = producer_clone,
    }};
    const mapping = try findIncomingTargetCloneBlockParameterMappingAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        producer,
        producer_value,
        &incoming,
        &lineage_index,
        &replay_index,
        &replay_cache,
    );
    try std.testing.expect(!mapping.ambiguous);
    try std.testing.expect(mapping.value != null);
    try std.testing.expectEqual(seed, mapping.value.?);
    try std.testing.expectEqual(seed, (try findExistingValueCloneAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        producer,
        producer_value,
        &incoming,
        &.{producer_clone},
        &lineage_index,
        &replay_index,
        &replay_cache,
    )).?);

    var sources: std.ArrayList(ir.ValueId) = .empty;
    defer sources.deinit(std.testing.allocator);
    var clones: std.ArrayList(ir.ValueId) = .empty;
    defer clones.deinit(std.testing.allocator);
    try std.testing.expect(try appendValueMapping(
        std.testing.allocator,
        &program,
        &sources,
        &clones,
        selector,
        seed,
        false,
    ));
    try std.testing.expect(!try appendValueMapping(
        std.testing.allocator,
        &program,
        &sources,
        &clones,
        producer_value,
        seed,
        false,
    ));
    try std.testing.expect(try isAuthenticatedValueAliasAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        producer,
        producer_value,
        seed,
        &incoming,
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));
    try std.testing.expect(try appendValueMapping(
        std.testing.allocator,
        &program,
        &sources,
        &clones,
        producer_value,
        seed,
        true,
    ));
    try std.testing.expectEqualSlices(ir.ValueId, &.{ selector, producer_value }, sources.items);
    try std.testing.expectEqualSlices(ir.ValueId, &.{ seed, seed }, clones.items);

    var unauthenticated_program = program;
    unauthenticated_program.edge_rewrites = &.{};
    var unauthenticated_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &unauthenticated_program,
        functions[0],
    );
    defer unauthenticated_analysis.deinit();
    var unauthenticated_lineage = try CloneLineageIndex.init(
        std.testing.allocator,
        &unauthenticated_program,
    );
    defer unauthenticated_lineage.deinit();
    var unauthenticated_replay = try node_split.ReplayIndex.init(
        std.testing.allocator,
        &unauthenticated_program,
    );
    defer unauthenticated_replay.deinit();
    var unauthenticated_cache = ReplayCache.init(
        std.testing.allocator,
        &unauthenticated_program,
        &unauthenticated_replay,
    );
    defer unauthenticated_cache.deinit();
    const rejected = try findIncomingTargetCloneBlockParameterMappingAlloc(
        std.testing.allocator,
        &unauthenticated_program,
        &unauthenticated_analysis,
        producer,
        producer_value,
        &incoming,
        &unauthenticated_lineage,
        &unauthenticated_replay,
        &unauthenticated_cache,
    );
    try std.testing.expect(rejected.value == null);
    try std.testing.expect(!rejected.ambiguous);
    try std.testing.expect(!try isAuthenticatedValueAliasAlloc(
        std.testing.allocator,
        &unauthenticated_program,
        &unauthenticated_analysis,
        producer,
        producer_value,
        seed,
        &incoming,
        &unauthenticated_lineage,
        &unauthenticated_replay,
        &unauthenticated_cache,
    ));
}

test "authenticated producer clone forwards original parameters through zero-argument chain" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const incoming_source = ir.BlockId.fromIndex(2);
    const clone = ir.BlockId.fromIndex(3);
    const forward_first = ir.BlockId.fromIndex(4);
    const forward_second = ir.BlockId.fromIndex(5);
    const consumer = ir.BlockId.fromIndex(6);
    const exit = ir.BlockId.fromIndex(7);

    const owner_first = ir.ValueId.fromIndex(0);
    const owner_second = ir.ValueId.fromIndex(1);
    const owner_third = ir.ValueId.fromIndex(2);
    const owner_fourth = ir.ValueId.fromIndex(3);
    const selector = ir.ValueId.fromIndex(4);
    const producer_first = ir.ValueId.fromIndex(5);
    const producer_second = ir.ValueId.fromIndex(6);
    const producer_third = ir.ValueId.fromIndex(7);
    const producer_fourth = ir.ValueId.fromIndex(8);
    const clone_first = ir.ValueId.fromIndex(9);
    const clone_second = ir.ValueId.fromIndex(10);
    const clone_third = ir.ValueId.fromIndex(11);
    const clone_fourth = ir.ValueId.fromIndex(12);
    const consumer_first = ir.ValueId.fromIndex(13);
    const consumer_second = ir.ValueId.fromIndex(14);
    const consumer_third = ir.ValueId.fromIndex(15);
    const consumer_fourth = ir.ValueId.fromIndex(16);
    const owners = [_]ir.ValueId{ owner_first, owner_second, owner_third, owner_fourth };
    const producer_values = [_]ir.ValueId{ producer_first, producer_second, producer_third, producer_fourth };
    const clone_values = [_]ir.ValueId{ clone_first, clone_second, clone_third, clone_fourth };
    const consumer_values = [_]ir.ValueId{ consumer_first, consumer_second, consumer_third, consumer_fourth };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = producer, .arguments = owners[0..] },
            .else_edge = .{ .target = incoming_source },
        } } },
        .{ .id = producer, .function = function_id, .parameters = producer_values[0..], .terminator = .{ .return_values = &.{} } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{
            .target = clone,
            .arguments = owners[0..],
        } } },
        .{ .id = clone, .function = function_id, .parameters = clone_values[0..], .terminator = .{ .jump = .{ .target = forward_first } } },
        .{ .id = forward_first, .function = function_id, .terminator = .{ .jump = .{ .target = forward_second } } },
        .{ .id = forward_second, .function = function_id, .terminator = .{ .jump = .{
            .target = consumer,
            .arguments = producer_values[0..],
        } } },
        .{ .id = consumer, .function = function_id, .parameters = consumer_values[0..], .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, owner_first, owner_second, owner_third, owner_fourth },
        .blocks = &.{ entry, producer, incoming_source, clone, forward_first, forward_second, consumer, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = owner_first, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = owner_second, .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = owner_third, .function = function_id, .type = .integer, .origin = .{ .parameter = 3 } },
        .{ .id = owner_fourth, .function = function_id, .type = .integer, .origin = .{ .parameter = 4 } },
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = producer_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer, .index = 0 } } },
        .{ .id = producer_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer, .index = 1 } } },
        .{ .id = producer_third, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer, .index = 2 } } },
        .{ .id = producer_fourth, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer, .index = 3 } } },
        .{ .id = clone_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 0 } } },
        .{ .id = clone_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 1 } } },
        .{ .id = clone_third, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 2 } } },
        .{ .id = clone_fourth, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 3 } } },
        .{ .id = consumer_first, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = consumer, .index = 0 } } },
        .{ .id = consumer_second, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = consumer, .index = 1 } } },
        .{ .id = consumer_third, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = consumer, .index = 2 } } },
        .{ .id = consumer_fourth, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = consumer, .index = 3 } } },
    };
    const rewrite = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = incoming_source,
        .kind = .jump,
        .from = .{ .target = producer, .arguments = owners[0..] },
        .to = .{ .target = clone, .arguments = owners[0..] },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "authenticated-clone-forwarded-original-parameters",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrite,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = clone,
        .kind = .jump,
        .target = forward_first,
    }};
    var lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(std.testing.allocator, &program, &replay_index);
    defer replay_cache.deinit();

    try std.testing.expectEqual(
        clone_first,
        (try findExistingValueCloneAlloc(
            std.testing.allocator,
            &program,
            &analysis,
            producer,
            producer_first,
            &incoming,
            &.{ clone, forward_first, forward_second },
            &lineage_index,
            &replay_index,
            &replay_cache,
        )).?,
    );

    try std.testing.expect(try parameterizedContinuationBridge(
        std.testing.allocator,
        &program,
        &analysis,
        forward_second,
        0,
        consumer,
        exit,
        &.{ clone, forward_first, forward_second },
        &.{},
        &incoming,
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));

    var closure = [_]ir.BlockId{ clone, forward_first, forward_second };
    try std.testing.expect(prepareClosure(
        std.testing.allocator,
        &program,
        &analysis,
        closure[0..],
        &incoming,
    ));

    var tampered_rewrite = rewrite;
    tampered_rewrite[0].to.arguments = &.{ owner_first, selector, owner_third, owner_fourth };
    var tampered_program = program;
    tampered_program.edge_rewrites = &tampered_rewrite;
    var tampered_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &tampered_program,
        functions[0],
    );
    defer tampered_analysis.deinit();
    var tampered_lineage_index = try CloneLineageIndex.init(
        std.testing.allocator,
        &tampered_program,
    );
    defer tampered_lineage_index.deinit();
    var tampered_replay_index = try node_split.ReplayIndex.init(
        std.testing.allocator,
        &tampered_program,
    );
    defer tampered_replay_index.deinit();
    var tampered_replay_cache = ReplayCache.init(
        std.testing.allocator,
        &tampered_program,
        &tampered_replay_index,
    );
    defer tampered_replay_cache.deinit();
    try std.testing.expect(!try parameterizedContinuationBridge(
        std.testing.allocator,
        &tampered_program,
        &tampered_analysis,
        forward_second,
        0,
        consumer,
        exit,
        &closure,
        &.{},
        &incoming,
        &tampered_lineage_index,
        &tampered_replay_index,
        &tampered_replay_cache,
    ));
}

test "incoming-source definitions are not remapped through a downstream clone" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const closure = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const selector = ir.ValueId.fromIndex(0);
    const seed = ir.ValueId.fromIndex(1);
    const source_value = ir.ValueId.fromIndex(2);
    const clone_value = ir.ValueId.fromIndex(3);
    const exit_value = ir.ValueId.fromIndex(4);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = producer, .arguments = &.{seed} },
            .else_edge = .{ .target = clone, .arguments = &.{seed} },
        } } },
        .{ .id = producer, .function = function_id, .parameters = &.{source_value}, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = closure },
            .else_edge = .{ .target = clone, .arguments = &.{source_value} },
        } } },
        .{ .id = clone, .function = function_id, .parameters = &.{clone_value}, .terminator = .{ .jump = .{ .target = closure } } },
        .{ .id = closure, .function = function_id, .terminator = .{ .jump = .{ .target = exit, .arguments = &.{source_value} } } },
        .{ .id = exit, .function = function_id, .parameters = &.{exit_value}, .terminator = .{ .return_values = &.{exit_value} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, seed },
        .blocks = &.{ entry, producer, clone, closure, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = seed, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = source_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer, .index = 0 } } },
        .{ .id = clone_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 0 } } },
        .{ .id = exit_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = exit, .index = 0 } } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = entry,
        .kind = .branch_else,
        .from = .{ .target = producer, .arguments = &.{seed} },
        .to = .{ .target = clone, .arguments = &.{seed} },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    const program: ir.Program = .{
        .program_id = "incoming-source-definition-identity",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = producer,
        .kind = .branch_then,
        .target = closure,
    }};

    var mappings = (try collectExternalCloneMappingsAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        &.{closure},
        &incoming,
    )).?;
    defer mappings.deinit();
    try std.testing.expectEqualSlices(ir.ValueId, &.{source_value}, mappings.values);
    try std.testing.expectEqualSlices(ir.ValueId, &.{source_value}, mappings.clone_values);
}

test "nested clone context keeps distinct continuation edge arguments" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const sibling = ir.BlockId.fromIndex(2);
    const selected = ir.BlockId.fromIndex(3);
    const nested = ir.BlockId.fromIndex(4);
    const continuation = ir.BlockId.fromIndex(5);
    const exit = ir.BlockId.fromIndex(6);
    const selector = ir.ValueId.fromIndex(0);
    const seed = ir.ValueId.fromIndex(1);
    const producer_value = ir.ValueId.fromIndex(2);
    const sibling_value = ir.ValueId.fromIndex(3);
    const selected_value = ir.ValueId.fromIndex(4);
    const nested_value = ir.ValueId.fromIndex(5);
    const continuation_value = ir.ValueId.fromIndex(6);
    const exit_value = ir.ValueId.fromIndex(7);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = producer, .arguments = &.{seed} },
            .else_edge = .{ .target = sibling, .arguments = &.{seed} },
        } } },
        .{ .id = producer, .function = function_id, .parameters = &.{producer_value}, .terminator = .{ .jump = .{
            .target = selected,
            .arguments = &.{producer_value},
        } } },
        .{ .id = sibling, .function = function_id, .parameters = &.{sibling_value}, .terminator = .{ .jump = .{
            .target = nested,
            .arguments = &.{sibling_value},
        } } },
        .{ .id = selected, .function = function_id, .parameters = &.{selected_value}, .terminator = .{ .jump = .{
            .target = nested,
            .arguments = &.{selected_value},
        } } },
        .{ .id = nested, .function = function_id, .parameters = &.{nested_value}, .terminator = .{ .jump = .{
            .target = continuation,
            .arguments = &.{nested_value},
        } } },
        .{ .id = continuation, .function = function_id, .parameters = &.{continuation_value}, .terminator = .{ .jump = .{
            .target = exit,
            .arguments = &.{producer_value},
        } } },
        .{ .id = exit, .function = function_id, .parameters = &.{exit_value}, .terminator = .{ .return_values = &.{exit_value} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, seed },
        .blocks = &.{ entry, producer, sibling, selected, nested, continuation, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = seed, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = producer_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer, .index = 0 } } },
        .{ .id = sibling_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = sibling, .index = 0 } } },
        .{ .id = selected_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = selected, .index = 0 } } },
        .{ .id = nested_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = nested, .index = 0 } } },
        .{ .id = continuation_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = continuation, .index = 0 } } },
        .{ .id = exit_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = exit, .index = 0 } } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .branch_else,
            .from = .{ .target = producer, .arguments = &.{seed} },
            .to = .{ .target = sibling, .arguments = &.{seed} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = entry,
            .kind = .branch_then,
            .from = .{ .target = producer, .arguments = &.{seed} },
            .to = .{ .target = selected, .arguments = &.{seed} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(2),
            .source = selected,
            .kind = .jump,
            .from = .{ .target = selected, .arguments = &.{selected_value} },
            .to = .{ .target = nested, .arguments = &.{selected_value} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(2),
        },
    };
    const program: ir.Program = .{
        .program_id = "nested-clone-continuation-edge-context",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = nested,
        .kind = .jump,
        .target = continuation,
    }};

    try std.testing.expect(!try cloneContextMatchesIncoming(&program, &analysis, sibling, &incoming));
    try std.testing.expect(try cloneContextMatchesIncoming(&program, &analysis, selected, &incoming));

    const context = try findIncomingCloneLineageValueMappingAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        producer,
        producer_value,
        &incoming,
        null,
        null,
    );
    try std.testing.expect(!context.ambiguous);
    try std.testing.expectEqual(nested_value, context.value.?);

    var mappings = (try collectExternalCloneMappingsAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        &.{continuation},
        &incoming,
    )).?;
    defer mappings.deinit();
    try std.testing.expectEqualSlices(ir.ValueId, &.{producer_value}, mappings.values);
    try std.testing.expectEqualSlices(ir.ValueId, &.{nested_value}, mappings.clone_values);
}

test "composed clone mapping rejects unstable incoming lineage" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const clone_one = ir.BlockId.fromIndex(2);
    const clone_two = ir.BlockId.fromIndex(3);
    const continuation = ir.BlockId.fromIndex(4);
    const selector = ir.ValueId.fromIndex(0);
    const seed = ir.ValueId.fromIndex(1);
    const alternate = ir.ValueId.fromIndex(2);
    const source_value = ir.ValueId.fromIndex(3);
    const clone_one_value = ir.ValueId.fromIndex(4);
    const clone_two_value = ir.ValueId.fromIndex(5);
    const continuation_value = ir.ValueId.fromIndex(6);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = producer, .arguments = &.{seed} },
            .else_edge = .{ .target = clone_one, .arguments = &.{seed} },
        } } },
        .{ .id = producer, .function = function_id, .parameters = &.{source_value}, .terminator = .{ .jump = .{
            .target = continuation,
            .arguments = &.{source_value},
        } } },
        .{ .id = clone_one, .function = function_id, .parameters = &.{clone_one_value}, .terminator = .{ .jump = .{
            .target = clone_two,
            .arguments = &.{clone_one_value},
        } } },
        .{ .id = clone_two, .function = function_id, .parameters = &.{clone_two_value}, .terminator = .{ .jump = .{
            .target = continuation,
            .arguments = &.{clone_two_value},
        } } },
        .{ .id = continuation, .function = function_id, .parameters = &.{continuation_value}, .terminator = .{ .return_values = &.{continuation_value} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, seed, alternate },
        .blocks = &.{ entry, producer, clone_one, clone_two, continuation },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = seed, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = alternate, .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = source_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer, .index = 0 } } },
        .{ .id = clone_one_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone_one, .index = 0 } } },
        .{ .id = clone_two_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone_two, .index = 0 } } },
        .{ .id = continuation_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = continuation, .index = 0 } } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .branch_then,
            .from = .{ .target = producer, .arguments = &.{seed} },
            .to = .{ .target = clone_one, .arguments = &.{seed} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = clone_one,
            .kind = .jump,
            .from = .{ .target = clone_one, .arguments = &.{clone_one_value} },
            .to = .{ .target = clone_two, .arguments = &.{alternate} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
    };
    const program: ir.Program = .{
        .program_id = "unstable-composed-clone-context",
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
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = clone_two,
        .kind = .jump,
        .target = continuation,
    }};
    const mapping = try findIncomingCloneLineageValueMappingAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        producer,
        source_value,
        &incoming,
        &lineage_index,
        &replay_index,
    );
    try std.testing.expect(mapping.value == null);

    const authenticated_rewrites = [_]ir.CfgEdgeRewrite{
        rewrites[0],
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = clone_one,
            .kind = .jump,
            .from = .{ .target = clone_one, .arguments = &.{clone_one_value} },
            .to = .{ .target = clone_two, .arguments = &.{clone_two_value} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
    };
    var authenticated_program = program;
    authenticated_program.edge_rewrites = &authenticated_rewrites;
    var authenticated_lineage = try CloneLineageIndex.init(std.testing.allocator, &authenticated_program);
    defer authenticated_lineage.deinit();
    var authenticated_replay = try node_split.ReplayIndex.init(std.testing.allocator, &authenticated_program);
    defer authenticated_replay.deinit();
    const authenticated = try findIncomingCloneLineageValueMappingAlloc(
        std.testing.allocator,
        &authenticated_program,
        &analysis,
        producer,
        source_value,
        &incoming,
        &authenticated_lineage,
        &authenticated_replay,
    );
    try std.testing.expectEqual(clone_two_value, authenticated.value.?);
}

test "direct clone lookup rejects sibling mappings at a shared continuation" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const sibling = ir.BlockId.fromIndex(2);
    const continuation = ir.BlockId.fromIndex(3);
    const clone_a = ir.BlockId.fromIndex(4);
    const clone_b = ir.BlockId.fromIndex(5);
    const selector = ir.ValueId.fromIndex(0);
    const source_value = ir.ValueId.fromIndex(1);
    const clone_a_value = ir.ValueId.fromIndex(2);
    const clone_b_value = ir.ValueId.fromIndex(3);
    const continuation_value = ir.ValueId.fromIndex(4);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = producer, .arguments = &.{selector} },
            .else_edge = .{ .target = sibling },
        } } },
        .{ .id = producer, .function = function_id, .parameters = &.{source_value}, .terminator = .{ .jump = .{
            .target = continuation,
            .arguments = &.{source_value},
        } } },
        .{ .id = sibling, .function = function_id, .terminator = .{ .jump = .{ .target = continuation, .arguments = &.{selector} } } },
        .{ .id = continuation, .function = function_id, .parameters = &.{continuation_value}, .terminator = .{ .return_values = &.{} } },
        .{ .id = clone_a, .function = function_id, .parameters = &.{clone_a_value}, .terminator = .{ .return_values = &.{} } },
        .{ .id = clone_b, .function = function_id, .parameters = &.{clone_b_value}, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ entry, producer, sibling, continuation, clone_a, clone_b },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = source_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer, .index = 0 } } },
        .{ .id = clone_a_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone_a, .index = 0 } } },
        .{ .id = clone_b_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone_b, .index = 0 } } },
        .{ .id = continuation_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = continuation, .index = 0 } } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = entry,
            .kind = .branch_then,
            .from = .{ .target = producer, .arguments = &.{selector} },
            .to = .{ .target = clone_a, .arguments = &.{selector} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = entry,
            .kind = .branch_else,
            .from = .{ .target = producer, .arguments = &.{selector} },
            .to = .{ .target = clone_b, .arguments = &.{selector} },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
    };
    const program: ir.Program = .{
        .program_id = "direct-clone-sibling-ambiguity",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = sibling,
        .kind = .jump,
        .target = continuation,
    }};
    const closure = [_]ir.BlockId{ continuation, clone_a, clone_b };

    try std.testing.expect(directValueCloneForIncoming(
        &program,
        &analysis,
        producer,
        source_value,
        &incoming,
        &closure,
    ) == null);
}

fn cloneLineageAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.BlockId,
    clone: ir.BlockId,
) std.mem.Allocator.Error!?[]CloneLineageStep {
    return cloneLineageAllocCached(allocator, program, source, clone, null);
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

fn blockLineageContains(
    program: *const ir.Program,
    descendant: ir.BlockId,
    ancestor: ir.BlockId,
) bool {
    return blockLineageContainsCached(program, descendant, ancestor, null);
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

fn cloneContextMatchesIncoming(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    candidate: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
) std.mem.Allocator.Error!bool {
    return cloneContextMatchesIncomingCached(program, analysis, candidate, incoming, null);
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

fn cloneContextMatchesIncomingCached(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    candidate: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    index: ?*const CloneLineageIndex,
) std.mem.Allocator.Error!bool {
    return cloneContextMatchesIncomingWithReplayCached(
        null,
        program,
        analysis,
        candidate,
        incoming,
        index,
        null,
        null,
    );
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

fn cloneGroupMatchesIncomingContext(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    candidate: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
) std.mem.Allocator.Error!bool {
    return cloneGroupMatchesIncomingContextCached(program, analysis, candidate, incoming, null);
}

fn cloneGroupMatchesIncomingContextCached(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    candidate: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    index: ?*const CloneLineageIndex,
) std.mem.Allocator.Error!bool {
    const candidate_step = cloneStepForTargetCached(program, candidate, index) orelse return false;
    for (incoming) |reference| {
        const incoming_step = cloneStepForTargetCached(program, reference.source, index) orelse return false;
        if (incoming_step.group != candidate_step.group) return false;
    }
    if (incoming.len == 0) return false;
    return try cloneContextMatchesIncomingCached(program, analysis, candidate, incoming, index);
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

fn mapValueThroughCloneLineageAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.BlockId,
    clone: ir.BlockId,
    value: ir.ValueId,
) std.mem.Allocator.Error!?ir.ValueId {
    return mapValueThroughCloneLineageAllocCached(allocator, program, source, clone, value, null, null);
}

fn mapValueThroughCloneLineageAllocCached(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.BlockId,
    clone: ir.BlockId,
    value: ir.ValueId,
    index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
) std.mem.Allocator.Error!?ir.ValueId {
    return mapValueThroughCloneLineageAllocCachedWithReplayCache(
        allocator,
        program,
        source,
        clone,
        value,
        index,
        replay_index,
        null,
    );
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

fn mapPackThroughCloneLineageAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.BlockId,
    clone: ir.BlockId,
    pack: ir.ValuePackId,
) std.mem.Allocator.Error!?ir.ValuePackId {
    return mapPackThroughCloneLineageAllocCached(allocator, program, source, clone, pack, null, null);
}

fn mapPackThroughCloneLineageAllocCached(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.BlockId,
    clone: ir.BlockId,
    pack: ir.ValuePackId,
    index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
) std.mem.Allocator.Error!?ir.ValuePackId {
    return mapPackThroughCloneLineageAllocCachedWithReplayCache(
        allocator,
        program,
        source,
        clone,
        pack,
        index,
        replay_index,
        null,
    );
}

fn mapPackThroughCloneLineageAllocCachedWithReplayCache(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.BlockId,
    clone: ir.BlockId,
    pack: ir.ValuePackId,
    index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!?ir.ValuePackId {
    const lineage = try cloneLineageAllocCached(allocator, program, source, clone, index) orelse return null;
    defer allocator.free(lineage);
    var current = pack;
    for (lineage) |step| {
        const mapped = if (replay_cache) |cache| blk: {
            const replay = (try cache.get(step.source, step.clone, step.group)) orelse return null;
            break :blk mapPackFromReplay(program, step.source, step.clone, current, replay.*);
        } else blk: {
            var replay = if (replay_index) |cached|
                (try node_split.replayMappingsForCloneAllocWithIndex(allocator, program, cached, step.source, step.clone, step.group)) orelse return null
            else
                (try node_split.replayMappingsForCloneAlloc(allocator, program, step.source, step.clone, step.group)) orelse return null;
            defer replay.deinit();
            break :blk mapPackFromReplay(program, step.source, step.clone, current, replay);
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

/// Authenticate a split entry whose clone body was extended after the split.
/// This is intentionally weaker than ordinary clone replay: it proves only
/// the live rewrite, its stable incoming tuple, canonical parameter types,
/// and the mapped entry terminator. Callers must separately prove ownership
/// and replay the already-admitted effectful body.
pub fn hasAuthenticatedEffectfulEntryBridgeForEdge(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    reference: ir.CfgEdgeRef,
    expected_arguments: []const ir.ValueId,
) bool {
    if (!incomingEdgeIsCanonical(program, analysis, reference)) return false;
    const current_edge = cfg_edge.value(program, reference) orelse return false;
    if (!std.mem.eql(ir.ValueId, current_edge.arguments, expected_arguments)) return false;

    const clone = program.blocks[reference.target.index()];
    if (clone.instructions.len == 0) return false;

    var found = false;
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.rule != .node_split or rewrite.node_split_group == null or
            rewrite.source != reference.source or rewrite.kind != reference.kind or
            rewrite.to.target != reference.target or rewrite.from.target == rewrite.to.target)
        {
            continue;
        }
        if (found or !nodeSplitRewriteArgumentsAreStable(program, rewrite) or
            !activeNodeSplitRewrite(program, rewrite)) return false;

        const source = program.blocks[rewrite.from.target.index()];
        if (source.function != analysis.function.id or clone.function != source.function or
            source.instructions.len >= clone.instructions.len or
            !std.mem.eql(ir.ValueId, rewrite.to.arguments, expected_arguments) or
            !node_split.entryShapeMatches(program, source, clone)) return false;
        found = true;
    }
    return found;
}

// A clone lineage is only useful for an external value when the incoming
// predecessor actually carries the composed value into the closure. Lineage
// membership and CFG reachability alone are insufficient: sibling clones can
// both reach the same continuation while representing different edge
// arguments. Keep this proof at the boundary where the incoming edge is
// available, before candidate ranking is considered.
fn findIncomingCloneLineageValueMappingAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    producer: ir.BlockId,
    source_value: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
) std.mem.Allocator.Error!ContextualMapping {
    return findIncomingCloneLineageValueMappingAllocWithReplayCache(
        allocator,
        program,
        analysis,
        producer,
        source_value,
        incoming,
        lineage_index,
        replay_index,
        null,
    );
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

fn cloneCandidateIsMoreSpecific(
    program: *const ir.Program,
    candidate: ir.BlockId,
    existing: ir.BlockId,
) ?bool {
    return cloneCandidateIsMoreSpecificCached(program, candidate, existing, null);
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

fn isParameterlessForwardingBlock(
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
            .jump => |edge| edge.target.index() < program.blocks.len and
                analysis.blockIndex(edge.target) != null and
                program.blocks[edge.target.index()].function == block.function,
            .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => false,
        };
}

fn isAuthenticatedParameterlessForwardingBlock(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    block_id: ir.BlockId,
    closure: []const ir.BlockId,
    lineage_index: *const CloneLineageIndex,
) bool {
    if (closure.len != 1 or cloneStepForTargetCached(program, closure[0], lineage_index) == null) return false;
    return isParameterlessForwardingBlock(program, analysis, block_id);
}

fn iterationStateTupleTransition(
    program: *const ir.Program,
    arguments: []const ir.ValueId,
) ?IterationTransitionResult {
    if (arguments.len != 4 or !iteration_state.isBooleanLiteral(program, arguments[3], false)) return null;
    const transition = iterationTransitionResult(program, arguments[0]) orelse return null;
    if (iterationStateArgumentIndex(transition.instruction, transition.index) != 0 or
        !iteration_state.transitionStateMatches(program, transition.instruction, arguments))
    {
        return null;
    }
    return transition;
}

fn authenticatedIterationValuesEquivalentAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    expected: []const ir.ValueId,
    actual: []const ir.ValueId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    if (expected.len != actual.len) return false;
    for (expected, actual) |expected_value, actual_value| {
        if (try authenticatedComposedCloneValueMatchAlloc(
            allocator,
            program,
            expected_value,
            actual_value,
            lineage_index,
            replay_index,
            replay_cache,
        )) continue;

        // A loop may be cloned repeatedly through different split groups.
        // The changing SSA values are equivalent only when each producer has
        // a complete replay-authenticated lineage to the same root and both
        // values map back to that root's identical definition.
        if (!try authenticatedSameRootCloneValueMatchAlloc(
            allocator,
            program,
            expected_value,
            actual_value,
            lineage_index,
            replay_index,
            replay_cache,
        )) return false;
    }
    return true;
}

fn authenticatedSameRootCloneValueMatchAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    expected: ir.ValueId,
    actual: ir.ValueId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    if (expected == actual) return true;
    if (!sameContinuationValueType(program, expected, actual)) return false;

    const expected_producer = projectionValueProducer(program, expected) orelse return false;
    const actual_producer = projectionValueProducer(program, actual) orelse return false;
    const expected_position = cloneLineagePositionCached(program, expected_producer, lineage_index) orelse return false;
    const actual_position = cloneLineagePositionCached(program, actual_producer, lineage_index) orelse return false;
    if (expected_position.root != actual_position.root) return false;

    if (!cloneLineageArgumentsAreStableCached(program, expected_producer, lineage_index) or
        !cloneLineageArgumentsAreStableCached(program, actual_producer, lineage_index) or
        !try cloneLineageArgumentsMatchReplayCached(
            allocator,
            program,
            expected_position.root,
            expected_producer,
            lineage_index,
            replay_index,
            replay_cache,
        ) or
        !try cloneLineageArgumentsMatchReplayCached(
            allocator,
            program,
            actual_position.root,
            actual_producer,
            lineage_index,
            replay_index,
            replay_cache,
        )) return false;

    const expected_root = try mapValueBackThroughCloneLineageAllocCachedWithReplayCache(
        allocator,
        program,
        expected_position.root,
        expected_producer,
        expected,
        lineage_index,
        replay_index,
        replay_cache,
    ) orelse return false;
    const actual_root = try mapValueBackThroughCloneLineageAllocCachedWithReplayCache(
        allocator,
        program,
        actual_position.root,
        actual_producer,
        actual,
        lineage_index,
        replay_index,
        replay_cache,
    ) orelse return false;
    return expected_root == actual_root;
}

fn authenticatedIterationTransitionEquivalentAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    expected: IterationTransitionResult,
    actual: IterationTransitionResult,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    if (!sameIterationTransitionKind(expected.instruction, actual.instruction) or
        !std.meta.eql(expected.instruction.effects, actual.instruction.effects)) return false;

    const operands_match = switch (expected.instruction.operation) {
        .numeric_for_next => |expected_operation| switch (actual.instruction.operation) {
            .numeric_for_next => |actual_operation| try authenticatedIterationValuesEquivalentAlloc(
                allocator,
                program,
                &.{
                    expected_operation.control,
                    expected_operation.limit,
                    expected_operation.step,
                    expected_operation.initial,
                },
                &.{
                    actual_operation.control,
                    actual_operation.limit,
                    actual_operation.step,
                    actual_operation.initial,
                },
                lineage_index,
                replay_index,
                replay_cache,
            ),
            else => false,
        },
        .generic_for_next => |expected_operation| switch (actual.instruction.operation) {
            .generic_for_next => |actual_operation| try authenticatedIterationValuesEquivalentAlloc(
                allocator,
                program,
                &.{
                    expected_operation.iterator,
                    expected_operation.state,
                    expected_operation.control,
                    expected_operation.initial,
                },
                &.{
                    actual_operation.iterator,
                    actual_operation.state,
                    actual_operation.control,
                    actual_operation.initial,
                },
                lineage_index,
                replay_index,
                replay_cache,
            ),
            else => false,
        },
        else => false,
    };
    if (!operands_match) return false;

    return try authenticatedIterationValuesEquivalentAlloc(
        allocator,
        program,
        expected.instruction.results,
        actual.instruction.results,
        lineage_index,
        replay_index,
        replay_cache,
    );
}

// A context tuple may be produced by a compound continuation block rather
// than by a one-instruction loop header. Accept that tuple only when both
// entries are live, both are exact iteration-state tuples, and their complete
// transition inputs/results are authenticated through clone replay.
fn authenticatedIterationStateTupleEquivalentAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    target: ir.BlockId,
    expected: []const ir.ValueId,
    actual: []const ir.ValueId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    if (target.index() >= program.blocks.len) return false;
    const target_block = program.blocks[target.index()];
    if (target_block.id != target or target_block.parameters.len != expected.len or
        expected.len != actual.len or expected.len != 4 or
        !hasLiveIncomingEdgeWithArguments(program, target, expected) or
        !hasLiveIncomingEdgeWithArguments(program, target, actual)) return false;

    for (target_block.parameters, expected, actual) |formal, expected_value, actual_value| {
        if (!sameContinuationValueType(program, formal, expected_value) or
            !sameContinuationValueType(program, formal, actual_value)) return false;
    }

    const expected_transition = iterationStateTupleTransition(program, expected) orelse return false;
    const actual_transition = iterationStateTupleTransition(program, actual) orelse return false;
    var branch_match = true;
    if (expected_transition.block == actual_transition.block) {
        branch_match = std.meta.eql(expected_transition.instruction, actual_transition.instruction);
    } else if (!try authenticatedCloneBranchEquivalentAlloc(
        allocator,
        program,
        expected_transition.block,
        actual_transition.block,
        lineage_index,
        replay_index,
        replay_cache,
        0,
    )) {
        // Independent node-split groups can clone the same transition block
        // into sibling continuation contexts.  The strict branch proof above
        // intentionally rejects that shape because its final groups differ.
        // In this iteration-only contract, positional replay of every result
        // is the stronger identity proof: the transition kind, effects,
        // operands, and results are checked again below.  Do not use this
        // fallback for general value projection; it is limited to a complete
        // iteration-state tuple.
        branch_match = try authenticatedIterationValuesEquivalentAlloc(
            allocator,
            program,
            expected_transition.instruction.results,
            actual_transition.instruction.results,
            lineage_index,
            replay_index,
            replay_cache,
        );
    }
    if (!branch_match) {
        return false;
    }

    const transition_match = try authenticatedIterationTransitionEquivalentAlloc(
        allocator,
        program,
        expected_transition,
        actual_transition,
        lineage_index,
        replay_index,
        replay_cache,
    );
    return transition_match;
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

fn findExistingPackCloneAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    producer: ir.BlockId,
    source_pack: ir.ValuePackId,
    incoming: []const ir.CfgEdgeRef,
    _: []const ir.BlockId,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!?ir.ValuePackId {
    const group_context = try findGroupContextPackMappingAlloc(
        allocator,
        program,
        analysis,
        source_pack,
        incoming,
        lineage_index,
        replay_index,
        replay_cache,
    );
    if (group_context.ambiguous) return null;
    if (group_context.pack) |mapped| return mapped;

    var authenticated: ?ir.ValuePackId = null;
    var authenticated_candidate: ?ir.BlockId = null;
    var authenticated_rank: u8 = 0;
    var authenticated_ambiguous = false;
    var fallback: ?ir.ValuePackId = null;
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
        const dominated = definitionDominatesIncoming(analysis, candidate, incoming);
        if (context_rank == 0 and !dominated) continue;
        const clone_pack = try mapPackThroughCloneLineageAllocCachedWithReplayCache(
            allocator,
            program,
            producer,
            candidate,
            source_pack,
            lineage_index,
            replay_index,
            replay_cache,
        ) orelse continue;
        if (context_rank != 0) {
            const rank = context_rank;
            if (authenticated == null or rank > authenticated_rank) {
                authenticated = clone_pack;
                authenticated_candidate = candidate;
                authenticated_rank = rank;
                authenticated_ambiguous = false;
            } else if (rank == authenticated_rank) {
                const existing = authenticated.?;
                if (existing != clone_pack) {
                    const existing_candidate = authenticated_candidate orelse return null;
                    if (cloneCandidateIsMoreSpecificCached(program, candidate, existing_candidate, lineage_index)) |more_specific| {
                        if (more_specific) {
                            authenticated = clone_pack;
                            authenticated_candidate = candidate;
                        }
                    } else {
                        authenticated_ambiguous = true;
                    }
                }
            }
        } else if (fallback) |existing| {
            if (existing != clone_pack) fallback_ambiguous = true;
        } else fallback = clone_pack;
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

fn commonCloneAncestorCached(
    program: *const ir.Program,
    left: ir.BlockId,
    right: ir.BlockId,
    lineage_index: *const CloneLineageIndex,
) ?ir.BlockId {
    if (left.index() >= program.blocks.len or right.index() >= program.blocks.len or
        program.blocks[left.index()].function != program.blocks[right.index()].function)
    {
        return null;
    }
    const left_position = cloneLineagePositionCached(program, left, lineage_index) orelse return null;
    const right_position = cloneLineagePositionCached(program, right, lineage_index) orelse return null;
    if (left_position.root != right_position.root) return null;

    var left_current = left;
    var right_current = right;
    var left_depth = left_position.depth;
    var right_depth = right_position.depth;
    while (left_depth > right_depth) : (left_depth -= 1) {
        left_current = (cloneStepForTargetCached(program, left_current, lineage_index) orelse return null).source;
    }
    while (right_depth > left_depth) : (right_depth -= 1) {
        right_current = (cloneStepForTargetCached(program, right_current, lineage_index) orelse return null).source;
    }
    while (left_current != right_current) {
        left_current = (cloneStepForTargetCached(program, left_current, lineage_index) orelse return null).source;
        right_current = (cloneStepForTargetCached(program, right_current, lineage_index) orelse return null).source;
    }
    return left_current;
}

fn mapValueToReplay(
    program: *const ir.Program,
    source_block_id: ir.BlockId,
    clone_block_id: ir.BlockId,
    clone_value_id: ir.ValueId,
    replay: node_split.ReplayMappings,
) ?ir.ValueId {
    var selected: ?ir.ValueId = mapValueByCloneShape(
        program,
        clone_block_id,
        source_block_id,
        clone_value_id,
    );
    for (replay.clone_values, replay.source_values) |candidate_clone, candidate_source| {
        if (candidate_clone != clone_value_id) continue;
        if (selected) |existing| {
            if (existing != candidate_source) return null;
        } else {
            selected = candidate_source;
        }
    }
    return selected;
}

fn mapValueBackThroughCloneLineageAllocCachedWithReplayCache(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    ancestor: ir.BlockId,
    descendant: ir.BlockId,
    value: ir.ValueId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!?ir.ValueId {
    const lineage = try cloneLineageAllocCached(allocator, program, ancestor, descendant, lineage_index) orelse return null;
    defer allocator.free(lineage);

    var current = value;
    var index = lineage.len;
    while (index > 0) {
        index -= 1;
        const step = lineage[index];
        const replay = (try replay_cache.get(step.source, step.clone, step.group)) orelse return null;
        const mapped = mapValueToReplay(program, step.source, step.clone, current, replay.*) orelse return null;
        if (!sameContinuationValueType(program, current, mapped)) return null;
        current = mapped;
    }
    _ = replay_index;
    return current;
}

// Compare values produced in sibling clone branches by composing every
// authenticated positional map through their nearest common clone ancestor.
// The inverse walk is required because the expected value may be produced in
// a different branch from the actual value; a direct source-to-clone shape
// lookup cannot represent that composition.
fn authenticatedComposedCloneValueMatchAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    expected: ir.ValueId,
    actual: ir.ValueId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    if (expected == actual) return true;
    if (!sameContinuationValueType(program, expected, actual)) return false;
    const expected_producer = projectionValueProducer(program, expected) orelse return false;
    const actual_producer = projectionValueProducer(program, actual) orelse return false;
    if (expected_producer == actual_producer) return false;

    const ancestor = commonCloneAncestorCached(
        program,
        expected_producer,
        actual_producer,
        lineage_index,
    ) orelse return false;
    if (!try authenticatedCloneBranchEquivalentAlloc(
        allocator,
        program,
        expected_producer,
        actual_producer,
        lineage_index,
        replay_index,
        replay_cache,
        0,
    )) return false;
    if (!try cloneLineageArgumentsMatchReplayCached(
        allocator,
        program,
        ancestor,
        expected_producer,
        lineage_index,
        replay_index,
        replay_cache,
    ) or !try cloneLineageArgumentsMatchReplayCached(
        allocator,
        program,
        ancestor,
        actual_producer,
        lineage_index,
        replay_index,
        replay_cache,
    )) return false;

    const expected_root = try mapValueBackThroughCloneLineageAllocCachedWithReplayCache(
        allocator,
        program,
        ancestor,
        expected_producer,
        expected,
        lineage_index,
        replay_index,
        replay_cache,
    ) orelse return false;
    const actual_root = try mapValueBackThroughCloneLineageAllocCachedWithReplayCache(
        allocator,
        program,
        ancestor,
        actual_producer,
        actual,
        lineage_index,
        replay_index,
        replay_cache,
    ) orelse return false;
    if (expected_root != actual_root) return false;
    const mapped = try mapValueThroughCloneLineageAllocCachedWithReplayCache(
        allocator,
        program,
        ancestor,
        actual_producer,
        expected_root,
        lineage_index,
        replay_index,
        replay_cache,
    ) orelse return false;
    return mapped == actual and sameContinuationValueType(program, expected_root, mapped);
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

fn directValueCloneForIncoming(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    producer: ir.BlockId,
    source_value: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    closure: []const ir.BlockId,
) ?ir.ValueId {
    var selected: ?ir.ValueId = null;
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.rule != .node_split or rewrite.from.target != producer) continue;
        const candidate = rewrite.to.target;
        if (candidate == producer or candidate.index() >= program.blocks.len or
            analysis.blockIndex(candidate) == null or
            (!definitionDominatesIncoming(analysis, candidate, incoming) and !containsBlock(closure, candidate))) continue;
        if (mapValueByCloneShape(program, producer, candidate, source_value)) |clone_value| {
            if (selected) |existing| {
                // A direct lookup is only sound when every admissible clone
                // gives the same value.  Rewrite order is not semantic
                // evidence when sibling contexts reach the same continuation.
                if (existing != clone_value) return null;
            } else {
                selected = clone_value;
            }
        }
    }
    return selected;
}

fn directPackCloneForIncoming(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    producer: ir.BlockId,
    source_pack: ir.ValuePackId,
    incoming: []const ir.CfgEdgeRef,
    closure: []const ir.BlockId,
) ?ir.ValuePackId {
    var selected: ?ir.ValuePackId = null;
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.rule != .node_split or rewrite.from.target != producer) continue;
        const candidate = rewrite.to.target;
        if (candidate == producer or candidate.index() >= program.blocks.len or
            analysis.blockIndex(candidate) == null or
            (!definitionDominatesIncoming(analysis, candidate, incoming) and !containsBlock(closure, candidate))) continue;
        const source_block = program.blocks[producer.index()];
        const clone_block = program.blocks[candidate.index()];
        if (source_block.id != producer or clone_block.id != candidate or
            source_block.instructions.len != clone_block.instructions.len) continue;
        for (source_block.instructions, clone_block.instructions) |source_instruction_id, clone_instruction_id| {
            if (source_instruction_id.index() >= program.instructions.len or clone_instruction_id.index() >= program.instructions.len) continue;
            const source_instruction = program.instructions[source_instruction_id.index()];
            const clone_instruction = program.instructions[clone_instruction_id.index()];
            if (source_instruction.pack_result != source_pack) continue;
            const clone_pack = clone_instruction.pack_result orelse continue;
            if (clone_instruction.id == clone_instruction_id and clone_pack.index() < program.value_packs.len and
                program.value_packs[clone_pack.index()].id == clone_pack)
            {
                if (selected) |existing| {
                    // Keep pack identity deterministic across sibling clone
                    // contexts; the first rewrite must not win by accident.
                    if (existing != clone_pack) return null;
                } else {
                    selected = clone_pack;
                }
            }
        }
    }
    return selected;
}

fn mapPackFromReplay(
    program: *const ir.Program,
    source_block_id: ir.BlockId,
    clone_block_id: ir.BlockId,
    source_pack_id: ir.ValuePackId,
    replay: node_split.ReplayMappings,
) ?ir.ValuePackId {
    for (replay.source_packs, replay.clone_packs) |source_pack, clone_pack| {
        if (source_pack == source_pack_id) {
            return if (packReplayPairIsCompatible(program, source_pack, clone_pack)) clone_pack else null;
        }
    }
    if (source_block_id.index() >= program.blocks.len or clone_block_id.index() >= program.blocks.len) return null;
    const source_block = program.blocks[source_block_id.index()];
    const clone_block = program.blocks[clone_block_id.index()];
    if (source_block.id != source_block_id or clone_block.id != clone_block_id or
        source_block.function != clone_block.function)
    {
        return null;
    }
    for (source_block.instructions, 0..) |source_id, instruction_index| {
        if (source_id.index() >= program.instructions.len or instruction_index >= clone_block.instructions.len) return null;
        const source_instruction = program.instructions[source_id.index()];
        const clone_id = clone_block.instructions[instruction_index];
        if (source_instruction.id != source_id or clone_id.index() >= program.instructions.len) return null;
        const clone_instruction = program.instructions[clone_id.index()];
        if (source_instruction.pack_result != source_pack_id) continue;
        if (clone_instruction.id != clone_id) return null;
        const clone_pack_id = clone_instruction.pack_result orelse return null;
        if (clone_pack_id.index() >= program.value_packs.len) return null;
        const clone_pack = program.value_packs[clone_pack_id.index()];
        if (clone_pack.id != clone_pack_id or clone_pack.function != clone_block.function or
            !packReplayPairIsCompatible(program, source_pack_id, clone_pack_id)) return null;
        return clone_pack_id;
    }
    return null;
}

fn packReplayPairIsCompatible(
    program: *const ir.Program,
    source_pack_id: ir.ValuePackId,
    clone_pack_id: ir.ValuePackId,
) bool {
    if (source_pack_id.index() >= program.value_packs.len or clone_pack_id.index() >= program.value_packs.len) return false;
    const source = program.value_packs[source_pack_id.index()];
    const clone = program.value_packs[clone_pack_id.index()];
    if (source.id != source_pack_id or clone.id != clone_pack_id or source.function != clone.function) return false;
    if (source.shape.tail != clone.shape.tail or source.shape.prefix.len != clone.shape.prefix.len) return false;
    for (source.shape.prefix, clone.shape.prefix) |source_type, clone_type| {
        if (!std.meta.eql(source_type, clone_type)) return false;
    }
    return std.mem.eql(ir.EvidenceId, source.evidence, clone.evidence);
}

fn externalInstructionProducerBlock(
    program: *const ir.Program,
    function_id: ir.FunctionId,
    value_id: ir.ValueId,
    origin: anytype,
) ?ir.BlockId {
    if (origin.instruction.index() >= program.instructions.len) return null;
    const instruction = program.instructions[origin.instruction.index()];
    const result_index: usize = @intCast(origin.index);
    if (instruction.id != origin.instruction or instruction.block.index() >= program.blocks.len or
        program.blocks[instruction.block.index()].function != function_id or
        result_index >= instruction.results.len or instruction.results[result_index] != value_id)
    {
        return null;
    }
    return instruction.block;
}

fn externalPackProducerBlock(
    program: *const ir.Program,
    function_id: ir.FunctionId,
    pack_id: ir.ValuePackId,
    instruction_id: ir.InstructionId,
) ?ir.BlockId {
    if (instruction_id.index() >= program.instructions.len) return null;
    const instruction = program.instructions[instruction_id.index()];
    if (instruction.id != instruction_id or instruction.block.index() >= program.blocks.len or
        program.blocks[instruction.block.index()].function != function_id or instruction.pack_result != pack_id)
    {
        return null;
    }
    return instruction.block;
}

pub fn selectIterationConvergence(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    block: ir.BlockId,
    allowed: ?[]const bool,
) std.mem.Allocator.Error!?Selection {
    const branch = switch (analysis.program.blocks[block.index()].terminator) {
        .branch => |value| value,
        else => return null,
    };
    const then_distances = try forwardDistancesAlloc(
        allocator,
        analysis,
        branch.then_edge.target,
        null,
        allowed,
    ) orelse return null;
    defer allocator.free(then_distances);
    const else_distances = try forwardDistancesAlloc(
        allocator,
        analysis,
        branch.else_edge.target,
        null,
        allowed,
    ) orelse return null;
    defer allocator.free(else_distances);
    const distances: DistancePair = .{
        .then_distances = then_distances,
        .else_distances = else_distances,
    };
    var selected: ?Selection = null;
    for (analysis.function.blocks) |candidate| {
        if (!isIterationTransitionHeader(analysis.program, candidate)) continue;
        const then_distance = distanceAt(analysis, then_distances, candidate) orelse continue;
        const else_distance = distanceAt(analysis, else_distances, candidate) orelse continue;
        if (try analysis.immediateStructuralPostDominatorWithin(
            allocator,
            block,
            candidate,
            allowed,
        ) == null) continue;
        if (try convergenceIsBypassed(allocator, analysis, block, branch, candidate, allowed, distances)) continue;

        const current: Selection = .{
            .join = candidate,
            .then_distance = then_distance,
            .else_distance = else_distance,
        };
        if (selected == null or selectionLessThan(current, selected.?)) selected = current;
    }
    return selected;
}

fn selectOverlapConvergence(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    block: ir.BlockId,
) std.mem.Allocator.Error!?Selection {
    const branch = switch (analysis.program.blocks[block.index()].terminator) {
        .branch => |value| value,
        else => return null,
    };
    const then_distances = try forwardDistancesAlloc(
        allocator,
        analysis,
        branch.then_edge.target,
        null,
        null,
    ) orelse return null;
    defer allocator.free(then_distances);
    const else_distances = try forwardDistancesAlloc(
        allocator,
        analysis,
        branch.else_edge.target,
        null,
        null,
    ) orelse return null;
    defer allocator.free(else_distances);
    const distances: DistancePair = .{
        .then_distances = then_distances,
        .else_distances = else_distances,
    };
    var selected: ?Selection = null;
    for (analysis.function.blocks) |candidate| {
        if (!isIterationTransitionHeader(analysis.program, candidate)) {
            var membership = natural_loop.collect(allocator, analysis, candidate) catch |err| switch (err) {
                error.UnsupportedShape => continue,
                error.OutOfMemory => return error.OutOfMemory,
            } orelse continue;
            membership.deinit();
        }
        const then_distance = distanceAt(analysis, then_distances, candidate) orelse continue;
        const else_distance = distanceAt(analysis, else_distances, candidate) orelse continue;
        if (try analysis.immediateStructuralPostDominatorWithin(
            allocator,
            block,
            candidate,
            null,
        ) == null) continue;
        if (try convergenceIsBypassed(allocator, analysis, block, branch, candidate, null, distances)) continue;

        const current: Selection = .{
            .join = candidate,
            .then_distance = then_distance,
            .else_distance = else_distance,
        };
        if (selected == null or selectionLessThan(current, selected.?)) selected = current;
    }
    return selected;
}

pub fn findSplitAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
) std.mem.Allocator.Error!?Split {
    return findSplitAllocForFunction(allocator, program, null);
}

pub fn findSplitAllocForFunction(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    only_function: ?usize,
) std.mem.Allocator.Error!?Split {
    for (program.functions, 0..) |function, function_index| {
        if (only_function) |selected| if (function_index != selected) continue;
        var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
            error.InvalidCfg => continue,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer analysis.deinit();
        if (try findConditionalLoopEntrySplitAlloc(allocator, &analysis, function_index)) |split| return split;
        for (function.blocks) |block_id| {
            if (isIterationTransitionHeader(program, block_id)) continue;
            const branch = switch (program.blocks[block_id.index()].terminator) {
                .branch => |value| value,
                else => continue,
            };
            if (try analysis.canReach(branch.then_edge.target, block_id) or
                try analysis.canReach(branch.else_edge.target, block_id)) continue;
            if (try analysis.immediateConvergence(allocator, block_id, null) != null) continue;
            const selection = try selectOverlapConvergence(allocator, &analysis, block_id) orelse continue;
            const then_closure = try collectArmClosureAlloc(
                allocator,
                &analysis,
                branch.then_edge.target,
                selection.join,
            ) orelse continue;
            defer allocator.free(then_closure);
            const else_closure = try collectArmClosureAlloc(
                allocator,
                &analysis,
                branch.else_edge.target,
                selection.join,
            ) orelse continue;
            defer allocator.free(else_closure);
            const common = try commonClosureAlloc(allocator, program, &analysis, selection.join, then_closure, else_closure);
            var owns_common = true;
            defer if (owns_common) allocator.free(common);
            if (common.len == 0) continue;

            const use_then = then_closure.len < else_closure.len;
            const context = if (use_then) then_closure else else_closure;
            var boundary = (try collectBoundaryAlloc(allocator, program, context, common)) orelse continue;
            var owns_boundary = true;
            defer if (owns_boundary) boundary.deinit(allocator);

            if (!prepareClosure(allocator, program, &analysis, common, boundary.incoming)) continue;
            owns_common = false;
            owns_boundary = false;
            return .{
                .allocator = allocator,
                .function_index = function_index,
                .branch = block_id,
                .entry = boundary.entry,
                .join = selection.join,
                .incoming = boundary.incoming,
                .closure = common,
            };
        }
    }
    return null;
}

pub fn findContextualValueSplitAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    only_function: ?usize,
) std.mem.Allocator.Error!?Split {
    // Build the immutable rewrite indexes once for this scan. Each function
    // receives a scoped value view below, so ownership checks remain local
    // without repeating the complete block/rewrite history preprocessing.
    var global_lineage_index = try CloneLineageIndex.init(allocator, program);
    defer global_lineage_index.deinit();
    var global_replay_index = try node_split.ReplayIndex.init(allocator, program);
    defer global_replay_index.deinit();

    for (program.functions, 0..) |function, function_index| {
        if (only_function) |selected| if (function_index != selected) continue;
        var lineage_index = global_lineage_index;
        lineage_index.function_id = function.id;
        var replay_index = global_replay_index;
        replay_index.function_id = function.id;
        var replay_cache = ReplayCache.init(allocator, program, &replay_index);
        defer replay_cache.deinit();
        var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
            error.InvalidCfg => continue,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer analysis.deinit();

        for (function.blocks) |source_id| {
            if (!analysis.isReachable(source_id) or source_id.index() >= program.blocks.len) continue;
            const source = program.blocks[source_id.index()];
            switch (source.terminator) {
                .jump => |edge| {
                    if (try findContextualValueEdgeSplitAlloc(
                        allocator,
                        program,
                        &analysis,
                        function_index,
                        source_id,
                        .jump,
                        edge.target,
                        &lineage_index,
                        &replay_index,
                        &replay_cache,
                        null,
                        null,
                    )) |split| return split;
                },
                .branch => |branch| {
                    if (try findContextualValueEdgeSplitAlloc(
                        allocator,
                        program,
                        &analysis,
                        function_index,
                        source_id,
                        .branch_then,
                        branch.then_edge.target,
                        &lineage_index,
                        &replay_index,
                        &replay_cache,
                        null,
                        null,
                    )) |split| return split;
                    if (try findContextualValueEdgeSplitAlloc(
                        allocator,
                        program,
                        &analysis,
                        function_index,
                        source_id,
                        .branch_else,
                        branch.else_edge.target,
                        &lineage_index,
                        &replay_index,
                        &replay_cache,
                        null,
                        null,
                    )) |split| return split;
                },
                .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
            }
        }
    }
    return null;
}

pub fn findContextualValueSplitForIncomingAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function_index: usize,
    target: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    expected_parameters: ?[]const ir.ValueId,
) std.mem.Allocator.Error!?Split {
    if (function_index >= program.functions.len or incoming.len == 0) return null;
    var analysis = cfg.Analysis.init(allocator, program, program.functions[function_index]) catch |err| switch (err) {
        error.InvalidCfg => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    var replay_context = try ReplayProjectionContext.initForFunction(
        allocator,
        program,
        program.functions[function_index].id,
    );
    defer replay_context.deinit();
    return findContextualValueSplitForIncomingAllocWithReplayContext(
        allocator,
        program,
        &analysis,
        function_index,
        target,
        incoming,
        expected_parameters,
        &replay_context,
    );
}

/// Finds an incoming-context split while reusing the caller's immutable
/// function-scoped lineage and replay indexes.  Feedback normalization already
/// owns these indexes for the current function; rebuilding them here turns
/// repeated collision handling into a full history scan per candidate.
pub fn findContextualValueSplitForIncomingAllocWithReplayContext(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    function_index: usize,
    target: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    expected_parameters: ?[]const ir.ValueId,
    replay_context: *ReplayProjectionContext,
) std.mem.Allocator.Error!?Split {
    if (function_index >= program.functions.len or incoming.len == 0) return null;

    for (incoming) |reference| {
        if (reference.target != target) continue;
        if (try findContextualValueEdgeSplitAlloc(
            allocator,
            program,
            analysis,
            function_index,
            reference.source,
            reference.kind,
            reference.target,
            &replay_context.lineage_index,
            &replay_context.replay_index,
            &replay_context.replay_cache,
            expected_parameters,
            replay_context,
        )) |split| return split;
    }
    return null;
}

const ContextualValueUseDetector = struct {
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    incoming: ir.CfgEdgeRef,
    target: ir.BlockId,
    owned: []const ir.BlockId = &.{},
    found: bool = false,
    value_id: ?ir.ValueId = null,
    pack_id: ?ir.ValuePackId = null,

    pub fn value(self: *ContextualValueUseDetector, value_id: ir.ValueId) void {
        if (self.found) return;
        if (value_id.index() >= self.program.values.len) {
            self.found = true;
            return;
        }
        const producer = switch (self.program.values[value_id.index()].origin) {
            .parameter, .capture => return,
            .block_parameter => |origin| origin.block,
            .instruction_result => |origin| if (origin.instruction.index() < self.program.instructions.len)
                self.program.instructions[origin.instruction.index()].block
            else
                null,
        } orelse {
            self.found = true;
            return;
        };
        // A pure literal has no producer identity to preserve across a
        // contextual split.  Ignore it here so a rematerializable seed (for
        // example the initial nil/false tuple of an iteration) cannot mask a
        // later value that genuinely needs clone ownership proof.
        if (isRematerializableConstant(self.program, value_id, self.analysis.function.id)) return;
        if (producer == self.target or containsBlock(self.owned, producer) or
            !definitionDominatesIncoming(self.analysis, producer, &.{self.incoming})) return;
        self.found = true;
        self.value_id = value_id;
    }

    pub fn pack(self: *ContextualValueUseDetector, pack_id: ir.ValuePackId) void {
        if (self.found) return;
        const producer = packProducerBlock(self.program, pack_id) orelse return;
        if (producer == self.target or containsBlock(self.owned, producer) or
            !definitionDominatesIncoming(self.analysis, producer, &.{self.incoming})) return;
        self.found = true;
        self.pack_id = pack_id;
    }

    pub fn place(_: *ContextualValueUseDetector, _: ir.PlaceId) void {}
};

const DirectValueUseDetector = struct {
    target: ir.ValueId,
    found: bool = false,

    pub fn value(self: *DirectValueUseDetector, value_id: ir.ValueId) void {
        if (value_id == self.target) self.found = true;
    }

    pub fn pack(_: *DirectValueUseDetector, _: ir.ValuePackId) void {}
    pub fn place(_: *DirectValueUseDetector, _: ir.PlaceId) void {}
};

const DirectPackUseDetector = struct {
    target: ir.ValuePackId,
    found: bool = false,

    pub fn value(_: *DirectPackUseDetector, _: ir.ValueId) void {}

    pub fn pack(self: *DirectPackUseDetector, pack_id: ir.ValuePackId) void {
        if (pack_id == self.target) self.found = true;
    }

    pub fn place(_: *DirectPackUseDetector, _: ir.PlaceId) void {}
};

const BoundaryUseProjection = struct {
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    use_block: ir.BlockId,
    invalid: bool = false,
    producer: ?ir.BlockId = null,
    predecessor: ?ir.BlockId = null,

    pub fn value(self: *BoundaryUseProjection, value_id: ir.ValueId) void {
        if (self.invalid) return;
        const producer = projectionValueProducer(self.program, value_id) orelse return;
        if (!containsBlock(self.closure, producer)) return;

        if (!containsBlock(self.closure, self.use_block)) {
            if (!self.analysis.isReachable(self.use_block)) return;
            const clone_can_reach_use = self.analysis.canReach(producer, self.use_block) catch {
                self.invalid = true;
                self.producer = producer;
                return;
            };
            if (!self.analysis.dominates(producer, self.use_block) or clone_can_reach_use) {
                self.invalid = true;
                self.producer = producer;
            }
            return;
        }

        if (producer == self.use_block) return;
        var predecessor_index: usize = 0;
        while (predecessor_index < self.analysis.predecessorCount(self.use_block)) : (predecessor_index += 1) {
            const predecessor = self.analysis.predecessorAt(self.use_block, predecessor_index) orelse {
                self.invalid = true;
                return;
            };
            if (containsBlock(self.closure, predecessor)) continue;
            var selected_incoming = false;
            for (self.incoming) |reference| {
                if (reference.source == predecessor and reference.target == self.use_block) {
                    selected_incoming = true;
                    break;
                }
            }
            const clone_can_reach_predecessor = self.analysis.canReach(self.use_block, predecessor) catch {
                self.invalid = true;
                self.producer = producer;
                self.predecessor = predecessor;
                return;
            };
            if (selected_incoming or
                (self.analysis.dominates(producer, predecessor) and !clone_can_reach_predecessor)) continue;
            self.invalid = true;
            self.producer = producer;
            self.predecessor = predecessor;
            return;
        }
    }

    pub fn pack(_: *BoundaryUseProjection, _: ir.ValuePackId) void {}
    pub fn place(_: *BoundaryUseProjection, _: ir.PlaceId) void {}
};

// A closure-local definition cannot be left behind a shared predecessor.
// After the selected incoming edge is redirected, the clone owns the
// definition while the original consumer may remain reachable through that
// predecessor.  Reject the candidate before mutation unless the original
// definition already dominates that predecessor (or the predecessor is the
// selected boundary itself).  This is a generic boundary proof; it does not
// infer a value or weaken the post-apply availability gate.
fn closureLocalUsesHaveProjectedBoundary(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
) bool {
    if (closure.len == 0 or incoming.len == 0) return false;
    for (analysis.function.blocks) |block_id| {
        if (block_id.index() >= program.blocks.len) return false;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id or block.function != analysis.function.id) return false;
        var visitor = BoundaryUseProjection{
            .program = program,
            .analysis = analysis,
            .closure = closure,
            .incoming = incoming,
            .use_block = block_id,
        };
        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) return false;
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or instruction.block != block_id) return false;
            runtime_uses.visitOperationUses(instruction.operation, &visitor);
            if (visitor.invalid) break;
        }
        if (!visitor.invalid) runtime_uses.visitTerminatorUses(block.terminator, &visitor);
        if (!visitor.invalid) continue;
        traceStructural("structural_boundary_projection_reject use={} producer={} predecessor={?}\n", .{
            block_id.index(),
            if (visitor.producer) |producer| producer.index() else 0,
            if (visitor.predecessor) |predecessor| predecessor.index() else null,
        });
        return false;
    }
    return true;
}

// A node-split group can contain a pure carrier path that is not selected by
// the ordinary delayed-use walk.  If that path rejoins a closure-local value
// consumer, leaving it outside the clone would make the original consumer
// observe a definition owned by the new clone.  Expand only authenticated
// node-split carriers, including nested groups, and only when a bounded
// reverse search connects them to the existing closure.  This keeps replay
// evidence as the authority and does not turn arbitrary reachability into
// clone ownership.
fn appendAuthenticatedGroupCarrierPathAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure_entry: ir.BlockId,
    target: ir.BlockId,
    group: ir.NodeSplitGroupId,
    incoming: []const ir.CfgEdgeRef,
    membership: []bool,
    replay_index: *const node_split.ReplayIndex,
    expanded: *std.ArrayList(ir.BlockId),
) std.mem.Allocator.Error!bool {
    const target_index = analysis.blockIndex(target) orelse {
        std.debug.print("group_carrier_path_abort target={} reason=target_not_in_analysis\n", .{target.index()});
        return false;
    };
    if (membership[target_index]) return true;
    if (trace_structural_phases and replay_index.isAuthenticatedCloneBlock(program, target)) {
        traceStructural("group_carrier_candidate entry={} target={} group={} reachable={} canonical={}\n", .{
            closure_entry.index(),
            target.index(),
            group.index(),
            try analysis.canReach(closure_entry, target),
            node_split.parametersAreCanonical(program.values, program.blocks[target.index()]),
        });
    }
    if (target.index() >= program.blocks.len or
        program.blocks[target.index()].id != target or
        !node_split.parametersAreCanonical(program.values, program.blocks[target.index()]) or
        !replay_index.isAuthenticatedCloneBlock(program, target) or
        !try analysis.canReach(closure_entry, target))
    {
        return false;
    }

    const block_count = analysis.function.blocks.len;
    const seen = try allocator.alloc(bool, block_count);
    defer allocator.free(seen);
    const candidates = try allocator.alloc(bool, block_count);
    defer allocator.free(candidates);
    const connected = try allocator.alloc(bool, block_count);
    defer allocator.free(connected);
    const queue = try allocator.alloc(ir.BlockId, block_count);
    defer allocator.free(queue);
    @memset(seen, false);
    @memset(candidates, false);
    @memset(connected, false);

    var head: usize = 0;
    var tail: usize = 1;
    queue[0] = target;
    seen[target_index] = true;
    candidates[target_index] = true;
    var incoming_skips: usize = 0;
    var membership_joins: usize = 0;
    var seen_skips: usize = 0;
    var invalid_skips: usize = 0;
    var ownership_skips: usize = 0;
    while (head < tail) : (head += 1) {
        const current = queue[head];
        if (analysis.blockIndex(current) == null) {
            std.debug.print("group_carrier_path_abort target={} current={} reason=current_not_in_analysis\n", .{ target.index(), current.index() });
            return false;
        }
        var predecessor_index: usize = 0;
        while (analysis.predecessorAt(current, predecessor_index)) |predecessor| : (predecessor_index += 1) {
            var incoming_source = false;
            for (incoming) |reference| {
                if (reference.source == predecessor and reference.target == current) {
                    incoming_source = true;
                    break;
                }
            }
            if (incoming_source) {
                incoming_skips += 1;
                continue;
            }

            const predecessor_local_index = analysis.blockIndex(predecessor) orelse {
                std.debug.print("group_carrier_path_abort target={} current={} predecessor={} reason=predecessor_not_in_analysis\n", .{ target.index(), current.index(), predecessor.index() });
                return false;
            };
            if (membership[predecessor_local_index]) {
                membership_joins += 1;
                continue;
            }
            if (seen[predecessor_local_index]) {
                seen_skips += 1;
                continue;
            }
            if (predecessor.index() >= program.blocks.len or
                program.blocks[predecessor.index()].id != predecessor or
                !node_split.parametersAreCanonical(program.values, program.blocks[predecessor.index()]))
            {
                invalid_skips += 1;
                continue;
            }
            if (!replay_index.isAuthenticatedCloneBlock(program, predecessor)) {
                ownership_skips += 1;
                continue;
            }
            seen[predecessor_local_index] = true;
            candidates[predecessor_local_index] = true;
            if (tail >= queue.len) {
                std.debug.print("group_carrier_path_abort target={} current={} predecessor={} reason=queue_exhausted explored={} capacity={}\n", .{ target.index(), current.index(), predecessor.index(), tail, queue.len });
                return false;
            }
            queue[tail] = predecessor;
            tail += 1;
        }
    }

    // A target can have both a direct closure predecessor and an authenticated
    // carrier predecessor.  The old single-path search stopped at the first
    // closure predecessor and left the carrier outside the projected clone.
    // Mark candidate blocks that have at least one complete authenticated path
    // back to the selected boundary, then retain every connected candidate.
    var connected_changed = true;
    while (connected_changed) {
        connected_changed = false;
        var candidate_index: usize = 0;
        while (candidate_index < tail) : (candidate_index += 1) {
            const current = queue[candidate_index];
            const current_index = analysis.blockIndex(current) orelse return false;
            if (connected[current_index]) continue;
            var predecessor_index: usize = 0;
            while (analysis.predecessorAt(current, predecessor_index)) |predecessor| : (predecessor_index += 1) {
                var selected_incoming = false;
                for (incoming) |reference| {
                    if (reference.source == predecessor and reference.target == current) {
                        selected_incoming = true;
                        break;
                    }
                }
                if (selected_incoming) {
                    connected[current_index] = true;
                    connected_changed = true;
                    break;
                }
                const predecessor_local_index = analysis.blockIndex(predecessor) orelse return false;
                if (membership[predecessor_local_index] or
                    (candidates[predecessor_local_index] and connected[predecessor_local_index]))
                {
                    connected[current_index] = true;
                    connected_changed = true;
                    break;
                }
            }
        }
    }

    const connected_target_index = analysis.blockIndex(target) orelse return false;
    if (!connected[connected_target_index]) {
        traceStructural("group_carrier_path_not_found target={} group={} explored={} incoming_skips={} membership_joins={} seen_skips={} invalid_skips={} ownership_skips={}\n", .{
            target.index(),
            group.index(),
            tail,
            incoming_skips,
            membership_joins,
            seen_skips,
            invalid_skips,
            ownership_skips,
        });
        return false;
    }

    // A connected carrier path is still unsafe when one of its blocks has a
    // reachable predecessor outside the path.  That predecessor would keep
    // the original block reachable after the selected edge is redirected,
    // so accepting only the authenticated reverse path would manufacture a
    // clone-local value boundary.  Treat the whole candidate as a transaction
    // and leave membership untouched; a later candidate may still use the
    // existing closure without importing this incomplete path.
    var candidate_index: usize = 0;
    while (candidate_index < tail) : (candidate_index += 1) {
        const current = queue[candidate_index];
        const current_index = analysis.blockIndex(current) orelse return false;
        if (!connected[current_index] or membership[current_index]) continue;
        var predecessor_index: usize = 0;
        while (analysis.predecessorAt(current, predecessor_index)) |predecessor| : (predecessor_index += 1) {
            const predecessor_local_index = analysis.blockIndex(predecessor) orelse return false;
            if (membership[predecessor_local_index] or connected[predecessor_local_index]) continue;
            var selected_incoming = false;
            for (incoming) |reference| {
                if (reference.source == predecessor and reference.target == current) {
                    selected_incoming = true;
                    break;
                }
            }
            if (selected_incoming or !try analysis.canReach(closure_entry, predecessor)) continue;
            if (trace_structural_phases) {
                traceStructural("group_carrier_path_boundary_reject entry={} target={} block={} predecessor={} group={}\n", .{
                    closure_entry.index(),
                    target.index(),
                    current.index(),
                    predecessor.index(),
                    group.index(),
                });
            }
            return false;
        }
    }

    var path: std.ArrayList(ir.BlockId) = .empty;
    defer path.deinit(allocator);
    var queue_index = tail;
    while (queue_index != 0) {
        queue_index -= 1;
        const block_id = queue[queue_index];
        const block_index = analysis.blockIndex(block_id) orelse return false;
        if (!connected[block_index] or membership[block_index]) continue;
        membership[block_index] = true;
        try expanded.append(allocator, block_id);
        try path.append(allocator, block_id);
    }
    if (trace_structural_phases) {
        traceStructural("group_carrier_path entry={} target={} group={} added={any}\n", .{
            closure_entry.index(),
            target.index(),
            group.index(),
            path.items,
        });
    }
    return true;
}

fn extendAuthenticatedGroupBoundaryContextAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
) std.mem.Allocator.Error![]ir.BlockId {
    if (closure.len == 0 or incoming.len == 0) return closure;
    const entry = closure[0];
    const entry_step = cloneStepForTargetCached(program, entry, lineage_index) orelse {
        if (trace_structural_phases) traceStructural("group_projection_no_entry_lineage entry={} closure={}\n", .{ entry.index(), closure.len });
        return closure;
    };
    const group = entry_step.group;
    if (trace_structural_phases and closure.len >= 20) {
        traceStructural("group_projection_attempt entry={} closure={} group={}\n", .{ entry.index(), closure.len, group.index() });
    }
    const block_count = analysis.function.blocks.len;
    const membership = try allocator.alloc(bool, block_count);
    defer allocator.free(membership);
    @memset(membership, false);
    for (closure) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return closure;
        if (local_index >= membership.len or membership[local_index]) return closure;
        membership[local_index] = true;
    }

    var expanded: std.ArrayList(ir.BlockId) = .empty;
    errdefer expanded.deinit(allocator);
    try expanded.appendSlice(allocator, closure);
    var changed = false;

    // Resolve a directly observed closure-local use before walking the wider
    // authenticated carrier frontier.  The broad walk can encounter an
    // unrelated unowned ingress first and conservatively roll back, even
    // though the use's own predecessor has an authenticated carrier path.
    // Keep the unowned-ingress rejection intact; only prioritize the
    // authenticated boundary that the current closure already proves.
    while (true) {
        var projected_boundary = false;
        for (analysis.function.blocks) |block_id| {
            if (block_id.index() >= program.blocks.len) return closure;
            const block = program.blocks[block_id.index()];
            if (block.id != block_id or block.function != analysis.function.id) return closure;
            var visitor = BoundaryUseProjection{
                .program = program,
                .analysis = analysis,
                .closure = expanded.items,
                .incoming = incoming,
                .use_block = block_id,
            };
            for (block.instructions) |instruction_id| {
                if (instruction_id.index() >= program.instructions.len) return closure;
                const instruction = program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or instruction.block != block_id) return closure;
                runtime_uses.visitOperationUses(instruction.operation, &visitor);
                if (visitor.invalid) break;
            }
            if (!visitor.invalid) runtime_uses.visitTerminatorUses(block.terminator, &visitor);
            if (visitor.invalid) {
                if (visitor.predecessor) |predecessor| {
                    if (!try appendAuthenticatedGroupCarrierPathAlloc(
                        allocator,
                        program,
                        analysis,
                        entry,
                        predecessor,
                        group,
                        incoming,
                        membership,
                        replay_index,
                        &expanded,
                    )) continue;
                    changed = true;
                    projected_boundary = true;
                    break;
                }
            }
        }
        if (!projected_boundary) break;
    }

    while (true) {
        // An authenticated carrier can re-enter the projected closure through an
        // interior block rather than through the selected entry.  Leaving that
        // ingress outside would keep the original suffix reachable with a
        // closure-local value after the selected edge is cloned.  Admit only
        // reachable, authenticated group blocks; the membership bitset keeps
        // this closure expansion bounded by the function CFG.
        const Ingress = struct { source: ir.BlockId, target: ir.BlockId };
        var accepted_ingress: ?Ingress = null;
        var blocked_ingress = false;
        for (expanded.items) |block_id| {
            var predecessor_index: usize = 0;
            while (analysis.predecessorAt(block_id, predecessor_index)) |predecessor| : (predecessor_index += 1) {
                const predecessor_local_index = analysis.blockIndex(predecessor) orelse return closure;
                if (membership[predecessor_local_index]) continue;
                var selected_incoming = false;
                for (incoming) |reference| {
                    if (reference.source == predecessor and reference.target == block_id) {
                        selected_incoming = true;
                        break;
                    }
                }
                if (selected_incoming or
                    !replay_index.isAuthenticatedCloneBlock(program, predecessor) or
                    !try analysis.canReach(entry, predecessor)) continue;
                const boundary: Ingress = .{
                    .source = predecessor,
                    .target = block_id,
                };
                if (!try appendAuthenticatedGroupCarrierPathAlloc(
                    allocator,
                    program,
                    analysis,
                    entry,
                    boundary.source,
                    group,
                    incoming,
                    membership,
                    replay_index,
                    &expanded,
                )) {
                    if (trace_structural_phases and expanded.items.len >= 20) {
                        traceStructural("group_projection_ingress_reject source={} target={} closure={} group={}\n", .{
                            boundary.source.index(),
                            boundary.target.index(),
                            expanded.items.len,
                            group.index(),
                        });
                    }
                    // Stop the broad walk at an unconnectable ingress.  The
                    // targeted boundary pass below can still project a direct
                    // closure-local carrier without importing later siblings.
                    blocked_ingress = true;
                    break;
                }
                accepted_ingress = boundary;
                break;
            }
            if (accepted_ingress != null or blocked_ingress) break;
        }
        if (accepted_ingress) |boundary| {
            changed = true;
            if (trace_structural_phases and expanded.items.len >= 20) {
                traceStructural("group_projection_ingress_accept source={} target={} closure={} group={}\n", .{
                    boundary.source.index(),
                    boundary.target.index(),
                    expanded.items.len,
                    group.index(),
                });
            }
            continue;
        }

        var boundary: ?struct { predecessor: ir.BlockId } = null;
        var external_target_added = false;
        for (analysis.function.blocks) |block_id| {
            if (block_id.index() >= program.blocks.len) return closure;
            const block = program.blocks[block_id.index()];
            if (block.id != block_id or block.function != analysis.function.id) return closure;
            var visitor = BoundaryUseProjection{
                .program = program,
                .analysis = analysis,
                .closure = expanded.items,
                .incoming = incoming,
                .use_block = block_id,
            };
            for (block.instructions) |instruction_id| {
                if (instruction_id.index() >= program.instructions.len) return closure;
                const instruction = program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or instruction.block != block_id) return closure;
                runtime_uses.visitOperationUses(instruction.operation, &visitor);
                if (visitor.invalid) break;
            }
            if (!visitor.invalid) runtime_uses.visitTerminatorUses(block.terminator, &visitor);
            if (visitor.invalid) {
                if (visitor.predecessor) |predecessor| {
                    if (trace_structural_phases and expanded.items.len >= 20) {
                        traceStructural("group_projection_boundary use={} producer={?d} predecessor={} closure={} owned={}\n", .{
                            block_id.index(),
                            if (visitor.producer) |producer| producer.index() else null,
                            predecessor.index(),
                            expanded.items.len,
                            replay_index.isAuthenticatedCloneBlock(program, predecessor),
                        });
                    }
                    boundary = .{ .predecessor = predecessor };
                    break;
                }
                // An external consumer can itself be an authenticated clone
                // reached through a nested group.  Project that complete
                // carrier path before rejecting the closure; an unauthenticated
                // shared consumer remains a hard boundary.
                if (visitor.producer) |producer| {
                    const producer_reaches_use = analysis.canReach(producer, block_id) catch false;
                    if (replay_index.isAuthenticatedCloneBlock(program, block_id) and
                        producer_reaches_use and
                        try appendAuthenticatedGroupCarrierPathAlloc(
                            allocator,
                            program,
                            analysis,
                            entry,
                            block_id,
                            group,
                            incoming,
                            membership,
                            replay_index,
                            &expanded,
                        ))
                    {
                        changed = true;
                        external_target_added = true;
                        if (trace_structural_phases and expanded.items.len >= 20) {
                            traceStructural("group_projection_external_accept use={} producer={} closure={} group={}\n", .{
                                block_id.index(),
                                producer.index(),
                                expanded.items.len,
                                group.index(),
                            });
                        }
                        break;
                    }
                }
                if (trace_structural_phases and expanded.items.len >= 20) {
                    traceStructural("group_projection_unexpandable use={} producer={?d} closure={}\n", .{
                        block_id.index(),
                        if (visitor.producer) |producer| producer.index() else null,
                        expanded.items.len,
                    });
                }
                // A failed external projection may be an unrelated consumer.
                // Keep searching for an authenticated carrier that reconnects
                // to the selected closure; the final value-boundary proof still
                // rejects any closure-local use left unprojected.
                continue;
            }
        }
        if (external_target_added) continue;
        // A failed sibling ingress must remain a hard boundary, but it must
        // not hide an independently authenticated external consumer.  The
        // latter may provide the only complete carrier path for a closure
        // value; scan it before abandoning the projection.  Never fall
        // through to the ordinary predecessor boundary after this point.
        if (blocked_ingress) break;
        const selected = boundary orelse break;
        if (!try appendAuthenticatedGroupCarrierPathAlloc(
            allocator,
            program,
            analysis,
            entry,
            selected.predecessor,
            group,
            incoming,
            membership,
            replay_index,
            &expanded,
        )) {
            if (trace_structural_phases and expanded.items.len >= 20) {
                traceStructural("group_projection_path_reject predecessor={} closure={} group={}\n", .{
                    selected.predecessor.index(),
                    expanded.items.len,
                    group.index(),
                });
            }
            expanded.deinit(allocator);
            return closure;
        }
        changed = true;
    }
    if (!changed) {
        expanded.deinit(allocator);
        return closure;
    }
    const owned = try expanded.toOwnedSlice(allocator);
    if (trace_structural_phases) {
        traceStructural("group_projection_accept entry={} before={} after={} group={}\n", .{
            entry.index(),
            closure.len,
            owned.len,
            group.index(),
        });
    }
    allocator.free(closure);
    return owned;
}

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

fn findGroupContextPackMappingAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source_pack: ir.ValuePackId,
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
            var detector = DirectPackUseDetector{ .target = source_pack };
            for (source_block.instructions) |instruction_id| {
                if (instruction_id.index() >= program.instructions.len) continue;
                runtime_uses.visitOperationUses(program.instructions[instruction_id.index()].operation, &detector);
            }
            runtime_uses.visitTerminatorUses(source_block.terminator, &detector);
            if (!detector.found) continue;
            const mapped = if (replay_cache) |cache| blk: {
                const replay = (try cache.get(source_id, clone_id, incoming_step.group)) orelse continue;
                if (!nodeSplitRewriteArgumentsMatchReplay(program, rewrite, replay.*)) continue;
                break :blk mapPackFromReplay(program, source_id, clone_id, source_pack, replay.*);
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
                break :blk mapPackFromReplay(program, source_id, clone_id, source_pack, replay);
            };
            const mapped_pack = mapped orelse continue;
            if (result.pack) |existing| {
                if (existing != mapped_pack) result.ambiguous = true;
            } else {
                result.pack = mapped_pack;
            }
        }
    }
    return result;
}

fn findContextualValueEdgeSplitAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    function_index: usize,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    target: ir.BlockId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
    expected_parameters: ?[]const ir.ValueId,
    replay_context: ?*ReplayProjectionContext,
) std.mem.Allocator.Error!?Split {
    if (function_index >= program.functions.len or target.index() >= program.blocks.len or
        program.blocks[target.index()].function != analysis.function.id or !analysis.isReachable(target)) return null;
    const incoming: ir.CfgEdgeRef = .{ .source = source, .kind = kind, .target = target };
    const edge = cfg_edge: {
        const source_block = program.blocks[source.index()];
        break :cfg_edge switch (kind) {
            .jump => switch (source_block.terminator) {
                .jump => |edge| if (edge.target == target) edge else return null,
                else => return null,
            },
            .branch_then => switch (source_block.terminator) {
                .branch => |branch| if (branch.then_edge.target == target) branch.then_edge else return null,
                else => return null,
            },
            .branch_else => switch (source_block.terminator) {
                .branch => |branch| if (branch.else_edge.target == target) branch.else_edge else return null,
                else => return null,
            },
        };
    };
    if (!analysis.isReachable(source)) return null;

    const incoming_edges = [_]ir.CfgEdgeRef{incoming};
    var authenticated_parameters = false;
    if (expected_parameters) |expected| {
        switch (try authenticatedComposedParameterProjectionAlloc(
            allocator,
            program,
            target,
            expected,
            edge.arguments,
            lineage_index,
            replay_index,
            replay_cache,
        )) {
            .matched => authenticated_parameters = true,
            .rejected, .not_applicable => {},
        }
        if (!authenticated_parameters) {
            authenticated_parameters = try hasAuthenticatedIterationContextualProjectionAlloc(
                allocator,
                program,
                analysis,
                target,
                incoming,
                expected,
                lineage_index,
                replay_index,
                replay_cache,
            );
        }
        if (!authenticated_parameters and expected.len == 1) {
            if (replay_context) |context| {
                authenticated_parameters = try context.hasAuthenticatedOneParameterContinuationForEdge(
                    analysis,
                    incoming,
                    expected,
                );
            }
        }
    }
    // Internal members of an authenticated clone group intentionally have no
    // independent visit context.  When one of those members is reached by a
    // direct split edge, use the edge's complete one-parameter tuple as the
    // proof subject.  The helper still requires replayed lineage, identical
    // effects and operation semantics, and an authenticated successor, so an
    // absent owner context cannot be replaced by value equality alone.
    if (!authenticated_parameters and expected_parameters == null and edge.arguments.len == 1) {
        if (replay_context) |context| {
            authenticated_parameters = try context.hasAuthenticatedOneParameterContinuationForEdge(
                analysis,
                incoming,
                edge.arguments,
            );
        }
    }

    // A parameterized contextual entry may be fully self-contained: its
    // formal tuple is consumed by the entry's own effect before a shared
    // successor.  Keep that authenticated boundary local instead of
    // expanding through a surrounding SCC and importing unrelated producers.
    if (authenticated_parameters and program.blocks[target.index()].parameters.len != 0) {
        const minimal = try allocator.dupe(ir.BlockId, &.{target});
        const prepared = if (replay_context) |context|
            prepareClosureWithReplayContext(
                allocator,
                program,
                analysis,
                minimal,
                &incoming_edges,
                context,
            )
        else
            prepareClosure(allocator, program, analysis, minimal, &incoming_edges);
        if (prepared) {
            traceStructural("contextual_candidate_parameterized_minimal_boundary target={} source={}\n", .{
                target.index(),
                source.index(),
            });
            return .{
                .allocator = allocator,
                .function_index = function_index,
                .branch = source,
                .entry = target,
                .join = target,
                .incoming = try allocator.dupe(ir.CfgEdgeRef, &incoming_edges),
                .closure = minimal,
            };
        }
        allocator.free(minimal);
    }

    var closure = try allocator.dupe(ir.BlockId, &.{target});
    var retain_closure = false;
    defer if (!retain_closure) allocator.free(closure);

    // A shared target can be a forwarding block with no local use.  Let the
    // existing authenticated continuation analysis discover a contextual use
    // downstream before rejecting the split for lack of a distinct mapping.
    // The extension remains constrained by canonical edge arguments, replay
    // lineage, and the same cloneability checks used by collision splitting.
    closure = try extendContinuationClosureAlloc(
        allocator,
        program,
        analysis,
        target,
        closure,
        &incoming_edges,
    );
    const boundary_closure = try trimIncomingSourceClosureAlloc(
        allocator,
        analysis,
        target,
        closure,
        &incoming_edges,
    ) orelse return null;
    if (boundary_closure.ptr != closure.ptr or boundary_closure.len != closure.len) {
        traceStructural("contextual_candidate_source_boundary target={} closure_before={} closure_after={}\n", .{
            target.index(),
            closure.len,
            boundary_closure.len,
        });
    }
    closure = boundary_closure;

    closure = try extendAuthenticatedGroupBoundaryContextAlloc(
        allocator,
        program,
        analysis,
        closure,
        &incoming_edges,
        lineage_index,
        replay_index,
    );

    if (!closureLocalUsesHaveProjectedBoundary(program, analysis, closure, &incoming_edges)) {
        traceStructural("contextual_candidate_boundary_projection_rejected target={} closure={}\n", .{
            target.index(),
            closure.len,
        });
        return null;
    }

    var detector = ContextualValueUseDetector{
        .program = program,
        .analysis = analysis,
        .incoming = incoming,
        .target = target,
        .owned = closure,
    };
    for (closure) |block_id| {
        if (block_id.index() >= program.blocks.len) return null;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id or block.function != analysis.function.id) return null;
        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) return null;
            runtime_uses.visitOperationUses(program.instructions[instruction_id.index()].operation, &detector);
            if (detector.found) break;
        }
        if (!detector.found) runtime_uses.visitTerminatorUses(block.terminator, &detector);
        if (detector.found) break;
    }
    if (!detector.found and !authenticated_parameters) return null;

    traceStructural("contextual_candidate source={} target={} kind={s} closure={} value={?d} pack={?d}\n", .{
        source.index(),
        target.index(),
        @tagName(kind),
        closure.len,
        if (detector.value_id) |value_id| value_id.index() else null,
        if (detector.pack_id) |pack_id| pack_id.index() else null,
    });

    if (detector.value_id) |value_id| {
        const producer = switch (program.values[value_id.index()].origin) {
            .block_parameter => |origin| origin.block,
            .instruction_result => |origin| if (origin.instruction.index() < program.instructions.len)
                program.instructions[origin.instruction.index()].block
            else
                return null,
            .parameter, .capture => return null,
        };
        const authenticated = try findExistingValueCloneAlloc(
            allocator,
            program,
            analysis,
            producer,
            value_id,
            &incoming_edges,
            closure[0..],
            lineage_index,
            replay_index,
            replay_cache,
        );
        if (authenticated == null and !definitionDominatesIncoming(analysis, producer, &incoming_edges)) {
            traceStructural("contextual_candidate_no_authenticated_clone producer={} value={} target={}\n", .{ producer.index(), value_id.index(), target.index() });
            return null;
        }
    } else if (detector.pack_id) |pack_id| {
        const producer = switch (program.value_packs[pack_id.index()].origin) {
            .instruction_result => |instruction_id| if (instruction_id.index() < program.instructions.len)
                program.instructions[instruction_id.index()].block
            else
                return null,
            .varargs => return null,
        };
        const authenticated = try findExistingPackCloneAlloc(
            allocator,
            program,
            analysis,
            producer,
            pack_id,
            &incoming_edges,
            closure[0..],
            lineage_index,
            replay_index,
            replay_cache,
        );
        if (authenticated == null and !definitionDominatesIncoming(analysis, producer, &incoming_edges)) {
            traceStructural("contextual_candidate_no_authenticated_pack producer={} pack={} target={}\n", .{ producer.index(), pack_id.index(), target.index() });
            return null;
        }
    } else if (!authenticated_parameters) return null;
    const external_result = collectExternalCloneMappingsAllocWithReplayState(
        allocator,
        program,
        analysis,
        closure,
        &incoming_edges,
        lineage_index,
        replay_index,
        replay_cache,
    ) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
    };
    var external = external_result orelse {
        traceStructural("contextual_candidate_external_failure target={}\n", .{target.index()});
        return null;
    };
    defer external.deinit();
    const distinct_external_mapping = hasDistinctExternalCloneMapping(external);
    if (!distinct_external_mapping) {
        // A contextual value can be semantically available without a clone
        // mapping when its producer dominates the live incoming edge.  The
        // collision itself still supplies the ownership reason for this
        // bounded split, and prepareClosure below proves that every use can
        // be replayed.  Do not confuse identity mapping with an unresolved
        // value: only a detected value/pack witness may use this path.
        if (!authenticated_parameters and detector.value_id == null and detector.pack_id == null) {
            traceStructural("contextual_candidate_no_distinct_mapping target={}\n", .{target.index()});
            return null;
        }
        if (authenticated_parameters) {
            traceStructural("contextual_candidate_authenticated_parameter_projection target={}\n", .{target.index()});
        } else {
            traceStructural("contextual_candidate_available_external target={}\n", .{target.index()});
        }
    }
    if (!prepareClosure(allocator, program, analysis, closure, &incoming_edges)) {
        traceStructural("contextual_candidate_prepare_failure target={}\n", .{target.index()});
        return null;
    }

    retain_closure = true;
    return .{
        .allocator = allocator,
        .function_index = function_index,
        .branch = source,
        .entry = target,
        .join = target,
        .incoming = try allocator.dupe(ir.CfgEdgeRef, &incoming_edges),
        .closure = closure,
    };
}

// An identity-only external mapping can still represent a distinct incoming
// context when the collision proof has already supplied the owner tuple and
// the live edge carries the complete result tuple of an authenticated numeric
// iteration transition. Type or shape equality, and a partial tuple match,
// are not sufficient for this boundary.
fn hasAuthenticatedIterationContextualProjectionAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    target: ir.BlockId,
    incoming: ir.CfgEdgeRef,
    expected: []const ir.ValueId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    const incoming_canonical = incomingEdgeIsCanonical(program, analysis, incoming);
    const expected_edge_live = hasLiveIncomingEdgeWithArguments(program, target, expected);
    if (!incoming_canonical or !expected_edge_live) return false;
    const edge = cfg_edge.value(program, incoming) orelse return false;
    if (!isIterationTransitionHeader(program, target)) {
        return try hasAuthenticatedCompoundIterationContextualProjectionAlloc(
            program,
            analysis,
            target,
            incoming,
            expected,
        );
    }
    if (expected.len != edge.arguments.len or
        std.mem.eql(ir.ValueId, expected, edge.arguments) or
        edge.arguments.len != 4 or
        !iteration_state.isBooleanLiteral(program, edge.arguments[3], false)) return false;

    const block = program.blocks[target.index()];
    const transition_id = block.instructions[0];
    if (transition_id.index() >= program.instructions.len) return false;
    const transition = program.instructions[transition_id.index()];
    if (transition.id != transition_id or transition.results.len != 4) return false;

    var mapped_slots = [_]bool{ false, false, false, false };
    for (transition.results, 0..) |source_value, result_index| {
        const slot = iterationStateArgumentIndex(transition, result_index) orelse continue;
        const mapping = try findAuthenticatedIterationStateResultMappingAlloc(
            allocator,
            program,
            analysis,
            source_value,
            &.{incoming},
            lineage_index,
            replay_index,
            replay_cache,
            false,
        );
        if (mapping.ambiguous or mapping.value == null or mapping.value.? != edge.arguments[slot]) return false;
        mapped_slots[slot] = true;
    }
    return mapped_slots[0] and mapped_slots[1] and mapped_slots[2];
}

// A compound continuation may forward its formal tuple into a nested
// iteration header after an effectful straight-line prefix.  The target is
// context-dependent even when its instructions use only its own block
// parameters, so no external value-use witness exists.  Require the complete
// owner/incoming edge pair and the formal-to-transition forwarding edge; an
// arbitrary four-value edge is not sufficient.  The iteration header may
// terminate or continue elsewhere: the prefix itself is the context-sensitive
// region that must be split, so requiring a return to the incoming predecessor
// would reject valid acyclic continuations.
fn hasAuthenticatedCompoundIterationContextualProjectionAlloc(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    target: ir.BlockId,
    incoming: ir.CfgEdgeRef,
    expected: []const ir.ValueId,
) std.mem.Allocator.Error!bool {
    if (target.index() >= program.blocks.len or
        incoming.target != target or
        expected.len != 4)
    {
        return false;
    }
    const target_block = program.blocks[target.index()];
    if (target_block.id != target or target_block.parameters.len != expected.len or
        !node_split.parametersAreCanonical(program.values, target_block))
    {
        return false;
    }
    const edge = cfg_edge.value(program, incoming) orelse return false;
    if (edge.target != target or edge.arguments.len != target_block.parameters.len or
        std.mem.eql(ir.ValueId, expected, edge.arguments))
    {
        return false;
    }
    for (target_block.parameters, expected, edge.arguments) |formal, owner, actual| {
        if (!continuationParameterAcceptsValueType(program, formal, owner) or
            !continuationParameterAcceptsValueType(program, formal, actual)) return false;
    }

    // A compound continuation can carry arbitrary state values into an
    // effectful prefix before forwarding its own formal tuple into the next
    // iteration header.  The incoming tuple is therefore not itself an
    // iteration result tuple.  Authenticate this shape separately before the
    // narrower result-tuple rule below; otherwise a valid parameterized
    // prefix is mistaken for an unauthenticated value collision.
    if (try hasAuthenticatedEffectfulParameterizedCompoundProjectionAlloc(
        program,
        analysis,
        target,
        incoming,
        expected,
    )) return true;

    if (!iteration_state.isBooleanLiteral(program, edge.arguments[3], false)) return false;

    const transition = iterationStateTupleTransition(program, edge.arguments) orelse return false;
    if (transition.block == target or !isIterationTransitionHeader(program, transition.block)) return false;
    if (!try analysis.canReach(target, transition.block) or
        !try analysis.canReach(transition.block, incoming.source) or
        !try analysis.canReach(incoming.source, target))
    {
        return false;
    }

    for (program.blocks) |source| {
        if (source.function != analysis.function.id or
            !analysis.isReachable(source.id) or
            !try analysis.canReach(target, source.id)) continue;
        switch (source.terminator) {
            .jump => |forward| {
                if (forward.target == transition.block and
                    std.mem.eql(ir.ValueId, forward.arguments, target_block.parameters)) return true;
            },
            .branch => |branch| {
                if ((branch.then_edge.target == transition.block and
                    std.mem.eql(ir.ValueId, branch.then_edge.arguments, target_block.parameters)) or
                    (branch.else_edge.target == transition.block and
                        std.mem.eql(ir.ValueId, branch.else_edge.arguments, target_block.parameters))) return true;
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }
    return false;
}

// A parameterized continuation can combine a canonical formal prefix with a
// complete nested iteration state.  The prefix is forwarded unchanged by the
// re-entry edge while the state suffix is produced by the nested transition;
// the owner edge may carry the same contract from a different transition.
// Authenticate the composition as a tuple shape.  This is intentionally
// independent of clone names, block ids, or source layout.
fn hasAuthenticatedMixedParameterizedIterationProjectionAlloc(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    target: ir.BlockId,
    incoming: ir.CfgEdgeRef,
    expected: []const ir.ValueId,
) std.mem.Allocator.Error!bool {
    const state_width: usize = 4;
    if (target.index() >= program.blocks.len or
        incoming.target != target or
        expected.len <= state_width)
    {
        return false;
    }

    const target_block = program.blocks[target.index()];
    if (target_block.id != target or
        target_block.function != analysis.function.id or
        target_block.parameters.len != expected.len or
        !node_split.parametersAreCanonical(program.values, target_block) or
        !analysis.isReachable(target))
    {
        return false;
    }

    const incoming_edge = cfg_edge.value(program, incoming) orelse return false;
    if (!incomingEdgeIsCanonical(program, analysis, incoming) or
        incoming_edge.target != target or
        incoming_edge.arguments.len != target_block.parameters.len or
        std.mem.eql(ir.ValueId, expected, incoming_edge.arguments))
    {
        return false;
    }

    const prefix_len = expected.len - state_width;
    if (prefix_len == 0 or
        !std.mem.eql(ir.ValueId, target_block.parameters[0..prefix_len], incoming_edge.arguments[0..prefix_len]))
    {
        return false;
    }

    for (target_block.parameters, expected, incoming_edge.arguments) |formal, owner, actual| {
        if (!continuationParameterAcceptsValueType(program, formal, owner) or
            !continuationParameterAcceptsValueType(program, formal, actual)) return false;
    }

    const expected_state = expected[prefix_len..];
    const actual_state = incoming_edge.arguments[prefix_len..];
    const expected_transition = iterationStateTupleTransition(program, expected_state) orelse return false;
    const actual_transition = iterationStateTupleTransition(program, actual_state) orelse return false;
    if (!isIterationTransitionHeader(program, expected_transition.block) or
        !isIterationTransitionHeader(program, actual_transition.block))
    {
        return false;
    }

    // Find the unique live owner edge.  A merely type-compatible predecessor
    // is not enough to establish which context owns the target tuple.
    var owner_source: ?ir.BlockId = null;
    for (analysis.function.blocks) |source| {
        if (!analysis.isReachable(source) or source.index() >= program.blocks.len) continue;
        const source_block = program.blocks[source.index()];
        if (source_block.id != source or source_block.function != analysis.function.id) return false;
        switch (source_block.terminator) {
            .jump => |edge| {
                if (edge.target == target and std.mem.eql(ir.ValueId, edge.arguments, expected)) {
                    if (owner_source != null) return false;
                    owner_source = source;
                }
            },
            .branch => |branch| {
                if (branch.then_edge.target == target and
                    std.mem.eql(ir.ValueId, branch.then_edge.arguments, expected))
                {
                    if (owner_source != null) return false;
                    owner_source = source;
                }
                if (branch.else_edge.target == target and
                    std.mem.eql(ir.ValueId, branch.else_edge.arguments, expected))
                {
                    if (owner_source != null) return false;
                    owner_source = source;
                }
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }
    const owner = owner_source orelse return false;
    if (owner == incoming.source or
        try analysis.canReach(target, owner) or
        !try analysis.canReach(expected_transition.block, owner) or
        !try analysis.canReach(owner, target))
    {
        return false;
    }

    // The incoming suffix must be a real state transfer through the current
    // SCC, not an arbitrary four-value tuple with matching types.
    if (!try analysis.canReach(target, actual_transition.block) or
        !try analysis.canReach(actual_transition.block, incoming.source) or
        !try analysis.canReach(incoming.source, target))
    {
        return false;
    }

    // Follow only zero-argument blocks after the target until the nested
    // transition consumes the target's state suffix.  This preserves the
    // operation ordering and prevents an unrelated reachable transition from
    // authenticating the tuple.
    const PathState = struct {
        block: ir.BlockId,
        effectful: bool,
    };
    const seen_without_effect = try analysis.allocator.alloc(bool, analysis.function.blocks.len);
    defer analysis.allocator.free(seen_without_effect);
    const seen_with_effect = try analysis.allocator.alloc(bool, analysis.function.blocks.len);
    defer analysis.allocator.free(seen_with_effect);
    @memset(seen_without_effect, false);
    @memset(seen_with_effect, false);

    var pending: std.ArrayList(PathState) = .empty;
    defer pending.deinit(analysis.allocator);
    try pending.append(analysis.allocator, .{ .block = target, .effectful = false });

    while (pending.pop()) |state| {
        const local_index = analysis.blockIndex(state.block) orelse return false;
        const seen = if (state.effectful) seen_with_effect else seen_without_effect;
        if (seen[local_index]) continue;
        seen[local_index] = true;

        if (state.block.index() >= program.blocks.len) return false;
        const block = program.blocks[state.block.index()];
        if (block.id != state.block or block.function != analysis.function.id) return false;
        var path_effectful = state.effectful;
        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) return false;
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or instruction.block != state.block) return false;
            path_effectful = path_effectful or proof_effect_closure.hasObservableEffects(instruction.effects);
        }

        switch (block.terminator) {
            .jump => |edge| {
                if (edge.target == actual_transition.block and
                    std.mem.eql(ir.ValueId, edge.arguments, target_block.parameters[prefix_len..]))
                {
                    if (path_effectful) return true;
                    continue;
                }
                if (edge.arguments.len != 0 or edge.target == target) continue;
                if (edge.target.index() >= program.blocks.len) return false;
                if (program.blocks[edge.target.index()].parameters.len != 0) continue;
                try pending.append(analysis.allocator, .{ .block = edge.target, .effectful = path_effectful });
            },
            .branch => |branch| {
                const edges = [_]ir.Edge{ branch.then_edge, branch.else_edge };
                for (edges) |edge| {
                    if (edge.target == actual_transition.block and
                        std.mem.eql(ir.ValueId, edge.arguments, target_block.parameters[prefix_len..]))
                    {
                        if (path_effectful) return true;
                        continue;
                    }
                    if (edge.arguments.len != 0 or edge.target == target) continue;
                    if (edge.target.index() >= program.blocks.len) return false;
                    if (program.blocks[edge.target.index()].parameters.len != 0) continue;
                    try pending.append(analysis.allocator, .{ .block = edge.target, .effectful = path_effectful });
                }
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }
    return false;
}

fn hasAuthenticatedEffectfulParameterizedCompoundProjectionAlloc(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    target: ir.BlockId,
    incoming: ir.CfgEdgeRef,
    expected: []const ir.ValueId,
) std.mem.Allocator.Error!bool {
    if (target.index() >= program.blocks.len or
        incoming.target != target or
        expected.len != 4)
    {
        return false;
    }
    const target_block = program.blocks[target.index()];
    if (target_block.id != target or target_block.function != analysis.function.id or
        target_block.parameters.len != expected.len or
        !node_split.parametersAreCanonical(program.values, target_block) or
        !analysis.isReachable(target))
    {
        return false;
    }
    const incoming_edge = cfg_edge.value(program, incoming) orelse return false;
    if (!analysis.isReachable(incoming.source) or
        incoming_edge.target != target or
        incoming_edge.arguments.len != target_block.parameters.len or
        std.mem.eql(ir.ValueId, expected, incoming_edge.arguments))
    {
        return false;
    }

    // The owner tuple must be a distinct, reachable entry into this target.
    // A type-compatible tuple or a dead edge does not establish ownership.
    var owner_entry: ?ir.BlockId = null;
    for (analysis.function.blocks) |source| {
        if (source == incoming.source or !analysis.isReachable(source)) continue;
        if (source.index() >= program.blocks.len) return false;
        const source_block = program.blocks[source.index()];
        if (source_block.id != source or source_block.function != analysis.function.id) return false;
        switch (source_block.terminator) {
            .jump => |edge| {
                if (edge.target == target and std.mem.eql(ir.ValueId, edge.arguments, expected)) {
                    if (owner_entry != null) return false;
                    owner_entry = source;
                }
            },
            .branch => |branch| {
                if (branch.then_edge.target == target and
                    std.mem.eql(ir.ValueId, branch.then_edge.arguments, expected))
                {
                    if (owner_entry != null) return false;
                    owner_entry = source;
                }
                if (branch.else_edge.target == target and
                    std.mem.eql(ir.ValueId, branch.else_edge.arguments, expected))
                {
                    if (owner_entry != null) return false;
                    owner_entry = source;
                }
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }
    if (owner_entry == null) return false;

    for (target_block.parameters, expected, incoming_edge.arguments) |formal, owner, actual| {
        if (!continuationParameterAcceptsValueType(program, formal, owner) or
            !continuationParameterAcceptsValueType(program, formal, actual)) return false;
    }

    // Walk only the straight-line compound prefix.  Every hop before the
    // iteration header must be a zero-argument jump; this keeps branch
    // choices and hidden context transfers out of the projection proof.
    const seen = try analysis.allocator.alloc(bool, analysis.function.blocks.len);
    defer analysis.allocator.free(seen);
    @memset(seen, false);

    var cursor = target;
    var transition: ?ir.BlockId = null;
    var has_effect = false;
    while (true) {
        const local_index = analysis.blockIndex(cursor) orelse return false;
        if (local_index >= seen.len or seen[local_index]) return false;
        seen[local_index] = true;
        if (cursor.index() >= program.blocks.len) return false;
        const block = program.blocks[cursor.index()];
        if (block.id != cursor or block.function != analysis.function.id or
            (cursor != target and block.parameters.len != 0)) return false;
        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) return false;
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or instruction.block != cursor) return false;
            if (proof_effect_closure.hasObservableEffects(instruction.effects)) has_effect = true;
        }

        switch (block.terminator) {
            .jump => |edge| {
                if (edge.target.index() >= program.blocks.len or
                    !analysis.isReachable(edge.target)) return false;
                if (isIterationTransitionHeader(program, edge.target)) {
                    if (transition != null or
                        !std.mem.eql(ir.ValueId, edge.arguments, target_block.parameters)) return false;
                    transition = edge.target;
                    break;
                }
                if (edge.arguments.len != 0) return false;
                cursor = edge.target;
            },
            .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
        }
    }

    const transition_block = transition orelse return false;
    if (!has_effect or transition_block == target or transition_block == incoming.source or
        !try analysis.canReach(target, transition_block) or
        !try analysis.canReach(incoming.source, target))
    {
        return false;
    }
    return true;
}

fn hasDistinctExternalCloneMapping(mappings: ExternalCloneMappings) bool {
    for (mappings.values, mappings.clone_values) |source, clone| if (source != clone) return true;
    for (mappings.packs, mappings.clone_packs) |source, clone| if (source != clone) return true;
    return false;
}

fn packProducerBlock(program: *const ir.Program, pack_id: ir.ValuePackId) ?ir.BlockId {
    if (pack_id.index() >= program.value_packs.len) return null;
    return switch (program.value_packs[pack_id.index()].origin) {
        .instruction_result => |instruction_id| if (instruction_id.index() < program.instructions.len)
            program.instructions[instruction_id.index()].block
        else
            null,
        .varargs => null,
    };
}

pub fn conditionalLoopEntryCountAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function_index: usize,
    header: ir.BlockId,
) std.mem.Allocator.Error!usize {
    if (function_index >= program.functions.len) return 0;
    var analysis = cfg.Analysis.init(allocator, program, program.functions[function_index]) catch |err| switch (err) {
        error.InvalidCfg => return 0,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    var membership = natural_loop.collect(allocator, &analysis, header) catch |err| switch (err) {
        error.UnsupportedShape => return 0,
        error.OutOfMemory => return error.OutOfMemory,
    } orelse return 0;
    defer membership.deinit();
    return countConditionalLoopEntries(&analysis, header, membership.bits);
}

pub fn interiorLoopEntryCountAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function_index: usize,
    header: ir.BlockId,
) std.mem.Allocator.Error!usize {
    if (function_index >= program.functions.len) return 0;
    var analysis = cfg.Analysis.init(allocator, program, program.functions[function_index]) catch |err| switch (err) {
        error.InvalidCfg => return 0,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer analysis.deinit();
    var membership = natural_loop.collect(allocator, &analysis, header) catch |err| switch (err) {
        error.UnsupportedShape => return 0,
        error.OutOfMemory => return error.OutOfMemory,
    } orelse return 0;
    defer membership.deinit();
    return countInteriorLoopEntries(&analysis, header, membership.bits);
}

// An incoming edge may originate inside an enclosing loop without making a
// collision closure unsafe.  A linear effectful suffix can be cloned when it
// has no parameters, no internal cycle, and one outgoing boundary.  If that
// boundary returns to the suffix entry, it must be the complete authenticated
// state handoff into an iteration header; otherwise cloning would duplicate a
// loop body and recreate the same ownership collision.
fn internalLoopEffectfulSuffixCanBeCloned(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    loop_headers: []const bool,
    entry: ir.BlockId,
    closure: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
) std.mem.Allocator.Error!bool {
    if (closure.len == 0 or incoming.len == 0 or
        loop_headers.len != analysis.function.blocks.len)
    {
        return false;
    }
    for (incoming) |reference| {
        if (reference.target != entry or
            !incomingEdgeIsCanonical(program, analysis, reference) or
            containsBlock(closure, reference.source))
        {
            return false;
        }
    }

    const membership = try allocator.alloc(bool, analysis.function.blocks.len);
    defer allocator.free(membership);
    @memset(membership, false);
    for (closure) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return false;
        if (local_index >= membership.len or membership[local_index] or
            block_id.index() >= program.blocks.len)
        {
            return false;
        }
        membership[local_index] = true;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id or block.function != analysis.function.id or
            block.parameters.len != 0 or loop_headers[local_index])
        {
            return false;
        }
    }

    const entry_index = analysis.blockIndex(entry) orelse return false;
    if (!membership[entry_index]) return false;
    const visited = try allocator.alloc(bool, membership.len);
    defer allocator.free(visited);
    @memset(visited, false);

    var cursor = entry;
    var visited_count: usize = 0;
    var boundary: ?ir.CfgEdgeRef = null;
    var has_effect = false;
    while (true) {
        const local_index = analysis.blockIndex(cursor) orelse return false;
        if (!membership[local_index] or visited[local_index] or
            cursor.index() >= program.blocks.len)
        {
            return false;
        }
        visited[local_index] = true;
        visited_count += 1;
        const block = program.blocks[cursor.index()];
        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) return false;
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or instruction.block != cursor) return false;
            has_effect = has_effect or proof_effect_closure.hasObservableEffects(instruction.effects);
        }

        const edge = switch (block.terminator) {
            .jump => |value| value,
            .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
        };
        if (edge.target.index() >= program.blocks.len or
            !analysis.isReachable(edge.target))
        {
            return false;
        }
        const target_index = analysis.blockIndex(edge.target) orelse return false;
        if (membership[target_index]) {
            if (edge.target == cursor or visited[target_index]) return false;
            cursor = edge.target;
            continue;
        }
        if (boundary != null) return false;
        const target = program.blocks[edge.target.index()];
        if (target.id != edge.target or target.function != analysis.function.id or
            edge.arguments.len != target.parameters.len)
        {
            return false;
        }
        boundary = .{ .source = cursor, .kind = .jump, .target = edge.target };
        break;
    }

    if (!has_effect or visited_count != closure.len or boundary == null) return false;
    const handoff = boundary.?;
    if (try analysis.canReach(handoff.target, entry)) {
        return try authenticatedIterationHandoffBoundaryAtIncoming(
            program,
            analysis,
            entry,
            closure,
            handoff,
            incoming,
            null,
        );
    }
    return true;
}

// A zero-parameter internal SCC edge can still be a valid clone boundary when
// the edge is one authenticated member of a single node-split group.  The
// ordinary internal-predecessor count cannot distinguish that case from an
// unowned loop edge, so keep the exception behind the complete group proof:
// every relevant edge must have one active replayable rewrite, one lineage
// parent, and one group-owned clone endpoint.
fn authenticatedGroupCloneEdgeForReference(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    reference: ir.CfgEdgeRef,
    replay_context: *ReplayProjectionContext,
) std.mem.Allocator.Error!?ir.NodeSplitGroupId {
    if (!incomingEdgeIsCanonical(program, analysis, reference)) return null;

    var selected_group: ?ir.NodeSplitGroupId = null;
    var found = false;
    for (replay_context.replay_index.nodeSplitRewriteIndices()) |rewrite_index| {
        if (rewrite_index >= program.edge_rewrites.len) return null;
        const rewrite = program.edge_rewrites[rewrite_index];
        if (rewrite.rule != .node_split or rewrite.node_split_group == null or
            rewrite.source != reference.source or rewrite.kind != reference.kind or
            rewrite.to.target != reference.target or rewrite.from.target == rewrite.to.target)
        {
            continue;
        }
        if (found or !nodeSplitRewriteArgumentsAreStable(program, rewrite) or
            !activeNodeSplitRewrite(program, rewrite)) return null;
        const group = rewrite.node_split_group.?;
        if (!replay_context.replay_index.groupOwnsBlock(program, group, reference.source) or
            !replay_context.replay_index.groupOwnsBlock(program, group, reference.target))
        {
            return null;
        }
        const lineage_parent = replay_context.cloneLineageParent(rewrite.to.target) orelse return null;
        if (lineage_parent.block != rewrite.from.target or lineage_parent.group != group) return null;
        const replay = (try replay_context.replay_cache.get(
            rewrite.from.target,
            rewrite.to.target,
            group,
        )) orelse return null;
        if (!nodeSplitRewriteArgumentsMatchReplay(program, rewrite, replay.*) or
            !try cloneLineageArgumentsMatchReplayCached(
                allocator,
                program,
                rewrite.from.target,
                rewrite.to.target,
                &replay_context.lineage_index,
                &replay_context.replay_index,
                &replay_context.replay_cache,
            )) return null;
        found = true;
        selected_group = group;
    }
    return selected_group;
}

fn authenticatedGroupOwnedInternalSccClosure(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    replay_context: *ReplayProjectionContext,
) std.mem.Allocator.Error!bool {
    if (closure.len <= 1 or incoming.len == 0) return false;

    var selected_group: ?ir.NodeSplitGroupId = null;
    for (incoming) |reference| {
        const group = (try authenticatedGroupCloneEdgeForReference(
            allocator,
            program,
            analysis,
            reference,
            replay_context,
        )) orelse return false;
        if (!try replay_context.hasAuthenticatedContinuationBridgeForEdge(analysis, reference)) return false;
        if (selected_group) |existing| {
            if (existing != group) return false;
        } else {
            selected_group = group;
        }
    }
    const group = selected_group orelse return false;

    for (closure) |block_id| {
        if (block_id.index() >= program.blocks.len) return false;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id or block.function != analysis.function.id or
            !node_split.parametersAreCanonical(program.values, block) or
            !replay_context.replay_index.isAuthenticatedCloneBlock(program, block_id) or
            !replay_context.replay_index.groupOwnsBlock(program, group, block_id))
        {
            return false;
        }

        switch (block.terminator) {
            .jump => |edge| if (containsBlock(closure, edge.target)) {
                const edge_group = (try authenticatedGroupCloneEdgeForReference(
                    allocator,
                    program,
                    analysis,
                    .{ .source = block_id, .kind = .jump, .target = edge.target },
                    replay_context,
                )) orelse return false;
                if (edge_group != group) return false;
            },
            .branch => |branch| {
                for ([_]struct { kind: ir.CfgEdgeKind, edge: ir.Edge }{
                    .{ .kind = .branch_then, .edge = branch.then_edge },
                    .{ .kind = .branch_else, .edge = branch.else_edge },
                }) |candidate| {
                    if (!containsBlock(closure, candidate.edge.target)) continue;
                    const edge_group = (try authenticatedGroupCloneEdgeForReference(
                        allocator,
                        program,
                        analysis,
                        .{ .source = block_id, .kind = candidate.kind, .target = candidate.edge.target },
                        replay_context,
                    )) orelse return false;
                    if (edge_group != group) return false;
                }
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
        }
    }
    return true;
}

// A selected collision edge can be the only external entry into an already
// authenticated clone-group cycle.  In that shape, cutting the incoming
// source out of the SCC leaves a cloned producer reachable from the original
// source and cannot project its carried tuple.  Clone the complete SCC only
// when the source and its ingress are themselves replay-authenticated members
// of one group.  The ordinary closure, boundary, and availability proofs
// still decide whether the resulting component is cloneable.
fn authenticatedIncomingSourceComponentProjection(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    entry: ir.BlockId,
    component: []const bool,
    incoming: []const ir.CfgEdgeRef,
    replay_context: *ReplayProjectionContext,
) std.mem.Allocator.Error!bool {
    if (incoming.len != 1 or component.len != analysis.function.blocks.len) {
        traceStructural("structural_phase complete_component_reject reason=shape incoming={} component={} blocks={}\n", .{
            incoming.len,
            component.len,
            analysis.function.blocks.len,
        });
        return false;
    }
    const reference = incoming[0];
    const canonical = incomingEdgeIsCanonical(program, analysis, reference);
    if (reference.target != entry or reference.source == entry or !canonical) {
        traceStructural("structural_phase complete_component_reject reason=edge_shape source={} target={} entry={} source_is_entry={} canonical={}\n", .{
            reference.source.index(),
            reference.target.index(),
            entry.index(),
            reference.source == entry,
            canonical,
        });
        return false;
    }
    const source_index = analysis.blockIndex(reference.source) orelse {
        traceStructural("structural_phase complete_component_reject reason=source_index source={}\n", .{reference.source.index()});
        return false;
    };
    const entry_index = analysis.blockIndex(entry) orelse {
        traceStructural("structural_phase complete_component_reject reason=entry_index entry={}\n", .{entry.index()});
        return false;
    };
    if (!component[source_index] or !component[entry_index] or
        !replay_context.replay_index.isAuthenticatedCloneBlock(program, reference.source))
    {
        traceStructural("structural_phase complete_component_reject reason=membership source={} source_scc={} entry={} entry_scc={} source_clone={}\n", .{
            reference.source.index(),
            component[source_index],
            entry.index(),
            component[entry_index],
            replay_context.replay_index.isAuthenticatedCloneBlock(program, reference.source),
        });
        return false;
    }

    const lineage_parent = replay_context.cloneLineageParent(reference.source) orelse {
        traceStructural("structural_phase complete_component_reject reason=lineage source={}\n", .{reference.source.index()});
        return false;
    };
    if (!replay_context.replay_index.groupOwnsBlock(
        program,
        lineage_parent.group,
        reference.source,
    )) {
        traceStructural("structural_phase complete_component_reject reason=group_ownership source={} parent={} group={}\n", .{
            reference.source.index(),
            lineage_parent.block.index(),
            lineage_parent.group.index(),
        });
        return false;
    }
    const stable_arguments = cloneLineageArgumentsAreStableCached(
        program,
        reference.source,
        &replay_context.lineage_index,
    );
    const replay_arguments = try cloneLineageArgumentsMatchReplayCached(
        allocator,
        program,
        lineage_parent.block,
        reference.source,
        &replay_context.lineage_index,
        &replay_context.replay_index,
        &replay_context.replay_cache,
    );
    if (!stable_arguments or !replay_arguments) {
        traceStructural("structural_phase complete_component_reject reason=lineage_replay source={} parent={} stable={} replay={}\n", .{
            reference.source.index(),
            lineage_parent.block.index(),
            stable_arguments,
            replay_arguments,
        });
        return false;
    }
    const reaches_source = try analysis.canReach(entry, reference.source);
    const returns_to_entry = try analysis.canReach(reference.source, entry);
    if (!reaches_source or !returns_to_entry) {
        traceStructural("structural_phase complete_component_reject reason=scc_reach source={} entry_to_source={} source_to_entry={}\n", .{
            reference.source.index(),
            reaches_source,
            returns_to_entry,
        });
        return false;
    }
    const live_reference = directEdgeRef(program, reference.source, entry) orelse {
        traceStructural("structural_phase complete_component_reject reason=live_edge source={} entry={}\n", .{
            reference.source.index(),
            entry.index(),
        });
        return false;
    };
    if (!std.meta.eql(live_reference, reference)) {
        traceStructural("structural_phase complete_component_reject reason=edge_mismatch source={} entry={} kind={s}\n", .{
            reference.source.index(),
            entry.index(),
            @tagName(reference.kind),
        });
        return false;
    }

    var predecessor_count: usize = 0;
    var predecessor_index: usize = 0;
    while (analysis.predecessorAt(reference.source, predecessor_index)) |predecessor| : (predecessor_index += 1) {
        const predecessor_local_index = analysis.blockIndex(predecessor) orelse {
            traceStructural("structural_phase complete_component_reject reason=predecessor_index source={} predecessor={}\n", .{
                reference.source.index(),
                predecessor.index(),
            });
            return false;
        };
        if (!component[predecessor_local_index] or
            !replay_context.replay_index.isAuthenticatedCloneBlock(program, predecessor) or
            !replay_context.replay_index.groupOwnsBlock(program, lineage_parent.group, predecessor))
        {
            traceStructural("structural_phase complete_component_reject reason=predecessor_ownership source={} predecessor={} predecessor_scc={} predecessor_clone={} predecessor_group={}\n", .{
                reference.source.index(),
                predecessor.index(),
                component[predecessor_local_index],
                replay_context.replay_index.isAuthenticatedCloneBlock(program, predecessor),
                replay_context.replay_index.groupOwnsBlock(program, lineage_parent.group, predecessor),
            });
            return false;
        }
        const predecessor_reference = directEdgeRef(program, predecessor, reference.source) orelse {
            traceStructural("structural_phase complete_component_reject reason=predecessor_edge source={} predecessor={}\n", .{
                reference.source.index(),
                predecessor.index(),
            });
            return false;
        };
        if (!replay_context.hasNodeSplitEntryEdge(
            predecessor_reference.source,
            predecessor_reference.kind,
            reference.source,
            lineage_parent.group,
        )) {
            traceStructural("structural_phase complete_component_reject reason=predecessor_replay source={} predecessor={} kind={s} group={}\n", .{
                reference.source.index(),
                predecessor.index(),
                @tagName(predecessor_reference.kind),
                lineage_parent.group.index(),
            });
            return false;
        }
        predecessor_count += 1;
    }
    return predecessor_count != 0;
}

// An internal SCC edge with more than one same-component predecessor is a
// join collision, not a linear suffix.  Cloning one block at a time merely
// walks the collision around the component.  Build the authenticated forward
// projection from the collided block while cutting every direct component
// predecessor of that block; the resulting closure can contain the whole
// cyclic route and still leaves the incoming sources outside the clone.
fn internalSccBoundaryClosureAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    block: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    replay_context: *ReplayProjectionContext,
) std.mem.Allocator.Error!?[]ir.BlockId {
    if (incoming.len == 0 or block.index() >= program.blocks.len) return null;
    const block_index = analysis.blockIndex(block) orelse return null;
    const block_count = analysis.function.blocks.len;
    const forward = try allocator.alloc(bool, block_count);
    defer allocator.free(forward);
    const backward = try allocator.alloc(bool, block_count);
    defer allocator.free(backward);
    const queued = try allocator.alloc(ir.BlockId, block_count);
    defer allocator.free(queued);
    @memset(forward, false);
    @memset(backward, false);

    var head: usize = 0;
    var tail: usize = 1;
    queued[0] = block;
    forward[block_index] = true;
    while (head < tail) : (head += 1) {
        const current = queued[head];
        var successor_index: usize = 0;
        while (successor_index < analysis.successorCount(current)) : (successor_index += 1) {
            const successor = analysis.successorAt(current, successor_index) orelse return null;
            const local_index = analysis.blockIndex(successor) orelse return null;
            if (!analysis.isReachable(successor) or forward[local_index]) continue;
            forward[local_index] = true;
            if (tail >= queued.len) return null;
            queued[tail] = successor;
            tail += 1;
        }
    }

    head = 0;
    tail = 1;
    queued[0] = block;
    backward[block_index] = true;
    while (head < tail) : (head += 1) {
        const current = queued[head];
        var predecessor_index: usize = 0;
        while (predecessor_index < analysis.predecessorCount(current)) : (predecessor_index += 1) {
            const predecessor = analysis.predecessorAt(current, predecessor_index) orelse return null;
            const local_index = analysis.blockIndex(predecessor) orelse return null;
            if (!analysis.isReachable(predecessor) or backward[local_index]) continue;
            backward[local_index] = true;
            if (tail >= queued.len) return null;
            queued[tail] = predecessor;
            tail += 1;
        }
    }

    const component = try allocator.alloc(bool, block_count);
    defer allocator.free(component);
    @memset(component, false);
    var component_size: usize = 0;
    for (analysis.function.blocks, 0..) |_, candidate_index| {
        if (forward[candidate_index] and backward[candidate_index]) {
            component[candidate_index] = true;
            component_size += 1;
        }
    }
    if (component_size < 2) return null;

    const complete_component_projection = try authenticatedIncomingSourceComponentProjection(
        allocator,
        program,
        analysis,
        block,
        component,
        incoming,
        replay_context,
    );

    const forbidden = try allocator.alloc(bool, block_count);
    defer allocator.free(forbidden);
    @memset(forbidden, false);
    if (!complete_component_projection) {
        for (incoming) |reference| {
            if (reference.target != block) return null;
            const source_index = analysis.blockIndex(reference.source) orelse return null;
            if (!component[source_index] or source_index == block_index) return null;
            forbidden[source_index] = true;
        }
    }

    // A second internal predecessor is what makes the scalar boundary clone
    // non-convergent.  A parameterized branching entry has a stronger
    // alternative: its complete incoming tuple can authenticate a rooted SCC
    // projection even when only one internal predecessor reaches the entry.
    // Cut all such predecessors, including ones not selected by this feedback
    // arm, so the projection owns one complete entry.
    var internal_predecessor_count: usize = 0;
    var predecessor_index: usize = 0;
    while (predecessor_index < analysis.predecessorCount(block)) : (predecessor_index += 1) {
        const predecessor = analysis.predecessorAt(block, predecessor_index) orelse return null;
        const local_index = analysis.blockIndex(predecessor) orelse return null;
        if (!component[local_index] or local_index == block_index) continue;
        if (!complete_component_projection) forbidden[local_index] = true;
        internal_predecessor_count += 1;
    }
    traceStructural("structural_phase internal_scc_candidate block={} component={} internal_predecessors={} complete_component={}\n", .{
        block.index(),
        component_size,
        internal_predecessor_count,
        complete_component_projection,
    });
    const parameterized_branch_boundary = program.blocks[block.index()].parameters.len != 0 and switch (program.blocks[block.index()].terminator) {
        .branch => true,
        else => false,
    };

    var closure = std.ArrayList(ir.BlockId).empty;
    var retain_closure = false;
    defer if (!retain_closure) closure.deinit(allocator);
    const seen = try allocator.alloc(bool, block_count);
    defer allocator.free(seen);
    @memset(seen, false);
    head = 0;
    tail = 1;
    queued[0] = block;
    seen[block_index] = true;
    while (head < tail) : (head += 1) {
        const current = queued[head];
        try closure.append(allocator, current);
        var successor_index: usize = 0;
        while (successor_index < analysis.successorCount(current)) : (successor_index += 1) {
            const successor = analysis.successorAt(current, successor_index) orelse return null;
            const local_index = analysis.blockIndex(successor) orelse return null;
            if (!component[local_index] or
                (!complete_component_projection and forbidden[local_index]) or
                seen[local_index]) continue;
            seen[local_index] = true;
            if (tail >= queued.len) return null;
            queued[tail] = successor;
            tail += 1;
        }
    }
    if (closure.items.len <= 1) {
        traceStructural("structural_phase internal_scc_reject block={} reason=boundary_cut closure={}\n", .{
            block.index(),
            closure.items.len,
        });
        return null;
    }
    if (complete_component_projection and closure.items.len != component_size) {
        traceStructural("structural_phase internal_scc_reject block={} reason=incomplete_component_projection closure={} component={}\n", .{
            block.index(),
            closure.items.len,
            component_size,
        });
        return null;
    }
    if (!complete_component_projection and internal_predecessor_count < 2 and !parameterized_branch_boundary and
        !try authenticatedGroupOwnedInternalSccClosure(
            allocator,
            program,
            analysis,
            closure.items,
            incoming,
            replay_context,
        ))
    {
        traceStructural("structural_phase internal_scc_reject block={} reason=single_internal_predecessor closure={} component={}\n", .{
            block.index(),
            closure.items.len,
            component_size,
        });
        return null;
    }
    // A complete authenticated SCC may have consumers immediately outside the
    // component.  Defer its first preparation check until the bounded
    // external-use and authenticated-group projections have had a chance to
    // bring those consumers into the clone.  The final preparation below
    // remains mandatory and still owns all boundary, availability, and clone
    // ordering proofs.  Incomplete projections retain the prefix fallback.
    if (!complete_component_projection) {
        if (!prepareClosureWithReplayContext(
            allocator,
            program,
            analysis,
            closure.items,
            incoming,
            replay_context,
        )) {
            if (try rootedSccPrefixClosureAlloc(
                allocator,
                program,
                analysis,
                block,
                incoming,
                component,
                forbidden,
                replay_context,
            )) |prefix| {
                traceStructural("structural_phase internal_scc_prefix_accept block={} closure={} component={} incoming={}\n", .{
                    block.index(),
                    prefix.len,
                    component_size,
                    incoming.len,
                });
                const owned = prefix;
                retain_closure = true;
                closure.deinit(allocator);
                return owned;
            }
            traceStructural("structural_phase internal_scc_reject block={} reason=prepare closure={} component={}\n", .{
                block.index(),
                closure.items.len,
                component_size,
            });
            return null;
        }
    }
    traceStructural("structural_phase internal_scc_accept block={} closure={} component={} incoming={} deferred_prepare={}\n", .{
        block.index(),
        closure.items.len,
        component_size,
        incoming.len,
        complete_component_projection,
    });

    var expanded = try closure.toOwnedSlice(allocator);
    retain_closure = true;
    var retain_expanded = false;
    defer if (!retain_expanded) allocator.free(expanded);
    // A complete SCC projection can still feed a shared continuation outside
    // the SCC. Expand only the authenticated consumers of its mapped values
    // before publication, using the same closure-only ownership pass as the
    // bounded boundary fallback.
    expanded = try extendClosureForExternalUsesAlloc(
        allocator,
        program,
        analysis,
        block,
        expanded,
        incoming,
    );
    expanded = try extendAuthenticatedGroupBoundaryContextAlloc(
        allocator,
        program,
        analysis,
        expanded,
        incoming,
        &replay_context.lineage_index,
        &replay_context.replay_index,
    );
    if (!complete_component_projection) {
        expanded = (try trimIncomingSourceClosureAlloc(
            allocator,
            analysis,
            block,
            expanded,
            incoming,
        )) orelse return null;
    }
    const prepared = if (complete_component_projection)
        prepareClosureWithReplayContextFromTargets(
            allocator,
            program,
            analysis,
            expanded,
            incoming,
            replay_context,
        )
    else
        prepareClosureWithReplayContext(
            allocator,
            program,
            analysis,
            expanded,
            incoming,
            replay_context,
        );
    if (!prepared) return null;
    retain_expanded = true;
    return expanded;
}

// A complete SCC projection may contain a producer that is globally
// dominant but not dominant from the proposed clone entry.  Cloning through
// that producer would remap a live value to a definition that is not executed
// on every cloned path.  Search the SCC in deterministic successor order and
// retain only the largest rooted prefix whose complete value/effect proof
// remains valid.  The first rejected successor stays outside the clone as a
// shared continuation; no value is synthesized or aliased.
fn rootedSccPrefixClosureAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    block: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    component: []const bool,
    forbidden: []const bool,
    replay_context: *ReplayProjectionContext,
) std.mem.Allocator.Error!?[]ir.BlockId {
    const block_count = analysis.function.blocks.len;
    if (block.index() >= program.blocks.len or
        component.len != block_count or
        forbidden.len != block_count or
        incoming.len == 0)
    {
        return null;
    }
    const block_index = analysis.blockIndex(block) orelse return null;
    if (!component[block_index]) return null;

    const seen = try allocator.alloc(bool, block_count);
    defer allocator.free(seen);
    const queue = try allocator.alloc(ir.BlockId, block_count);
    defer allocator.free(queue);
    @memset(seen, false);

    var closure: std.ArrayList(ir.BlockId) = .empty;
    errdefer closure.deinit(allocator);
    try closure.append(allocator, block);
    seen[block_index] = true;
    if (!prepareClosureWithReplayContext(
        allocator,
        program,
        analysis,
        closure.items,
        incoming,
        replay_context,
    )) {
        return null;
    }

    var head: usize = 0;
    var tail: usize = 1;
    queue[0] = block;
    var grew = false;
    while (head < tail) : (head += 1) {
        const current = queue[head];
        var successor_index: usize = 0;
        while (successor_index < analysis.successorCount(current)) : (successor_index += 1) {
            const successor = analysis.successorAt(current, successor_index) orelse return null;
            const local_index = analysis.blockIndex(successor) orelse return null;
            if (!component[local_index] or forbidden[local_index] or seen[local_index]) continue;

            const previous_len = closure.items.len;
            try closure.append(allocator, successor);
            if (!prepareClosureWithReplayContext(
                allocator,
                program,
                analysis,
                closure.items,
                incoming,
                replay_context,
            )) {
                closure.items.len = previous_len;
                continue;
            }

            seen[local_index] = true;
            if (tail >= queue.len) return null;
            queue[tail] = successor;
            tail += 1;
            grew = true;
        }
    }

    if (!grew or closure.items.len <= 1) return null;
    const owned = try closure.toOwnedSlice(allocator);
    var expanded = try extendClosureForExternalUsesAlloc(
        allocator,
        program,
        analysis,
        block,
        owned,
        incoming,
    );
    expanded = (try trimIncomingSourceClosureAlloc(
        allocator,
        analysis,
        block,
        expanded,
        incoming,
    )) orelse {
        allocator.free(expanded);
        return null;
    };
    if (!prepareClosureWithReplayContext(
        allocator,
        program,
        analysis,
        expanded,
        incoming,
        replay_context,
    )) {
        allocator.free(expanded);
        return null;
    }
    return expanded;
}

const DeadPureForwardingUses = struct {
    values: []bool,
    packs: []bool,

    pub fn value(self: DeadPureForwardingUses, value_id: ir.ValueId) void {
        if (value_id.index() < self.values.len) self.values[value_id.index()] = true;
    }

    pub fn pack(self: DeadPureForwardingUses, pack_id: ir.ValuePackId) void {
        if (pack_id.index() < self.packs.len) self.packs[pack_id.index()] = true;
    }

    pub fn place(_: DeadPureForwardingUses, _: ir.PlaceId) void {}
};

// A forwarding block may contain exact-pure instructions whose results are
// dead.  Such instructions do not carry observable state or a value boundary,
// so the block is semantically equivalent to its argument-free jump.  Keep
// this proof separate from the empty-block forwarding predicate: the latter
// is a historical shape, while this predicate proves the live semantics.
fn isDeadPureForwardingBlock(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    block_id: ir.BlockId,
) std.mem.Allocator.Error!bool {
    if (block_id.index() >= program.blocks.len or
        analysis.blockIndex(block_id) == null or
        !analysis.isReachable(block_id) or
        analysis.function.entry_block == block_id)
    {
        return false;
    }
    const block = program.blocks[block_id.index()];
    if (block.id != block_id or block.function != analysis.function.id or
        block.parameters.len != 0)
    {
        return false;
    }
    const outgoing = switch (block.terminator) {
        .jump => |edge| edge,
        .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
    };
    if (outgoing.arguments.len != 0 or outgoing.target == block_id or
        outgoing.target.index() >= program.blocks.len or
        analysis.blockIndex(outgoing.target) == null or
        !analysis.isReachable(outgoing.target))
    {
        return false;
    }
    const successor = program.blocks[outgoing.target.index()];
    if (successor.id != outgoing.target or successor.function != block.function or
        successor.parameters.len != 0)
    {
        return false;
    }

    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return false;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or instruction.block != block_id or
            proof_effect_closure.hasObservableEffects(instruction.effects))
        {
            return false;
        }
    }

    const used_values = try allocator.alloc(bool, program.values.len);
    defer allocator.free(used_values);
    @memset(used_values, false);
    const used_packs = try allocator.alloc(bool, program.value_packs.len);
    defer allocator.free(used_packs);
    @memset(used_packs, false);
    const visitor = DeadPureForwardingUses{
        .values = used_values,
        .packs = used_packs,
    };
    for (analysis.function.blocks) |reachable_block_id| {
        if (!analysis.isReachable(reachable_block_id) or
            reachable_block_id.index() >= program.blocks.len)
        {
            continue;
        }
        const reachable_block = program.blocks[reachable_block_id.index()];
        if (reachable_block.id != reachable_block_id or
            reachable_block.function != analysis.function.id)
        {
            return false;
        }
        for (reachable_block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) return false;
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or instruction.block != reachable_block_id) return false;
            runtime_uses.visitOperationUses(instruction.operation, visitor);
        }
        runtime_uses.visitTerminatorUses(reachable_block.terminator, visitor);
    }
    for (block.instructions) |instruction_id| {
        const instruction = program.instructions[instruction_id.index()];
        for (instruction.results) |result_id| {
            if (result_id.index() >= used_values.len or used_values[result_id.index()]) return false;
        }
        if (instruction.pack_result) |pack_id| {
            if (pack_id.index() >= used_packs.len or used_packs[pack_id.index()]) return false;
        }
    }
    return true;
}

// An authenticated SCC projection can be duplicated at an internal SCC edge
// without duplicating the SCC's continuation.  Parameterized and branching
// entries are admitted only through the complete SCC/replay proof below.  The
// A one-block fallback may also carry parameters, but only when the live
// incoming edge and the complete cloneability/availability proof authenticate
// that formal tuple.  It does not infer or synthesize any parameter value.
fn boundaryCloneSplitAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    block: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    replay_context: *ReplayProjectionContext,
) std.mem.Allocator.Error!?Split {
    if (block.index() >= program.blocks.len or incoming.len == 0) return null;
    const target = program.blocks[block.index()];
    if (target.id != block or target.function != analysis.function.id) return null;

    // A parameterized entry has a complete local boundary when its formal
    // tuple is consumed locally before the successor. Try that authenticated
    // one-block projection first; the larger SCC projection remains a
    // fallback when the local tuple is insufficient or the successor has a
    // context-dependent use.
    if (target.parameters.len != 0) {
        const closure = try allocator.alloc(ir.BlockId, 1);
        closure[0] = block;
        if (prepareClosureWithReplayContext(
            allocator,
            program,
            analysis,
            closure,
            incoming,
            replay_context,
        )) {
            const owned_incoming = try allocator.dupe(ir.CfgEdgeRef, incoming);
            return .{
                .allocator = allocator,
                .function_index = analysis.function.id.index(),
                .branch = incoming[0].source,
                .entry = block,
                .join = block,
                .incoming = owned_incoming,
                .closure = closure,
            };
        }
        allocator.free(closure);
    }

    if (try internalSccBoundaryClosureAlloc(
        allocator,
        program,
        analysis,
        block,
        incoming,
        replay_context,
    )) |scc_closure| {
        const owned_incoming = try allocator.dupe(ir.CfgEdgeRef, incoming);
        return .{
            .allocator = allocator,
            .function_index = analysis.function.id.index(),
            .branch = incoming[0].source,
            .entry = block,
            .join = block,
            .incoming = owned_incoming,
            .closure = scc_closure,
        };
    }

    if (target.parameters.len != 0) {
        var closure = try allocator.alloc(ir.BlockId, 1);
        var retain_closure = false;
        defer if (!retain_closure) allocator.free(closure);
        closure[0] = block;
        // A parameterized entry can feed a shared forwarding suffix even when
        // the entry itself is the only collided block. Retain only the
        // suffix blocks that consume its mapped values before validating the
        // clone; otherwise the availability audit sees the original producer
        // as unreachable after the incoming edge is redirected.
        closure = try extendClosureForExternalUsesAlloc(
            allocator,
            program,
            analysis,
            block,
            closure,
            incoming,
        );
        closure = try extendAuthenticatedGroupBoundaryContextAlloc(
            allocator,
            program,
            analysis,
            closure,
            incoming,
            &replay_context.lineage_index,
            &replay_context.replay_index,
        );
        closure = (try trimIncomingSourceClosureAlloc(
            allocator,
            analysis,
            block,
            closure,
            incoming,
        )) orelse return null;
        if (!prepareClosureWithReplayContext(
            allocator,
            program,
            analysis,
            closure,
            incoming,
            replay_context,
        )) {
            return null;
        }
        traceStructural("structural_phase collision_parameterized_boundary_split function={} block={} incoming={}\n", .{
            analysis.function.id.index(),
            block.index(),
            incoming.len,
        });
        const owned_incoming = try allocator.dupe(ir.CfgEdgeRef, incoming);
        retain_closure = true;
        return .{
            .allocator = allocator,
            .function_index = analysis.function.id.index(),
            .branch = incoming[0].source,
            .entry = block,
            .join = block,
            .incoming = owned_incoming,
            .closure = closure,
        };
    }
    switch (target.terminator) {
        .jump, .branch => {},
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return null,
    }

    // Cloning an empty pure forwarding jump inside an SCC does not project any
    // observable state and can simply move the ownership collision around the
    // cycle.  A non-empty block is eligible only when its exact-pure results
    // are proven dead, which gives the same semantic boundary without
    // treating a live value-producing block as transparent.
    var has_observable_boundary = switch (target.terminator) {
        .branch => true,
        else => false,
    };
    for (target.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return null;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or instruction.block != block) return null;
        has_observable_boundary = has_observable_boundary or
            proof_effect_closure.hasObservableEffects(instruction.effects);
    }
    const dead_pure_forwarding = if (has_observable_boundary)
        false
    else
        try isDeadPureForwardingBlock(allocator, program, analysis, block);
    if (!has_observable_boundary and !dead_pure_forwarding) return null;
    if (dead_pure_forwarding) {
        traceStructural("structural_phase collision_dead_pure_forwarding_boundary function={} block={} incoming={}\n", .{
            analysis.function.id.index(),
            block.index(),
            incoming.len,
        });
    }

    const closure = try allocator.alloc(ir.BlockId, 1);
    closure[0] = block;
    if (!prepareClosureWithReplayContext(
        allocator,
        program,
        analysis,
        closure,
        incoming,
        replay_context,
    )) {
        allocator.free(closure);
        return null;
    }

    const owned_incoming = try allocator.dupe(ir.CfgEdgeRef, incoming);
    return .{
        .allocator = allocator,
        .function_index = analysis.function.id.index(),
        .branch = incoming[0].source,
        .entry = block,
        .join = block,
        .incoming = owned_incoming,
        .closure = closure,
    };
}

pub fn findCollisionSplitAllocWithAnalysisAndReplayContext(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    function_index: usize,
    block: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    replay_context: *ReplayProjectionContext,
) std.mem.Allocator.Error!?Split {
    if (function_index >= program.functions.len or incoming.len == 0 or
        analysis.function.id != program.functions[function_index].id)
    {
        return null;
    }
    for (incoming) |reference| {
        if (reference.target != block) return null;
        const live = directEdgeRef(program, reference.source, block) orelse return null;
        if (!analysis.isReachable(reference.source) or !std.meta.eql(live, reference)) return null;
    }

    const candidate_scan_start = structuralPhaseNow();
    const block_index = analysis.blockIndex(block) orelse return null;
    const loop_headers = try natural_loop.headerCandidatesAlloc(allocator, analysis);
    defer allocator.free(loop_headers);
    var selected_header: ?ir.BlockId = null;
    var selected_size: usize = std.math.maxInt(usize);
    var has_internal_loop_source = false;
    for (analysis.function.blocks, 0..) |candidate, candidate_index| {
        if (!loop_headers[candidate_index] or !analysis.dominates(candidate, block)) continue;
        var candidate_membership = natural_loop.collect(allocator, analysis, candidate) catch |err| switch (err) {
            error.UnsupportedShape => continue,
            error.OutOfMemory => return error.OutOfMemory,
        } orelse continue;
        defer candidate_membership.deinit();
        if (!candidate_membership.bits[block_index]) continue;
        var contains_source = false;
        for (incoming) |reference| {
            const source_index = analysis.blockIndex(reference.source) orelse return null;
            if (candidate_membership.bits[source_index]) {
                contains_source = true;
                break;
            }
        }
        if (contains_source) {
            has_internal_loop_source = true;
            continue;
        }
        const size = std.mem.countScalar(bool, candidate_membership.bits, true);
        if (size < selected_size or
            (size == selected_size and (selected_header == null or candidate.index() < selected_header.?.index())))
        {
            selected_header = candidate;
            selected_size = size;
        }
    }
    traceStructural("structural_phase collision_scan function={} block={} incoming={} selected={?d} selected_size={} ms={}\n", .{
        function_index,
        block.index(),
        incoming.len,
        if (selected_header) |header_id| header_id.index() else null,
        if (selected_header != null) selected_size else 0,
        structuralPhaseMillis(candidate_scan_start),
    });
    const header = selected_header orelse block;
    var closure = if (selected_header) |owner| closure: {
        var membership = natural_loop.collect(allocator, analysis, owner) catch |err| switch (err) {
            error.UnsupportedShape => return null,
            error.OutOfMemory => return error.OutOfMemory,
        } orelse return null;
        defer membership.deinit();
        break :closure try collectConditionalLoopClosureAlloc(allocator, analysis, membership.bits);
    } else try collectAcyclicCollisionClosureAlloc(allocator, analysis, block);
    errdefer allocator.free(closure);
    const extension_start = structuralPhaseNow();
    closure = try extendContinuationClosureAlloc(allocator, program, analysis, header, closure, incoming);
    traceStructural("structural_phase collision_extension function={} block={} header={} closure={} ms={}\n", .{
        function_index,
        block.index(),
        header.index(),
        closure.len,
        structuralPhaseMillis(extension_start),
    });
    if (selected_header == null and has_internal_loop_source and
        !(try internalLoopEffectfulSuffixCanBeCloned(
            allocator,
            program,
            analysis,
            loop_headers,
            block,
            closure,
            incoming,
        )))
    {
        const target = program.blocks[block.index()];
        const has_branch_boundary = switch (target.terminator) {
            .branch => true,
            else => false,
        };
        const has_effect_boundary = blk: {
            for (target.instructions) |instruction_id| {
                if (instruction_id.index() >= program.instructions.len) break :blk false;
                if (proof_effect_closure.hasObservableEffects(
                    program.instructions[instruction_id.index()].effects,
                )) break :blk true;
            }
            break :blk false;
        };
        // A non-empty exact-pure block can also be a valid boundary when its
        // results are dead; boundaryCloneSplitAlloc performs that liveness
        // proof. An empty forwarding jump remains unsafe inside this loop.
        if (has_branch_boundary or has_effect_boundary or target.instructions.len != 0) {
            if (try boundaryCloneSplitAlloc(
                allocator,
                program,
                analysis,
                block,
                incoming,
                replay_context,
            )) |boundary_split| {
                traceStructural("structural_phase collision_boundary_branch_split function={} block={} incoming={}\n", .{
                    function_index,
                    block.index(),
                    incoming.len,
                });
                allocator.free(closure);
                return boundary_split;
            }
        }
        traceStructural("structural_phase collision_reject_internal_loop_suffix function={} block={} closure={} incoming={any}\n", .{
            function_index,
            block.index(),
            closure.len,
            incoming,
        });
        allocator.free(closure);
        return null;
    }
    // Redirecting an edge whose source is inside the clone would copy the
    // edge's own loop body and leave the same collision at the cloned entry.
    // Loop-header selection already avoids this shape; continuation extension
    // must preserve that boundary instead of reintroducing it downstream.
    for (incoming) |reference| {
        if (containsBlock(closure, reference.source)) {
            traceStructural("structural_phase collision_reject_internal_source function={} block={} source={} closure={}\n", .{
                function_index,
                block.index(),
                reference.source.index(),
                closure.len,
            });
            traceStructural("structural_phase collision_internal_source_closure function={} block={} source={} closure_ids={any} incoming={any}\n", .{
                function_index,
                block.index(),
                reference.source.index(),
                closure,
                incoming,
            });
            // Loop continuation extension can pull an incoming source into a
            // selected loop closure even when the collided entry itself was
            // not the selected loop header. Reuse the authenticated boundary
            // proof before rejecting that shape; the helper still rejects
            // pure forwarding blocks and unprepared value boundaries.
            const target = program.blocks[block.index()];
            const has_branch_boundary = switch (target.terminator) {
                .branch => true,
                else => false,
            };
            const has_effect_boundary = blk: {
                for (target.instructions) |instruction_id| {
                    if (instruction_id.index() >= program.instructions.len) break :blk false;
                    if (proof_effect_closure.hasObservableEffects(
                        program.instructions[instruction_id.index()].effects,
                    )) break :blk true;
                }
                break :blk false;
            };
            if (has_branch_boundary or has_effect_boundary) {
                if (try boundaryCloneSplitAlloc(
                    allocator,
                    program,
                    analysis,
                    block,
                    incoming,
                    replay_context,
                )) |boundary_split| {
                    traceStructural("structural_phase collision_internal_source_boundary_split function={} block={} incoming={}\n", .{
                        function_index,
                        block.index(),
                        incoming.len,
                    });
                    allocator.free(closure);
                    return boundary_split;
                }
            }
            allocator.free(closure);
            return null;
        }
    }
    const prepare_start = structuralPhaseNow();
    const prepared = prepareClosureWithReplayContext(
        allocator,
        program,
        analysis,
        closure,
        incoming,
        replay_context,
    );
    traceStructural("structural_phase collision_prepare function={} block={} header={} closure={} prepared={} ms={}\n", .{
        function_index,
        block.index(),
        header.index(),
        closure.len,
        prepared,
        structuralPhaseMillis(prepare_start),
    });
    if (!prepared) {
        std.debug.print("structural_collision_prepare_failure block={} header={} closure={any} incoming={any}\n", .{
            block.index(),
            header.index(),
            closure,
            incoming,
        });
        allocator.free(closure);

        // A boundary-only clone is not a valid substitute for an
        // unauthenticated continuation.  It leaves downstream uses in the
        // wrong context and can make feedback repeatedly clone the same
        // boundary.  Let the caller choose an authenticated contextual split
        // instead.
        return null;
    }
    const owned_incoming = try allocator.dupe(ir.CfgEdgeRef, incoming);
    return .{
        .allocator = allocator,
        .function_index = function_index,
        .branch = incoming[0].source,
        .entry = block,
        .join = header,
        .incoming = owned_incoming,
        .closure = closure,
    };
}

test "collision closure rejects an incoming source inside its loop" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const body = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .jump = .{ .target = body } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = source },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, source, target, body, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program = ir.Program{
        .program_id = "collision-internal-incoming-source",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = source,
        .kind = .jump,
        .target = target,
    }};
    const collision_split = try findCollisionSplitAllocWithAnalysisAndReplayContext(
        std.testing.allocator,
        &program,
        &analysis,
        0,
        target,
        &incoming,
        &replay,
    );
    if (collision_split) |split_value| {
        var split = split_value;
        split.deinit();
    }
    try std.testing.expect(collision_split == null);
}

test "dead pure forwarding boundary clones its one-block projection" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const body = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const dead_value = ir.ValueId.fromIndex(1);
    const constant = ir.InstructionId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .instructions = &.{constant}, .terminator = .{ .jump = .{ .target = body } } },
        .{ .id = body, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = source },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, source, target, body, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{
            .id = condition,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .parameter = 0 },
        },
        .{
            .id = dead_value,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .instruction_result = .{ .instruction = constant, .index = 0 } },
        },
    };
    const instructions = [_]ir.Instruction{.{
        .id = constant,
        .block = target,
        .operation = .{ .constant = .{ .boolean = true } },
        .results = &.{dead_value},
        .effects = ir.EffectSummary.pure,
    }};
    const program = ir.Program{
        .program_id = "dead-pure-forwarding-boundary",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = source,
        .kind = .jump,
        .target = target,
    }};

    var split = (try findCollisionSplitAllocWithAnalysisAndReplayContext(
        std.testing.allocator,
        &program,
        &analysis,
        0,
        target,
        &incoming,
        &replay,
    )) orelse return error.TestUnexpectedResult;
    defer split.deinit();
    try std.testing.expectEqual(target, split.entry);
    try std.testing.expectEqual(target, split.join);
    try std.testing.expectEqualSlices(ir.BlockId, &.{target}, split.closure);
}

test "branching internal SCC boundary clones only its authenticated block" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const body = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const observed = ir.ValueId.fromIndex(0);
    const read = ir.InstructionId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .instructions = &.{read}, .terminator = .{ .branch = .{
            .condition = observed,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, source, target, body, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = observed,
        .function = function_id,
        .type = .dynamic,
        .origin = .{ .instruction_result = .{ .instruction = read, .index = 0 } },
    }};
    const instructions = [_]ir.Instruction{.{
        .id = read,
        .block = target,
        .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "shared" } },
        .results = &.{observed},
        .effects = ir.EffectSummary.semantic_environment_read,
    }};
    const program = ir.Program{
        .program_id = "branching-internal-scc-boundary",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = source,
        .kind = .jump,
        .target = target,
    }};

    var split = (try findCollisionSplitAllocWithAnalysisAndReplayContext(
        std.testing.allocator,
        &program,
        &analysis,
        0,
        target,
        &incoming,
        &replay,
    )) orelse return error.TestUnexpectedResult;
    defer split.deinit();
    try std.testing.expectEqual(target, split.entry);
    try std.testing.expectEqual(target, split.join);
    try std.testing.expectEqualSlices(ir.BlockId, &.{target}, split.closure);
}

test "authenticated zero-parameter group SCC boundary requires complete replay ownership" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const root = ir.BlockId.fromIndex(1);
    const source = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const next = ir.BlockId.fromIndex(4);
    const root_clone = ir.BlockId.fromIndex(5);
    const source_clone = ir.BlockId.fromIndex(6);
    const target_clone = ir.BlockId.fromIndex(7);
    const next_clone = ir.BlockId.fromIndex(8);
    const exit = ir.BlockId.fromIndex(9);

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = root_clone } } },
        .{ .id = root, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .jump = .{ .target = next } } },
        .{ .id = next, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = root },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = root_clone, .function = function_id, .terminator = .{ .jump = .{ .target = source_clone } } },
        .{ .id = source_clone, .function = function_id, .terminator = .{ .jump = .{ .target = target_clone } } },
        .{ .id = target_clone, .function = function_id, .terminator = .{ .jump = .{ .target = next_clone } } },
        .{ .id = next_clone, .function = function_id, .terminator = .{ .branch = .{
            .condition = ir.ValueId.fromIndex(0),
            .then_edge = .{ .target = root_clone },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ir.ValueId.fromIndex(0)},
        .blocks = &.{ entry, root, source, target, next, root_clone, source_clone, target_clone, next_clone, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = ir.ValueId.fromIndex(0),
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{ .id = ir.EdgeRewriteId.fromIndex(0), .source = entry, .kind = .jump, .from = .{ .target = root }, .to = .{ .target = root_clone }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(1), .source = root_clone, .kind = .jump, .from = .{ .target = source }, .to = .{ .target = source_clone }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(2), .source = source_clone, .kind = .jump, .from = .{ .target = target }, .to = .{ .target = target_clone }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(3), .source = target_clone, .kind = .jump, .from = .{ .target = next }, .to = .{ .target = next_clone }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(4), .source = next_clone, .kind = .branch_then, .from = .{ .target = root }, .to = .{ .target = root_clone }, .rule = .node_split, .node_split_group = group },
    };
    var program = ir.Program{
        .program_id = "authenticated-zero-parameter-group-scc-boundary",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = root_clone,
        .kind = .jump,
        .target = source_clone,
    }};
    const closure = (try internalSccBoundaryClosureAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        source_clone,
        &incoming,
        &replay,
    )) orelse return error.TestUnexpectedResult;
    defer std.testing.allocator.free(closure);
    try std.testing.expectEqualSlices(ir.BlockId, &.{ source_clone, target_clone, next_clone }, closure);

    var tampered_rewrites = rewrites;
    tampered_rewrites[1].node_split_group = null;
    var tampered_program = program;
    tampered_program.edge_rewrites = &tampered_rewrites;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, function);
    defer tampered_analysis.deinit();
    var tampered_replay = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &tampered_program,
        function_id,
    );
    defer tampered_replay.deinit();
    try std.testing.expect((try internalSccBoundaryClosureAlloc(
        std.testing.allocator,
        &tampered_program,
        &tampered_analysis,
        source_clone,
        &incoming,
        &tampered_replay,
    )) == null);
}

test "contextual closure treats an incoming source as an external cycle boundary" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const middle = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const selector = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = source },
            .else_edge = .{ .target = target },
        } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .jump = .{ .target = middle } } },
        .{ .id = middle, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ entry, source, target, middle, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{.{
        .id = selector,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program = ir.Program{
        .program_id = "contextual-incoming-source-boundary",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = source,
        .kind = .jump,
        .target = target,
    }};
    const closure = try std.testing.allocator.dupe(ir.BlockId, &.{ target, middle, source });
    const trimmed = (try trimIncomingSourceClosureAlloc(
        std.testing.allocator,
        &analysis,
        target,
        closure,
        &incoming,
    )).?;
    defer std.testing.allocator.free(trimmed);
    try std.testing.expectEqualSlices(ir.BlockId, &.{ target, middle }, trimmed);
    try std.testing.expect(prepareClosure(
        std.testing.allocator,
        &program,
        &analysis,
        trimmed,
        &incoming,
    ));
}

test "continuation extension retains only the context-dependent sibling path" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const closure_entry = ir.BlockId.fromIndex(1);
    const dependent = ir.BlockId.fromIndex(2);
    const sibling = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const source_value = ir.ValueId.fromIndex(0);
    const closure_value = ir.ValueId.fromIndex(1);
    const exit_value = ir.ValueId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{
            .target = closure_entry,
            .arguments = &.{source_value},
        } } },
        .{ .id = closure_entry, .function = function_id, .parameters = &.{closure_value}, .terminator = .{ .branch = .{
            .condition = closure_value,
            .then_edge = .{ .target = dependent },
            .else_edge = .{ .target = sibling },
        } } },
        .{ .id = dependent, .function = function_id, .terminator = .{ .jump = .{
            .target = exit,
            .arguments = &.{closure_value},
        } } },
        .{ .id = sibling, .function = function_id, .terminator = .{ .jump = .{
            .target = exit,
            .arguments = &.{source_value},
        } } },
        .{ .id = exit, .function = function_id, .parameters = &.{exit_value}, .terminator = .{ .return_values = &.{exit_value} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{source_value},
        .blocks = &.{ entry, closure_entry, dependent, sibling, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = source_value, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = closure_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = closure_entry, .index = 0 } } },
        .{ .id = exit_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = exit, .index = 0 } } },
    };
    const program: ir.Program = .{
        .program_id = "minimal-continuation-extension",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const closure = try std.testing.allocator.dupe(ir.BlockId, &.{closure_entry});
    const extended = try extendContinuationClosureAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        exit,
        closure,
        null,
    );
    defer std.testing.allocator.free(extended);
    try std.testing.expectEqualSlices(ir.BlockId, &.{ closure_entry, dependent }, extended);

    var contextual_blocks = blocks;
    contextual_blocks[sibling.index()].terminator = .{ .jump = .{
        .target = exit,
        .arguments = &.{closure_value},
    } };
    var contextual_program = program;
    contextual_program.blocks = &contextual_blocks;
    var contextual_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &contextual_program,
        functions[0],
    );
    defer contextual_analysis.deinit();
    const contextual_closure = try std.testing.allocator.dupe(ir.BlockId, &.{closure_entry});
    const contextual_extended = try extendContinuationClosureAlloc(
        std.testing.allocator,
        &contextual_program,
        &contextual_analysis,
        exit,
        contextual_closure,
        null,
    );
    defer std.testing.allocator.free(contextual_extended);
    try std.testing.expectEqual(3, contextual_extended.len);
    try std.testing.expect(containsBlock(contextual_extended, dependent));
    try std.testing.expect(containsBlock(contextual_extended, sibling));
}

test "continuation extension retains an effectful zero-parameter suffix" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const closure_entry = ir.BlockId.fromIndex(1);
    const effectful = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const table = ir.ValueId.fromIndex(1);
    const make_table = ir.InstructionId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = closure_entry } } },
        .{ .id = closure_entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = effectful },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = effectful, .function = function_id, .instructions = &.{make_table}, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, closure_entry, effectful, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{
            .id = condition,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .parameter = 0 },
        },
        .{
            .id = table,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = make_table, .index = 0 } },
        },
    };
    const instructions = [_]ir.Instruction{.{
        .id = make_table,
        .block = effectful,
        .operation = .{ .make_table = {} },
        .results = &.{table},
        .effects = .table_constructor,
    }};
    const program: ir.Program = .{
        .program_id = "effectful-zero-parameter-continuation",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const closure = try std.testing.allocator.dupe(ir.BlockId, &.{closure_entry});
    const extended = try extendContinuationClosureAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        exit,
        closure,
        null,
    );
    defer std.testing.allocator.free(extended);
    try std.testing.expectEqualSlices(ir.BlockId, &.{ closure_entry, effectful }, extended);
}

test "continuation extension retains a delayed mapped use after a parameterized boundary" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const closure_entry = ir.BlockId.fromIndex(1);
    const parameterized_bridge = ir.BlockId.fromIndex(2);
    const delayed_use = ir.BlockId.fromIndex(3);
    const stop = ir.BlockId.fromIndex(4);
    const source_value = ir.ValueId.fromIndex(0);
    const closure_value = ir.ValueId.fromIndex(1);
    const bridge_value = ir.ValueId.fromIndex(2);

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = closure_entry, .arguments = &.{source_value} } } },
        .{ .id = closure_entry, .function = function_id, .parameters = &.{closure_value}, .terminator = .{ .jump = .{ .target = parameterized_bridge, .arguments = &.{closure_value} } } },
        .{ .id = parameterized_bridge, .function = function_id, .parameters = &.{bridge_value}, .terminator = .{ .jump = .{ .target = delayed_use } } },
        .{ .id = delayed_use, .function = function_id, .terminator = .{ .jump = .{ .target = stop, .arguments = &.{closure_value} } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{source_value},
        .blocks = &.{ entry, closure_entry, parameterized_bridge, delayed_use, stop },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = source_value, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = closure_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = closure_entry, .index = 0 } } },
        .{ .id = bridge_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = parameterized_bridge, .index = 0 } } },
    };
    const program: ir.Program = .{
        .program_id = "delayed-mapped-use-after-parameterized-boundary",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{ .source = entry, .kind = .jump, .target = closure_entry }};
    const closure = try std.testing.allocator.dupe(ir.BlockId, &.{closure_entry});
    const extended = try extendContinuationClosureAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        stop,
        closure,
        &incoming,
    );
    defer std.testing.allocator.free(extended);
    try std.testing.expectEqualSlices(
        ir.BlockId,
        &.{ closure_entry, parameterized_bridge, delayed_use },
        extended,
    );
    try std.testing.expect(prepareClosure(
        std.testing.allocator,
        &program,
        &analysis,
        extended,
        &incoming,
    ));
}

test "external-use projection rescans definitions added by the first pass" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const closure_entry = ir.BlockId.fromIndex(1);
    const first_consumer = ir.BlockId.fromIndex(2);
    const downstream_consumer = ir.BlockId.fromIndex(3);
    const stop = ir.BlockId.fromIndex(4);
    const source_value = ir.ValueId.fromIndex(0);
    const closure_value = ir.ValueId.fromIndex(1);
    const downstream_value = ir.ValueId.fromIndex(2);
    const first_copy = ir.InstructionId.fromIndex(0);
    const downstream_copy = ir.InstructionId.fromIndex(1);

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = closure_entry } } },
        .{ .id = closure_entry, .function = function_id, .instructions = &.{first_copy}, .terminator = .{ .jump = .{ .target = first_consumer } } },
        .{ .id = first_consumer, .function = function_id, .instructions = &.{downstream_copy}, .terminator = .{ .jump = .{ .target = downstream_consumer } } },
        .{ .id = downstream_consumer, .function = function_id, .terminator = .{ .return_values = &.{downstream_value} } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{source_value},
        .blocks = &.{ entry, closure_entry, first_consumer, downstream_consumer, stop },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = source_value, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = closure_value, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = first_copy, .index = 0 } } },
        .{ .id = downstream_value, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = downstream_copy, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = first_copy, .block = closure_entry, .operation = .{ .copy = source_value }, .results = &.{closure_value}, .effects = .pure },
        .{ .id = downstream_copy, .block = first_consumer, .operation = .{ .copy = closure_value }, .results = &.{downstream_value}, .effects = .pure },
    };
    const program = ir.Program{
        .program_id = "bounded-external-use-rescan",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const closure = try std.testing.allocator.dupe(ir.BlockId, &.{closure_entry});
    const projected = try extendClosureForExternalUsesAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        stop,
        closure,
        null,
    );
    defer std.testing.allocator.free(projected);
    try std.testing.expectEqualSlices(
        ir.BlockId,
        &.{ closure_entry, first_consumer, downstream_consumer },
        projected,
    );
}

test "continuation extension retains a shared effectful jump suffix before iteration handoff" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const source = ir.BlockId.fromIndex(2);
    const closure_entry = ir.BlockId.fromIndex(3);
    const forwarder = ir.BlockId.fromIndex(4);
    const alternate = ir.BlockId.fromIndex(5);
    const exit = ir.BlockId.fromIndex(6);

    const selector = ir.ValueId.fromIndex(0);
    const control = ir.ValueId.fromIndex(1);
    const limit = ir.ValueId.fromIndex(2);
    const step = ir.ValueId.fromIndex(3);
    const header_control = ir.ValueId.fromIndex(4);
    const header_limit = ir.ValueId.fromIndex(5);
    const header_step = ir.ValueId.fromIndex(6);
    const header_initial = ir.ValueId.fromIndex(7);
    const false_value = ir.ValueId.fromIndex(8);
    const has_next = ir.ValueId.fromIndex(9);
    const normalized_limit = ir.ValueId.fromIndex(10);
    const normalized_step = ir.ValueId.fromIndex(11);
    const next_control = ir.ValueId.fromIndex(12);
    const table = ir.ValueId.fromIndex(13);
    const false_instruction = ir.InstructionId.fromIndex(0);
    const transition_instruction = ir.InstructionId.fromIndex(1);
    const make_table = ir.InstructionId.fromIndex(2);

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{false_instruction}, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &.{ control, limit, step, false_value },
        } } },
        .{ .id = header, .function = function_id, .parameters = &.{
            header_control, header_limit, header_step, header_initial,
        }, .instructions = &.{transition_instruction}, .terminator = .{ .branch = .{
            .condition = has_next,
            .then_edge = .{ .target = source },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = source, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = closure_entry },
            .else_edge = .{ .target = alternate },
        } } },
        .{ .id = closure_entry, .function = function_id, .terminator = .{ .jump = .{ .target = forwarder } } },
        .{ .id = forwarder, .function = function_id, .instructions = &.{make_table}, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &.{ next_control, normalized_limit, normalized_step, false_value },
        } } },
        .{ .id = alternate, .function = function_id, .terminator = .{ .jump = .{ .target = forwarder } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, control, limit, step },
        .blocks = &.{ entry, header, source, closure_entry, forwarder, alternate, exit },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = control, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = limit, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } },
        .{ .id = step, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 3 } },
        .{ .id = header_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = header_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
        .{ .id = header_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
        .{ .id = header_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
        .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } },
        .{ .id = has_next, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 3 } } },
        .{ .id = table, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = make_table, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = false_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = transition_instruction, .block = header, .operation = .{ .numeric_for_next = .{
            .control = header_control,
            .limit = header_limit,
            .step = header_step,
            .initial = header_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ has_next, normalized_limit, normalized_step, next_control }, .effects = .numeric_for_next },
        .{ .id = make_table, .block = forwarder, .operation = .{ .make_table = {} }, .results = &.{table}, .effects = .table_constructor },
    };
    const program: ir.Program = .{
        .program_id = "shared-effectful-jump-suffix-iteration-handoff",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = source,
        .kind = .branch_then,
        .target = closure_entry,
    }};
    const closure = try std.testing.allocator.dupe(ir.BlockId, &.{closure_entry});
    const extended = try extendContinuationClosureAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        exit,
        closure,
        &incoming,
    );
    defer std.testing.allocator.free(extended);
    try std.testing.expectEqualSlices(ir.BlockId, &.{ closure_entry, forwarder }, extended);

    // The same suffix is also valid when its only reachable predecessor is
    // the admitted closure entry.  The iteration handoff proof must retain
    // the effectful suffix instead of rediscovering it on the next split.
    var uniquely_owned_blocks = blocks;
    uniquely_owned_blocks[source.index()].terminator = .{ .branch = .{
        .condition = selector,
        .then_edge = .{ .target = closure_entry },
        .else_edge = .{ .target = exit },
    } };
    uniquely_owned_blocks[alternate.index()].terminator = .{ .unreachable_block = {} };
    var uniquely_owned_program = program;
    uniquely_owned_program.blocks = &uniquely_owned_blocks;
    var uniquely_owned_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &uniquely_owned_program,
        function,
    );
    defer uniquely_owned_analysis.deinit();
    const uniquely_owned_closure = try std.testing.allocator.dupe(ir.BlockId, &.{closure_entry});
    const uniquely_owned_extended = try extendContinuationClosureAlloc(
        std.testing.allocator,
        &uniquely_owned_program,
        &uniquely_owned_analysis,
        header,
        uniquely_owned_closure,
        &incoming,
    );
    defer std.testing.allocator.free(uniquely_owned_extended);
    try std.testing.expectEqualSlices(
        ir.BlockId,
        &.{ closure_entry, forwarder },
        uniquely_owned_extended,
    );
}

test "continuation extension trims a shared context-independent suffix" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const frontier = ir.BlockId.fromIndex(1);
    const shared = ir.BlockId.fromIndex(2);
    const tail = ir.BlockId.fromIndex(3);
    const alternate = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = frontier },
            .else_edge = .{ .target = alternate },
        } } },
        .{ .id = frontier, .function = function_id, .terminator = .{ .jump = .{ .target = shared } } },
        .{ .id = shared, .function = function_id, .terminator = .{ .jump = .{ .target = tail } } },
        .{ .id = tail, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = alternate, .function = function_id, .terminator = .{ .jump = .{ .target = shared } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, frontier, shared, tail, alternate },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{.{
        .id = condition,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const program: ir.Program = .{
        .program_id = "shared-context-independent-continuation-suffix",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = entry,
        .kind = .branch_then,
        .target = frontier,
    }};

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const initial = try std.testing.allocator.dupe(ir.BlockId, &.{ shared, frontier, tail });
    const trimmed = try trimContextIndependentSharedSuffixAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        entry,
        initial,
        &incoming,
    );
    defer std.testing.allocator.free(trimmed);
    try std.testing.expectEqualSlices(ir.BlockId, &.{frontier}, trimmed);
}

test "continuation extension retains an effectful shared suffix" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const frontier = ir.BlockId.fromIndex(1);
    const shared = ir.BlockId.fromIndex(2);
    const tail = ir.BlockId.fromIndex(3);
    const alternate = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const table = ir.ValueId.fromIndex(1);
    const make_table = ir.InstructionId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = frontier },
            .else_edge = .{ .target = alternate },
        } } },
        .{ .id = frontier, .function = function_id, .terminator = .{ .jump = .{ .target = shared } } },
        .{ .id = shared, .function = function_id, .instructions = &.{make_table}, .terminator = .{ .jump = .{ .target = tail } } },
        .{ .id = tail, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = alternate, .function = function_id, .terminator = .{ .jump = .{ .target = shared } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{condition},
        .blocks = &.{ entry, frontier, shared, tail, alternate },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{
            .id = condition,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .parameter = 0 },
        },
        .{
            .id = table,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = make_table, .index = 0 } },
        },
    };
    const instructions = [_]ir.Instruction{.{
        .id = make_table,
        .block = shared,
        .operation = .{ .make_table = {} },
        .results = &.{table},
        .effects = .table_constructor,
    }};
    const program: ir.Program = .{
        .program_id = "effectful-shared-context-independent-suffix",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = entry,
        .kind = .branch_then,
        .target = frontier,
    }};

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const initial = try std.testing.allocator.dupe(ir.BlockId, &.{ shared, frontier, tail });
    const retained = try trimContextIndependentSharedSuffixAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        entry,
        initial,
        &incoming,
    );
    defer std.testing.allocator.free(retained);
    try std.testing.expectEqualSlices(ir.BlockId, &.{ shared, frontier, tail }, retained);
}

test "shared suffix trimming retains every effectful operation category" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const frontier = ir.BlockId.fromIndex(1);
    const shared = ir.BlockId.fromIndex(2);
    const tail = ir.BlockId.fromIndex(3);
    const alternate = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(1);
    const table = ir.ValueId.fromIndex(2);
    const key = ir.ValueId.fromIndex(3);
    const value = ir.ValueId.fromIndex(4);
    const place_id = ir.PlaceId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const local_places = [_]ir.PlaceId{place_id};
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = frontier },
            .else_edge = .{ .target = alternate },
        } } },
        .{ .id = frontier, .function = function_id, .terminator = .{ .jump = .{ .target = shared } } },
        .{ .id = shared, .function = function_id, .instructions = &.{instruction_id}, .terminator = .{ .jump = .{ .target = tail } } },
        .{ .id = tail, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = alternate, .function = function_id, .terminator = .{ .jump = .{ .target = shared } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ condition, callee, table, key, value },
        .local_places = &local_places,
        .blocks = &.{ entry, frontier, shared, tail, alternate },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = callee, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = table, .function = function_id, .origin = .{ .parameter = 2 } },
        .{ .id = key, .function = function_id, .origin = .{ .parameter = 3 } },
        .{ .id = value, .function = function_id, .origin = .{ .parameter = 4 } },
    };
    const places = [_]ir.Place{.{
        .id = place_id,
        .function = function_id,
        .origin = .{ .local = 0 },
    }};
    var instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = shared,
        .operation = .{ .place_write = .{ .place = place_id, .value = value } },
        .results = &.{},
        .effects = .place_write,
    }};
    const program: ir.Program = .{
        .program_id = "effectful-shared-suffix-operation-matrix",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = entry,
        .kind = .branch_then,
        .target = frontier,
    }};
    const cases = [_]struct {
        operation: ir.Operation,
        effects: ir.EffectSummary,
    }{
        .{ .operation = .{ .place_write = .{ .place = place_id, .value = value } }, .effects = .place_write },
        .{ .operation = .{ .table_get = .{ .table = table, .key = key } }, .effects = .semantic_table_read },
        .{ .operation = .{ .table_set = .{ .table = table, .key = key, .value = value } }, .effects = .semantic_table_write },
        .{ .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "shared" } }, .effects = .semantic_environment_read },
        .{ .operation = .{ .environment_set = .{ .target = .{ .ambient = {} }, .name = "shared", .value = value } }, .effects = .semantic_environment_write },
        .{ .operation = .{ .call = .{ .callee = callee, .arguments = &.{value}, .result_arity = .{ .fixed = 0 } } }, .effects = .dynamic_call },
        .{ .operation = .{ .coroutine_yield = .{ .arguments = &.{value}, .result_arity = .{ .fixed = 0 } } }, .effects = .coroutine_yield },
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    for (cases) |case| {
        instructions[0].operation = case.operation;
        instructions[0].effects = case.effects;
        const initial = try std.testing.allocator.dupe(ir.BlockId, &.{ shared, frontier, tail });
        const retained = try trimContextIndependentSharedSuffixAlloc(
            std.testing.allocator,
            &program,
            &analysis,
            tail,
            initial,
            &incoming,
        );
        defer std.testing.allocator.free(retained);
        try std.testing.expectEqualSlices(ir.BlockId, &.{ shared, frontier, tail }, retained);
    }
}

test "shared suffix trimming retains a throw terminator" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const frontier = ir.BlockId.fromIndex(1);
    const shared = ir.BlockId.fromIndex(2);
    const tail = ir.BlockId.fromIndex(3);
    const alternate = ir.BlockId.fromIndex(4);
    const condition = ir.ValueId.fromIndex(0);
    const error_value = ir.ValueId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = frontier },
            .else_edge = .{ .target = alternate },
        } } },
        .{ .id = frontier, .function = function_id, .terminator = .{ .jump = .{ .target = shared } } },
        .{ .id = shared, .function = function_id, .terminator = .{ .throw_error = .{ .value = error_value, .level = 0 } } },
        .{ .id = tail, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = alternate, .function = function_id, .terminator = .{ .jump = .{ .target = shared } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ condition, error_value },
        .blocks = &.{ entry, frontier, shared, tail, alternate },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = error_value, .function = function_id, .origin = .{ .parameter = 1 } },
    };
    const program: ir.Program = .{
        .program_id = "throwing-shared-suffix",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = entry,
        .kind = .branch_then,
        .target = frontier,
    }};

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const initial = try std.testing.allocator.dupe(ir.BlockId, &.{ shared, frontier, tail });
    const retained = try trimContextIndependentSharedSuffixAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        tail,
        initial,
        &incoming,
    );
    defer std.testing.allocator.free(retained);
    try std.testing.expectEqualSlices(ir.BlockId, &.{ shared, frontier, tail }, retained);
}

test "shared suffix trimming retains aliases sourced from incoming edge arguments" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const frontier = ir.BlockId.fromIndex(1);
    const shared = ir.BlockId.fromIndex(2);
    const tail = ir.BlockId.fromIndex(3);
    const alternate = ir.BlockId.fromIndex(4);
    const selector = ir.ValueId.fromIndex(0);
    const seed = ir.ValueId.fromIndex(1);
    const frontier_value = ir.ValueId.fromIndex(2);
    const alias_value = ir.ValueId.fromIndex(3);
    const alias_instruction = ir.InstructionId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = frontier, .arguments = &.{seed} },
            .else_edge = .{ .target = alternate },
        } } },
        .{ .id = frontier, .function = function_id, .parameters = &.{frontier_value}, .terminator = .{ .jump = .{ .target = shared } } },
        .{ .id = shared, .function = function_id, .instructions = &.{alias_instruction}, .terminator = .{ .jump = .{ .target = tail } } },
        .{ .id = tail, .function = function_id, .terminator = .{ .return_values = &.{alias_value} } },
        .{ .id = alternate, .function = function_id, .terminator = .{ .jump = .{ .target = shared } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, seed },
        .blocks = &.{ entry, frontier, shared, tail, alternate },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = seed, .function = function_id, .origin = .{ .parameter = 1 } },
        .{ .id = frontier_value, .function = function_id, .origin = .{ .block_parameter = .{ .block = frontier, .index = 0 } } },
        .{ .id = alias_value, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = alias_instruction, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = alias_instruction,
        .block = shared,
        .operation = .{ .copy = frontier_value },
        .results = &.{alias_value},
        .effects = .pure,
    }};
    const program: ir.Program = .{
        .program_id = "incoming-edge-argument-alias-shared-suffix",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = entry,
        .kind = .branch_then,
        .target = frontier,
    }};

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const initial = try std.testing.allocator.dupe(ir.BlockId, &.{ shared, frontier, tail });
    const retained = try trimContextIndependentSharedSuffixAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        tail,
        initial,
        &incoming,
    );
    defer std.testing.allocator.free(retained);
    try std.testing.expectEqualSlices(ir.BlockId, &.{ shared, frontier, tail }, retained);
}

test "non-dominating exact constants remain rematerializable continuation values" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const incoming_source = ir.BlockId.fromIndex(2);
    const consumer = ir.BlockId.fromIndex(3);
    const selector = ir.ValueId.fromIndex(0);
    const constant_value = ir.ValueId.fromIndex(1);
    const constant_instruction = ir.InstructionId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = producer },
            .else_edge = .{ .target = incoming_source },
        } } },
        .{ .id = producer, .function = function_id, .instructions = &.{constant_instruction}, .terminator = .{ .jump = .{ .target = consumer } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{ .target = consumer } } },
        .{ .id = consumer, .function = function_id, .terminator = .{ .return_values = &.{constant_value} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ entry, producer, incoming_source, consumer },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = constant_value, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = constant_instruction, .index = 0 } } },
    };
    var instructions = [_]ir.Instruction{.{
        .id = constant_instruction,
        .block = producer,
        .operation = .{ .constant = .{ .nil_value = {} } },
        .results = &.{constant_value},
        .effects = .pure,
    }};
    const program: ir.Program = .{
        .program_id = "non-dominating-rematerializable-constant",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = incoming_source,
        .kind = .jump,
        .target = consumer,
    }};

    try std.testing.expect(!analysis.dominates(producer, incoming_source));
    try std.testing.expectEqual(
        ContinuationValueContext.available,
        try valueCarriesContinuationContext(
            std.testing.allocator,
            &program,
            &analysis,
            constant_value,
            consumer,
            &.{},
            &.{consumer},
            &incoming,
            null,
            null,
            null,
        ),
    );

    instructions[0].effects = .place_read;
    try std.testing.expectEqual(
        ContinuationValueContext.unavailable,
        try valueCarriesContinuationContext(
            std.testing.allocator,
            &program,
            &analysis,
            constant_value,
            consumer,
            &.{},
            &.{consumer},
            &incoming,
            null,
            null,
            null,
        ),
    );
}

test "contextual-use detection ignores rematerializable constants" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const incoming_source = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const selector = ir.ValueId.fromIndex(0);
    const constant_value = ir.ValueId.fromIndex(1);
    const copied_value = ir.ValueId.fromIndex(2);
    const constant_instruction = ir.InstructionId.fromIndex(0);
    const copy_instruction = ir.InstructionId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{copy_instruction}, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = producer },
            .else_edge = .{ .target = incoming_source },
        } } },
        .{ .id = producer, .function = function_id, .instructions = &.{constant_instruction}, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ entry, producer, incoming_source, target },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = constant_value, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = constant_instruction, .index = 0 } } },
        .{ .id = copied_value, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = copy_instruction, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = constant_instruction, .block = producer, .operation = .{ .constant = .{ .nil_value = {} } }, .results = &.{constant_value}, .effects = .pure },
        .{ .id = copy_instruction, .block = entry, .operation = .{ .copy = selector }, .results = &.{copied_value}, .effects = .pure },
    };
    const program = ir.Program{
        .program_id = "contextual-use-constant-filter",
        .entry_function = function_id,
        .functions = &.{functions[0]},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = ir.CfgEdgeRef{ .source = incoming_source, .kind = .jump, .target = target };
    var detector = ContextualValueUseDetector{
        .program = &program,
        .analysis = &analysis,
        .incoming = incoming,
        .target = target,
    };
    detector.value(constant_value);
    try std.testing.expect(!detector.found);
    detector.value(copied_value);
    try std.testing.expect(detector.found);
    try std.testing.expectEqual(copied_value, detector.value_id.?);
}

test "contextual boundary rejects an unprojected shared predecessor" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const incoming_source = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const shared_predecessor = ir.BlockId.fromIndex(3);
    const shared_consumer = ir.BlockId.fromIndex(4);
    const selector = ir.ValueId.fromIndex(0);
    const seed = ir.ValueId.fromIndex(1);
    const target_value = ir.ValueId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = incoming_source },
            .else_edge = .{ .target = shared_predecessor },
        } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &.{seed},
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{target_value}, .terminator = .{ .jump = .{
            .target = shared_consumer,
        } } },
        .{ .id = shared_predecessor, .function = function_id, .terminator = .{ .jump = .{
            .target = shared_consumer,
        } } },
        .{ .id = shared_consumer, .function = function_id, .terminator = .{ .return_values = &.{target_value} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, seed },
        .blocks = &.{ entry, incoming_source, target, shared_predecessor, shared_consumer },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = seed, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = target_value, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
    };
    const program = ir.Program{
        .program_id = "contextual-boundary-shared-predecessor",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = incoming_source,
        .kind = .jump,
        .target = target,
    }};
    const closure = [_]ir.BlockId{ target, shared_consumer };
    try std.testing.expect(!closureLocalUsesHaveProjectedBoundary(
        &program,
        &analysis,
        &closure,
        &incoming,
    ));
}

test "authenticated group carrier path rejects an unowned ingress before nested clones" {
    const function_id = ir.FunctionId.fromIndex(0);
    const root = ir.BlockId.fromIndex(0);
    const closure_entry = ir.BlockId.fromIndex(1);
    const unowned_ingress = ir.BlockId.fromIndex(2);
    const nested_carrier = ir.BlockId.fromIndex(3);
    const carrier = ir.BlockId.fromIndex(4);
    const target = ir.BlockId.fromIndex(5);
    const original_entry = ir.BlockId.fromIndex(6);
    const original_nested = ir.BlockId.fromIndex(7);
    const original_carrier = ir.BlockId.fromIndex(8);
    const original_target = ir.BlockId.fromIndex(9);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const nested_group = ir.NodeSplitGroupId.fromIndex(1);
    const carrier_group = ir.NodeSplitGroupId.fromIndex(2);
    const target_group = ir.NodeSplitGroupId.fromIndex(3);
    const blocks = [_]ir.Block{
        .{ .id = root, .function = function_id, .terminator = .{ .jump = .{ .target = closure_entry } } },
        .{ .id = closure_entry, .function = function_id, .terminator = .{ .jump = .{ .target = unowned_ingress } } },
        .{ .id = unowned_ingress, .function = function_id, .terminator = .{ .jump = .{ .target = nested_carrier } } },
        .{ .id = nested_carrier, .function = function_id, .terminator = .{ .jump = .{ .target = carrier } } },
        .{ .id = carrier, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original_entry, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original_nested, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original_carrier, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original_target, .function = function_id, .terminator = .{ .unreachable_block = {} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{
            root,
            closure_entry,
            unowned_ingress,
            nested_carrier,
            carrier,
            target,
            original_entry,
            original_nested,
            original_carrier,
            original_target,
        },
        .entry_block = root,
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{ .id = ir.EdgeRewriteId.fromIndex(0), .source = closure_entry, .kind = .jump, .from = .{ .target = original_entry }, .to = .{ .target = closure_entry }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(1), .source = nested_carrier, .kind = .jump, .from = .{ .target = original_nested }, .to = .{ .target = nested_carrier }, .rule = .node_split, .node_split_group = nested_group },
        .{ .id = ir.EdgeRewriteId.fromIndex(2), .source = carrier, .kind = .jump, .from = .{ .target = original_carrier }, .to = .{ .target = carrier }, .rule = .node_split, .node_split_group = carrier_group },
        .{ .id = ir.EdgeRewriteId.fromIndex(3), .source = target, .kind = .jump, .from = .{ .target = original_target }, .to = .{ .target = target }, .rule = .node_split, .node_split_group = target_group },
    };
    const program = ir.Program{
        .program_id = "nested-carrier-unowned-ingress",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };
    var analysis_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer analysis_arena.deinit();
    var analysis = try cfg.Analysis.init(analysis_arena.allocator(), &program, function);
    defer analysis.deinit();
    var replay_index = try node_split.ReplayIndex.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay_index.deinit();
    var membership = [_]bool{ false, true, false, false, false, false, false, false, false, false };
    var expanded: std.ArrayList(ir.BlockId) = .empty;
    defer expanded.deinit(std.testing.allocator);
    try expanded.append(std.testing.allocator, closure_entry);
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = root,
        .kind = .jump,
        .target = closure_entry,
    }};

    try std.testing.expect(!try appendAuthenticatedGroupCarrierPathAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        closure_entry,
        target,
        group,
        &incoming,
        &membership,
        &replay_index,
        &expanded,
    ));
    try std.testing.expectEqual(@as(usize, 1), expanded.items.len);
    try std.testing.expectEqual(closure_entry, expanded.items[0]);
}

test "authenticated carrier path rejects a reachable unconnected predecessor" {
    const function_id = ir.FunctionId.fromIndex(0);
    const root = ir.BlockId.fromIndex(0);
    const closure_entry = ir.BlockId.fromIndex(1);
    const carrier = ir.BlockId.fromIndex(2);
    const alternate = ir.BlockId.fromIndex(3);
    const target = ir.BlockId.fromIndex(4);
    const original_carrier = ir.BlockId.fromIndex(5);
    const original_target = ir.BlockId.fromIndex(6);
    const selector = ir.ValueId.fromIndex(0);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = root, .function = function_id, .terminator = .{ .jump = .{ .target = closure_entry } } },
        .{ .id = closure_entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = carrier },
            .else_edge = .{ .target = alternate },
        } } },
        .{ .id = carrier, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = alternate, .function = function_id, .terminator = .{ .jump = .{ .target = target } } },
        .{ .id = target, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original_carrier, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original_target, .function = function_id, .terminator = .{ .unreachable_block = {} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ root, closure_entry, carrier, alternate, target, original_carrier, original_target },
        .entry_block = root,
    };
    const values = [_]ir.Value{.{
        .id = selector,
        .function = function_id,
        .type = .boolean,
        .origin = .{ .parameter = 0 },
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{ .id = ir.EdgeRewriteId.fromIndex(0), .source = carrier, .kind = .jump, .from = .{ .target = original_carrier }, .to = .{ .target = carrier }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(1), .source = target, .kind = .jump, .from = .{ .target = original_target }, .to = .{ .target = target }, .rule = .node_split, .node_split_group = group },
    };
    const program = ir.Program{
        .program_id = "authenticated-carrier-reachable-unconnected-predecessor",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var replay_index = try node_split.ReplayIndex.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay_index.deinit();
    var membership = [_]bool{ false, true, false, false, false, false, false };
    var expanded: std.ArrayList(ir.BlockId) = .empty;
    defer expanded.deinit(std.testing.allocator);
    try expanded.append(std.testing.allocator, closure_entry);
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = root,
        .kind = .jump,
        .target = closure_entry,
    }};

    try std.testing.expect(!try appendAuthenticatedGroupCarrierPathAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        closure_entry,
        target,
        group,
        &incoming,
        &membership,
        &replay_index,
        &expanded,
    ));
    try std.testing.expectEqual(@as(usize, 1), expanded.items.len);
    try std.testing.expectEqual(closure_entry, expanded.items[0]);
}

test "authenticated carrier path keeps an alternate edge from the selected source" {
    const function_id = ir.FunctionId.fromIndex(0);
    const closure_entry = ir.BlockId.fromIndex(0);
    const incoming_source = ir.BlockId.fromIndex(1);
    const carrier = ir.BlockId.fromIndex(2);
    const external = ir.BlockId.fromIndex(3);
    const original_entry = ir.BlockId.fromIndex(4);
    const original_source = ir.BlockId.fromIndex(5);
    const original_carrier = ir.BlockId.fromIndex(6);
    const original_external = ir.BlockId.fromIndex(7);
    const selector = ir.ValueId.fromIndex(0);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = closure_entry, .function = function_id, .terminator = .{ .jump = .{ .target = incoming_source } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = closure_entry },
            .else_edge = .{ .target = carrier },
        } } },
        .{ .id = carrier, .function = function_id, .terminator = .{ .jump = .{ .target = external } } },
        .{ .id = external, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original_entry, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original_source, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original_carrier, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original_external, .function = function_id, .terminator = .{ .unreachable_block = {} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ closure_entry, incoming_source, carrier, external, original_entry, original_source, original_carrier, original_external },
        .entry_block = closure_entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{ .id = ir.EdgeRewriteId.fromIndex(0), .source = closure_entry, .kind = .jump, .from = .{ .target = original_entry }, .to = .{ .target = closure_entry }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(1), .source = incoming_source, .kind = .branch_else, .from = .{ .target = original_source }, .to = .{ .target = incoming_source }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(2), .source = carrier, .kind = .jump, .from = .{ .target = original_carrier }, .to = .{ .target = carrier }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(3), .source = external, .kind = .jump, .from = .{ .target = original_external }, .to = .{ .target = external }, .rule = .node_split, .node_split_group = group },
    };
    const program = ir.Program{
        .program_id = "authenticated-alternate-carrier-edge",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer analysis_arena.deinit();
    var analysis = try cfg.Analysis.init(analysis_arena.allocator(), &program, function);
    defer analysis.deinit();
    var replay_index = try node_split.ReplayIndex.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay_index.deinit();
    var membership = [_]bool{ true, false, false, false, false, false, false, false };
    var expanded: std.ArrayList(ir.BlockId) = .empty;
    defer expanded.deinit(std.testing.allocator);
    try expanded.append(std.testing.allocator, closure_entry);
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = incoming_source,
        .kind = .branch_then,
        .target = closure_entry,
    }};
    try std.testing.expect(try appendAuthenticatedGroupCarrierPathAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        closure_entry,
        external,
        group,
        &incoming,
        &membership,
        &replay_index,
        &expanded,
    ));
    try std.testing.expect(containsBlock(expanded.items, incoming_source));
    try std.testing.expect(containsBlock(expanded.items, carrier));
    try std.testing.expect(containsBlock(expanded.items, external));
}

test "authenticated carrier path retains an alternate predecessor of a target" {
    const function_id = ir.FunctionId.fromIndex(0);
    const root = ir.BlockId.fromIndex(0);
    const incoming_source = ir.BlockId.fromIndex(1);
    const closure_entry = ir.BlockId.fromIndex(2);
    const carrier = ir.BlockId.fromIndex(3);
    const external = ir.BlockId.fromIndex(4);
    const original_entry = ir.BlockId.fromIndex(5);
    const original_carrier = ir.BlockId.fromIndex(6);
    const original_external = ir.BlockId.fromIndex(7);
    const selector = ir.ValueId.fromIndex(0);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = root, .function = function_id, .terminator = .{ .jump = .{ .target = incoming_source } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{ .target = closure_entry } } },
        .{ .id = closure_entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = external },
            .else_edge = .{ .target = carrier },
        } } },
        .{ .id = carrier, .function = function_id, .terminator = .{ .jump = .{ .target = external } } },
        .{ .id = external, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = original_entry, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original_carrier, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original_external, .function = function_id, .terminator = .{ .unreachable_block = {} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ root, incoming_source, closure_entry, carrier, external, original_entry, original_carrier, original_external },
        .entry_block = root,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{ .id = ir.EdgeRewriteId.fromIndex(0), .source = carrier, .kind = .jump, .from = .{ .target = original_carrier }, .to = .{ .target = carrier }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(1), .source = external, .kind = .jump, .from = .{ .target = original_external }, .to = .{ .target = external }, .rule = .node_split, .node_split_group = group },
    };
    const program = ir.Program{
        .program_id = "authenticated-alternate-target-predecessor",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var analysis_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer analysis_arena.deinit();
    var analysis = try cfg.Analysis.init(analysis_arena.allocator(), &program, function);
    defer analysis.deinit();
    var replay_index = try node_split.ReplayIndex.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay_index.deinit();
    var membership = [_]bool{ false, false, true, false, false, false, false, false };
    var expanded: std.ArrayList(ir.BlockId) = .empty;
    defer expanded.deinit(std.testing.allocator);
    try expanded.append(std.testing.allocator, closure_entry);
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = incoming_source,
        .kind = .jump,
        .target = closure_entry,
    }};

    try std.testing.expect(try appendAuthenticatedGroupCarrierPathAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        closure_entry,
        external,
        group,
        &incoming,
        &membership,
        &replay_index,
        &expanded,
    ));
    try std.testing.expect(containsBlock(expanded.items, carrier));
    try std.testing.expect(containsBlock(expanded.items, external));
}

test "parameterized continuation admits an authenticated loop-carried SCC" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const producer = ir.BlockId.fromIndex(3);
    const stop = ir.BlockId.fromIndex(4);
    const selector = ir.ValueId.fromIndex(0);
    const producer_value = ir.ValueId.fromIndex(1);
    const target_value = ir.ValueId.fromIndex(2);
    const instruction_id = ir.InstructionId.fromIndex(0);
    var blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &.{producer_value},
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{target_value}, .terminator = .{ .jump = .{
            .target = producer,
            .arguments = &.{target_value},
        } } },
        .{ .id = producer, .function = function_id, .instructions = &.{instruction_id}, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = source },
            .else_edge = .{ .target = stop },
        } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ entry, source, target, producer, stop },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = producer_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
        .{ .id = target_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = producer,
        .operation = .{ .constant = .{ .number = 1 } },
        .results = &.{producer_value},
        .effects = .pure,
    }};
    var program: ir.Program = .{
        .program_id = "parameterized-loop-carried-continuation",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{ .source = entry, .kind = .jump, .target = source }};

    try std.testing.expect(try parameterizedContinuationBridge(
        std.testing.allocator,
        &program,
        &analysis,
        source,
        0,
        target,
        stop,
        &.{source},
        &.{},
        &incoming,
        null,
        null,
        null,
    ));

    var acyclic_blocks = blocks;
    acyclic_blocks[producer.index()].terminator = .{ .jump = .{ .target = stop } };
    var acyclic_program = program;
    acyclic_program.blocks = &acyclic_blocks;
    var acyclic_analysis = try cfg.Analysis.init(std.testing.allocator, &acyclic_program, functions[0]);
    defer acyclic_analysis.deinit();
    try std.testing.expect(!try parameterizedContinuationBridge(
        std.testing.allocator,
        &acyclic_program,
        &acyclic_analysis,
        source,
        0,
        target,
        stop,
        &.{source},
        &.{},
        &incoming,
        null,
        null,
        null,
    ));
}

test "parameterized continuation retains a bridge that forwards closure state" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const bridge = ir.BlockId.fromIndex(2);
    const sink = ir.BlockId.fromIndex(3);
    const source_argument = ir.ValueId.fromIndex(0);
    const forwarded_value = ir.ValueId.fromIndex(1);
    const bridge_parameter = ir.ValueId.fromIndex(2);
    const sink_parameter = ir.ValueId.fromIndex(3);
    const source_instruction = ir.InstructionId.fromIndex(0);
    const forwarded_instruction = ir.InstructionId.fromIndex(1);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .instructions = &.{ source_instruction, forwarded_instruction }, .terminator = .{ .jump = .{
            .target = bridge,
            .arguments = &.{source_argument},
        } } },
        .{ .id = bridge, .function = function_id, .parameters = &.{bridge_parameter}, .terminator = .{ .jump = .{
            .target = sink,
            .arguments = &.{forwarded_value},
        } } },
        .{ .id = sink, .function = function_id, .parameters = &.{sink_parameter}, .terminator = .{ .return_values = &.{sink_parameter} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{ entry, source, bridge, sink },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = source_argument, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = source_instruction, .index = 0 } } },
        .{ .id = forwarded_value, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = forwarded_instruction, .index = 0 } } },
        .{ .id = bridge_parameter, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = bridge, .index = 0 } } },
        .{ .id = sink_parameter, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = sink, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = source_instruction, .block = source, .operation = .{ .constant = .{ .number = 1 } }, .results = &.{source_argument}, .effects = .pure },
        .{ .id = forwarded_instruction, .block = source, .operation = .{ .constant = .{ .number = 2 } }, .results = &.{forwarded_value}, .effects = .pure },
    };
    const program: ir.Program = .{
        .program_id = "parameterized-bridge-forwards-closure-state",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{ .source = entry, .kind = .jump, .target = source }};
    const initial = try std.testing.allocator.dupe(ir.BlockId, &.{source});
    const extended = try extendContinuationClosureAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        entry,
        initial,
        &incoming,
    );
    defer std.testing.allocator.free(extended);
    try std.testing.expect(containsBlock(extended, bridge));
}

test "effectful tuple prefix reuses an authenticated parameterized suffix" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const prefix = ir.BlockId.fromIndex(1);
    const forwarder = ir.BlockId.fromIndex(2);
    const suffix = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);
    const alternate = ir.BlockId.fromIndex(5);

    const selector = ir.ValueId.fromIndex(0);
    const input_first = ir.ValueId.fromIndex(1);
    const input_second = ir.ValueId.fromIndex(2);
    const input_third = ir.ValueId.fromIndex(3);
    const input_fourth = ir.ValueId.fromIndex(4);
    const prefix_first = ir.ValueId.fromIndex(5);
    const prefix_second = ir.ValueId.fromIndex(6);
    const prefix_third = ir.ValueId.fromIndex(7);
    const prefix_fourth = ir.ValueId.fromIndex(8);
    const suffix_first = ir.ValueId.fromIndex(9);
    const suffix_second = ir.ValueId.fromIndex(10);
    const suffix_third = ir.ValueId.fromIndex(11);
    const suffix_fourth = ir.ValueId.fromIndex(12);
    const prefix_read = ir.ValueId.fromIndex(13);
    const prefix_constant = ir.ValueId.fromIndex(14);
    const prefix_condition = ir.ValueId.fromIndex(15);
    const forward_read = ir.ValueId.fromIndex(16);
    const tampered_value = ir.ValueId.fromIndex(17);

    const prefix_read_id = ir.InstructionId.fromIndex(0);
    const prefix_constant_id = ir.InstructionId.fromIndex(1);
    const prefix_compare_id = ir.InstructionId.fromIndex(2);
    const forward_read_id = ir.InstructionId.fromIndex(3);
    const forward_write_id = ir.InstructionId.fromIndex(4);
    const tampered_instruction_id = ir.InstructionId.fromIndex(5);

    const prefix_place = ir.PlaceId.fromIndex(0);
    const forward_read_place = ir.PlaceId.fromIndex(1);
    const forward_write_place = ir.PlaceId.fromIndex(2);
    const alternate_place = ir.PlaceId.fromIndex(3);
    const prefix_arguments = [_]ir.ValueId{ input_first, input_second, input_third, input_fourth };
    const prefix_tuple = [_]ir.ValueId{ prefix_first, prefix_second, prefix_third, prefix_fourth };
    const suffix_tuple = [_]ir.ValueId{ suffix_first, suffix_second, suffix_third, suffix_fourth };
    var tampered_tuple = prefix_tuple;
    tampered_tuple[0] = tampered_value;

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = prefix, .arguments = prefix_arguments[0..] },
            .else_edge = .{ .target = alternate },
        } } },
        .{ .id = prefix, .function = function_id, .parameters = prefix_tuple[0..], .instructions = &.{
            prefix_read_id,
            prefix_constant_id,
            prefix_compare_id,
        }, .terminator = .{ .branch = .{
            .condition = prefix_condition,
            .then_edge = .{ .target = exit },
            .else_edge = .{ .target = forwarder },
        } } },
        .{ .id = forwarder, .function = function_id, .instructions = &.{
            forward_read_id,
            forward_write_id,
        }, .terminator = .{ .jump = .{
            .target = suffix,
            .arguments = prefix_tuple[0..],
        } } },
        .{ .id = suffix, .function = function_id, .parameters = suffix_tuple[0..], .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = alternate, .function = function_id, .instructions = &.{tampered_instruction_id}, .terminator = .{ .jump = .{ .target = exit } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, input_first, input_second, input_third, input_fourth },
        .local_places = &.{ prefix_place, forward_read_place, forward_write_place, alternate_place },
        .blocks = &.{ entry, prefix, forwarder, suffix, exit, alternate },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = input_first, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = input_second, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } },
        .{ .id = input_third, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 3 } },
        .{ .id = input_fourth, .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } },
        .{ .id = prefix_first, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = prefix, .index = 0 } } },
        .{ .id = prefix_second, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = prefix, .index = 1 } } },
        .{ .id = prefix_third, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = prefix, .index = 2 } } },
        .{ .id = prefix_fourth, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = prefix, .index = 3 } } },
        .{ .id = suffix_first, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = suffix, .index = 0 } } },
        .{ .id = suffix_second, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = suffix, .index = 1 } } },
        .{ .id = suffix_third, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = suffix, .index = 2 } } },
        .{ .id = suffix_fourth, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = suffix, .index = 3 } } },
        .{ .id = prefix_read, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = prefix_read_id, .index = 0 } } },
        .{ .id = prefix_constant, .function = function_id, .type = .number, .origin = .{ .instruction_result = .{ .instruction = prefix_constant_id, .index = 0 } } },
        .{ .id = prefix_condition, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = prefix_compare_id, .index = 0 } } },
        .{ .id = forward_read, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = forward_read_id, .index = 0 } } },
        .{ .id = tampered_value, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = tampered_instruction_id, .index = 0 } } },
    };
    const places = [_]ir.Place{
        .{ .id = prefix_place, .function = function_id, .origin = .{ .local = 0 } },
        .{ .id = forward_read_place, .function = function_id, .origin = .{ .local = 1 } },
        .{ .id = forward_write_place, .function = function_id, .origin = .{ .local = 2 } },
        .{ .id = alternate_place, .function = function_id, .origin = .{ .local = 3 } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = prefix_read_id, .block = prefix, .operation = .{ .place_read = prefix_place }, .results = &.{prefix_read}, .effects = .place_read },
        .{ .id = prefix_constant_id, .block = prefix, .operation = .{ .constant = .{ .number = 186 } }, .results = &.{prefix_constant}, .effects = .pure },
        .{ .id = prefix_compare_id, .block = prefix, .operation = .{ .binary = .{
            .operator = .not_equal,
            .left = prefix_read,
            .right = prefix_constant,
            .mode = .semantic,
        } }, .results = &.{prefix_condition}, .effects = .semantic_table_read },
        .{ .id = forward_read_id, .block = forwarder, .operation = .{ .place_read = forward_read_place }, .results = &.{forward_read}, .effects = .place_read },
        .{ .id = forward_write_id, .block = forwarder, .operation = .{ .place_write = .{ .place = forward_write_place, .value = forward_read } }, .results = &.{}, .effects = .place_write },
        .{ .id = tampered_instruction_id, .block = alternate, .operation = .{ .place_read = alternate_place }, .results = &.{tampered_value}, .effects = .place_read },
    };
    const program = ir.Program{
        .program_id = "effectful-parameterized-prefix",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
    };
    const incoming = [_]ir.CfgEdgeRef{.{ .source = entry, .kind = .branch_then, .target = prefix }};

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    try std.testing.expect(try parameterizedContinuationBridge(
        std.testing.allocator,
        &program,
        &analysis,
        forwarder,
        0,
        suffix,
        exit,
        &.{prefix},
        &.{ forwarder, suffix },
        &incoming,
        null,
        null,
        null,
    ));

    const initial = try std.testing.allocator.dupe(ir.BlockId, &.{prefix});
    const extended = try extendContinuationClosureAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        exit,
        initial,
        &incoming,
    );
    defer std.testing.allocator.free(extended);
    try std.testing.expect(containsBlock(extended, prefix));
    try std.testing.expect(containsBlock(extended, forwarder));
    try std.testing.expect(!containsBlock(extended, suffix));
    try std.testing.expect(prepareClosure(std.testing.allocator, &program, &analysis, extended, &incoming));

    var tampered_blocks = blocks;
    tampered_blocks[forwarder.index()].terminator = .{ .jump = .{
        .target = suffix,
        .arguments = tampered_tuple[0..],
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, functions[0]);
    defer tampered_analysis.deinit();
    try std.testing.expect(!try parameterizedContinuationBridge(
        std.testing.allocator,
        &tampered_program,
        &tampered_analysis,
        forwarder,
        0,
        suffix,
        exit,
        &.{prefix},
        &.{ forwarder, suffix },
        &incoming,
        null,
        null,
        null,
    ));
    const tampered_closure = try std.testing.allocator.dupe(ir.BlockId, &.{ prefix, forwarder });
    defer std.testing.allocator.free(tampered_closure);
    try std.testing.expect(!prepareClosure(
        std.testing.allocator,
        &tampered_program,
        &tampered_analysis,
        tampered_closure,
        &incoming,
    ));
}

test "authenticated numeric continuation projection requires a complete transition tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const owner = ir.BlockId.fromIndex(1);
    const candidate = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const exit = ir.BlockId.fromIndex(4);

    const selector = ir.ValueId.fromIndex(0);
    const owner_control = ir.ValueId.fromIndex(1);
    const owner_limit = ir.ValueId.fromIndex(2);
    const owner_step = ir.ValueId.fromIndex(3);
    const owner_initial = ir.ValueId.fromIndex(4);
    const candidate_control = ir.ValueId.fromIndex(5);
    const candidate_limit = ir.ValueId.fromIndex(6);
    const candidate_step = ir.ValueId.fromIndex(7);
    const candidate_initial = ir.ValueId.fromIndex(8);
    const target_control = ir.ValueId.fromIndex(9);
    const target_limit = ir.ValueId.fromIndex(10);
    const target_step = ir.ValueId.fromIndex(11);
    const target_initial = ir.ValueId.fromIndex(12);
    const false_value = ir.ValueId.fromIndex(13);
    const candidate_has = ir.ValueId.fromIndex(14);
    const candidate_result_limit = ir.ValueId.fromIndex(15);
    const candidate_result_step = ir.ValueId.fromIndex(16);
    const candidate_next = ir.ValueId.fromIndex(17);
    const target_has = ir.ValueId.fromIndex(18);
    const target_result_limit = ir.ValueId.fromIndex(19);
    const target_result_step = ir.ValueId.fromIndex(20);
    const target_next = ir.ValueId.fromIndex(21);

    const false_instruction = ir.InstructionId.fromIndex(0);
    const candidate_instruction = ir.InstructionId.fromIndex(1);
    const target_instruction = ir.InstructionId.fromIndex(2);

    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = owner_control, .function = function_id, .type = .number, .origin = .{ .parameter = 1 } },
        .{ .id = owner_limit, .function = function_id, .type = .number, .origin = .{ .parameter = 2 } },
        .{ .id = owner_step, .function = function_id, .type = .number, .origin = .{ .parameter = 3 } },
        .{ .id = owner_initial, .function = function_id, .type = .boolean, .origin = .{ .parameter = 4 } },
        .{ .id = candidate_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = candidate, .index = 0 } } },
        .{ .id = candidate_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = candidate, .index = 1 } } },
        .{ .id = candidate_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = candidate, .index = 2 } } },
        .{ .id = candidate_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = candidate, .index = 3 } } },
        .{ .id = target_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = target_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = target, .index = 1 } } },
        .{ .id = target_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = target, .index = 2 } } },
        .{ .id = target_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = target, .index = 3 } } },
        .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } },
        .{ .id = candidate_has, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = candidate_instruction, .index = 0 } } },
        .{ .id = candidate_result_limit, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = candidate_instruction, .index = 1 } } },
        .{ .id = candidate_result_step, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = candidate_instruction, .index = 2 } } },
        .{ .id = candidate_next, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = candidate_instruction, .index = 3 } } },
        .{ .id = target_has, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = target_instruction, .index = 0 } } },
        .{ .id = target_result_limit, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = target_instruction, .index = 1 } } },
        .{ .id = target_result_step, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = target_instruction, .index = 2 } } },
        .{ .id = target_next, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = target_instruction, .index = 3 } } },
    };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{false_instruction}, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = owner },
            .else_edge = .{ .target = candidate, .arguments = &.{ owner_control, owner_limit, owner_step, owner_initial } },
        } } },
        .{ .id = owner, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &.{ owner_control, owner_limit, owner_step, owner_initial },
        } } },
        .{ .id = candidate, .function = function_id, .parameters = &.{ candidate_control, candidate_limit, candidate_step, candidate_initial }, .instructions = &.{candidate_instruction}, .terminator = .{ .branch = .{
            .condition = candidate_has,
            .then_edge = .{ .target = target, .arguments = &.{ candidate_next, candidate_result_limit, candidate_result_step, false_value } },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{ target_control, target_limit, target_step, target_initial }, .instructions = &.{target_instruction}, .terminator = .{ .branch = .{
            .condition = target_has,
            .then_edge = .{ .target = target, .arguments = &.{ target_next, target_result_limit, target_result_step, false_value } },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, owner_control, owner_limit, owner_step, owner_initial },
        .blocks = &.{ entry, owner, candidate, target, exit },
        .entry_block = entry,
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = false_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = candidate_instruction, .block = candidate, .operation = .{ .numeric_for_next = .{
            .control = candidate_control,
            .limit = candidate_limit,
            .step = candidate_step,
            .initial = candidate_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ candidate_has, candidate_result_limit, candidate_result_step, candidate_next }, .effects = .numeric_for_next },
        .{ .id = target_instruction, .block = target, .operation = .{ .numeric_for_next = .{
            .control = target_control,
            .limit = target_limit,
            .step = target_step,
            .initial = target_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ target_has, target_result_limit, target_result_step, target_next }, .effects = .numeric_for_next },
    };
    var program: ir.Program = .{
        .program_id = "authenticated-numeric-continuation-projection",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(std.testing.allocator, &program, &replay_index);
    defer replay_cache.deinit();
    const expected = [_]ir.ValueId{ owner_control, owner_limit, owner_step, owner_initial };
    const incoming = ir.CfgEdgeRef{ .source = candidate, .kind = .branch_then, .target = target };

    try std.testing.expect(try hasAuthenticatedIterationContextualProjectionAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        target,
        incoming,
        &expected,
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));

    var projection_context = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer projection_context.deinit();
    try std.testing.expect(!try projection_context.hasAuthenticatedContinuationBridgeForEdge(
        &analysis,
        incoming,
    ));
    try std.testing.expect(try projection_context.hasAuthenticatedIterationContextualProjectionForEdge(
        &analysis,
        incoming,
        &expected,
    ));

    const self_reentry = ir.CfgEdgeRef{
        .source = target,
        .kind = .branch_then,
        .target = target,
    };
    const self_tuple = [_]ir.ValueId{ target_next, target_result_limit, target_result_step, false_value };
    try std.testing.expect(try authenticatedIterationTupleForwardingForIncomingAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        target,
        target,
        &self_tuple,
        &.{self_reentry},
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));

    var cross_transition_tuple = self_tuple;
    cross_transition_tuple[0] = candidate_next;
    try std.testing.expect(!try authenticatedIterationTupleForwardingForIncomingAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        target,
        target,
        &cross_transition_tuple,
        &.{self_reentry},
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));

    var tampered_blocks = blocks;
    tampered_blocks[candidate.index()].terminator = .{ .branch = .{
        .condition = candidate_has,
        .then_edge = .{ .target = target, .arguments = &.{ candidate_next, candidate_result_limit, candidate_result_step, selector } },
        .else_edge = .{ .target = exit },
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, functions[0]);
    defer tampered_analysis.deinit();
    var tampered_lineage_index = try CloneLineageIndex.init(std.testing.allocator, &tampered_program);
    defer tampered_lineage_index.deinit();
    var tampered_replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &tampered_program);
    defer tampered_replay_index.deinit();
    var tampered_replay_cache = ReplayCache.init(std.testing.allocator, &tampered_program, &tampered_replay_index);
    defer tampered_replay_cache.deinit();
    try std.testing.expect(!try hasAuthenticatedIterationContextualProjectionAlloc(
        std.testing.allocator,
        &tampered_program,
        &tampered_analysis,
        target,
        incoming,
        &expected,
        &tampered_lineage_index,
        &tampered_replay_index,
        &tampered_replay_cache,
    ));
}

test "compound iteration projection accepts concrete owners for dynamic formals" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const forward = ir.BlockId.fromIndex(2);
    const header = ir.BlockId.fromIndex(3);
    const source = ir.BlockId.fromIndex(4);
    const exit = ir.BlockId.fromIndex(5);

    const owner_control = ir.ValueId.fromIndex(0);
    const owner_limit = ir.ValueId.fromIndex(1);
    const owner_step = ir.ValueId.fromIndex(2);
    const false_value = ir.ValueId.fromIndex(3);
    const target_control = ir.ValueId.fromIndex(4);
    const target_limit = ir.ValueId.fromIndex(5);
    const target_step = ir.ValueId.fromIndex(6);
    const target_initial = ir.ValueId.fromIndex(7);
    const header_control = ir.ValueId.fromIndex(8);
    const header_limit = ir.ValueId.fromIndex(9);
    const header_step = ir.ValueId.fromIndex(10);
    const header_initial = ir.ValueId.fromIndex(11);
    const has_value = ir.ValueId.fromIndex(12);
    const normalized_limit = ir.ValueId.fromIndex(13);
    const normalized_step = ir.ValueId.fromIndex(14);
    const next_control = ir.ValueId.fromIndex(15);

    const false_instruction = ir.InstructionId.fromIndex(0);
    const transition_instruction = ir.InstructionId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = owner_control, .function = function_id, .type = .number, .origin = .{ .parameter = 0 } },
        .{ .id = owner_limit, .function = function_id, .type = .number, .origin = .{ .parameter = 1 } },
        .{ .id = owner_step, .function = function_id, .type = .number, .origin = .{ .parameter = 2 } },
        .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } },
        .{ .id = target_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = target_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 1 } } },
        .{ .id = target_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 2 } } },
        .{ .id = target_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = target, .index = 3 } } },
        .{ .id = header_control, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = header_limit, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
        .{ .id = header_step, .function = function_id, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
        .{ .id = header_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
        .{ .id = has_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = false_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = transition_instruction, .block = header, .operation = .{ .numeric_for_next = .{
            .control = header_control,
            .limit = header_limit,
            .step = header_step,
            .initial = header_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ has_value, normalized_limit, normalized_step, next_control }, .effects = .numeric_for_next },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{false_instruction}, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &.{ owner_control, owner_limit, owner_step, false_value },
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{ target_control, target_limit, target_step, target_initial }, .terminator = .{ .jump = .{ .target = forward } } },
        .{ .id = forward, .function = function_id, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &.{ target_control, target_limit, target_step, target_initial },
        } } },
        .{ .id = header, .function = function_id, .parameters = &.{ header_control, header_limit, header_step, header_initial }, .instructions = &.{transition_instruction}, .terminator = .{ .branch = .{
            .condition = has_value,
            .then_edge = .{ .target = source },
            .else_edge = .{ .target = exit },
        } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &.{ next_control, normalized_limit, normalized_step, false_value },
        } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ owner_control, owner_limit, owner_step },
        .blocks = &.{ entry, target, forward, header, source, exit },
        .entry_block = entry,
    };
    var program = ir.Program{
        .program_id = "compound-dynamic-formal-projection",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const expected = [_]ir.ValueId{ owner_control, owner_limit, owner_step, false_value };
    const incoming = ir.CfgEdgeRef{ .source = source, .kind = .jump, .target = target };

    try std.testing.expect(try hasAuthenticatedCompoundIterationContextualProjectionAlloc(
        &program,
        &analysis,
        target,
        incoming,
        &expected,
    ));

    var replay_context = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay_context.deinit();
    try std.testing.expect(try replay_context.hasAuthenticatedParameterizedContinuationProjectionForEdge(
        &analysis,
        incoming,
        &expected,
    ));

    var tampered_blocks = blocks;
    tampered_blocks[forward.index()].terminator = .{ .jump = .{
        .target = header,
        .arguments = &.{ header_control, header_limit, header_step, header_initial },
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, function);
    defer tampered_analysis.deinit();
    try std.testing.expect(!try hasAuthenticatedCompoundIterationContextualProjectionAlloc(
        &tampered_program,
        &tampered_analysis,
        target,
        incoming,
        &expected,
    ));

    var tampered_replay_context = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &tampered_program,
        function_id,
    );
    defer tampered_replay_context.deinit();
    try std.testing.expect(!try tampered_replay_context.hasAuthenticatedParameterizedContinuationProjectionForEdge(
        &tampered_analysis,
        incoming,
        &expected,
    ));
}

test "authenticated positional continuation projection uses live canonical parameters" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const seed_dynamic = ir.ValueId.fromIndex(0);
    const seed_integer = ir.ValueId.fromIndex(1);
    const target_dynamic = ir.ValueId.fromIndex(2);
    const target_integer = ir.ValueId.fromIndex(3);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{
            .target = target,
            .arguments = &.{ seed_dynamic, seed_integer },
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{ target_dynamic, target_integer }, .terminator = .{ .jump = .{ .target = exit } } },
        .{ .id = exit, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ seed_dynamic, seed_integer },
        .blocks = &.{ entry, source, target, exit },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = seed_dynamic, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = seed_integer, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = target_dynamic, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
        .{ .id = target_integer, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 1 } } },
    };
    const incoming = [_]ir.CfgEdgeRef{.{ .source = source, .kind = .jump, .target = target }};
    var program: ir.Program = .{
        .program_id = "authenticated-positional-continuation-projection",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(std.testing.allocator, &program, &replay_index);
    defer replay_cache.deinit();

    try std.testing.expect(try authenticatedParameterProjectionForEdge(
        std.testing.allocator,
        &program,
        &analysis,
        source,
        .jump,
        target,
        &.{ seed_dynamic, seed_integer },
        &.{target},
        &.{target},
        &incoming,
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));

    var reordered_blocks = blocks;
    reordered_blocks[target.index()].parameters = &.{ target_integer, target_dynamic };
    program.blocks = &reordered_blocks;
    try std.testing.expect(!try authenticatedParameterProjectionForEdge(
        std.testing.allocator,
        &program,
        &analysis,
        source,
        .jump,
        target,
        &.{ seed_dynamic, seed_integer },
        &.{target},
        &.{target},
        &incoming,
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));

    program.blocks = &blocks;
    var mismatched_values = values;
    mismatched_values[target_integer.index()].type = .boolean;
    program.values = &mismatched_values;
    try std.testing.expect(!try authenticatedParameterProjectionForEdge(
        std.testing.allocator,
        &program,
        &analysis,
        source,
        .jump,
        target,
        &.{ seed_dynamic, seed_integer },
        &.{target},
        &.{target},
        &incoming,
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));

    program.values = &values;
    var stale_blocks = blocks;
    stale_blocks[source.index()].terminator = .{ .jump = .{ .target = exit, .arguments = &.{ seed_dynamic, seed_integer } } };
    program.blocks = &stale_blocks;
    try std.testing.expect(!try authenticatedParameterProjectionForEdge(
        std.testing.allocator,
        &program,
        &analysis,
        source,
        .jump,
        target,
        &.{ seed_dynamic, seed_integer },
        &.{target},
        &.{target},
        &incoming,
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));
}

test "positional continuation projection rejects unauthenticated edge values" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const source = ir.BlockId.fromIndex(2);
    const target = ir.BlockId.fromIndex(3);
    const selector = ir.ValueId.fromIndex(0);
    const producer_value = ir.ValueId.fromIndex(1);
    const target_value = ir.ValueId.fromIndex(2);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = producer },
            .else_edge = .{ .target = source },
        } } },
        .{ .id = producer, .function = function_id, .instructions = &.{instruction_id}, .terminator = .{ .return_values = &.{} } },
        .{ .id = source, .function = function_id, .terminator = .{ .jump = .{ .target = target, .arguments = &.{producer_value} } } },
        .{ .id = target, .function = function_id, .parameters = &.{target_value}, .terminator = .{ .return_values = &.{target_value} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ entry, producer, source, target },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = producer_value, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
        .{ .id = target_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = producer,
        .operation = .{ .constant = .{ .number = 1 } },
        .results = &.{producer_value},
        .effects = .pure,
    }};
    const incoming = [_]ir.CfgEdgeRef{.{ .source = source, .kind = .jump, .target = target }};
    var program: ir.Program = .{
        .program_id = "reject-unauthenticated-positional-continuation-projection",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(std.testing.allocator, &program, &replay_index);
    defer replay_cache.deinit();

    try std.testing.expect(!try authenticatedParameterProjectionForEdge(
        std.testing.allocator,
        &program,
        &analysis,
        source,
        .jump,
        target,
        &.{producer_value},
        &.{target},
        &.{target},
        &incoming,
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));
}

test "parameterized continuation rejects unavailable arguments despite stop reachability" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const incoming_source = ir.BlockId.fromIndex(1);
    const producer = ir.BlockId.fromIndex(2);
    const closure = ir.BlockId.fromIndex(3);
    const target = ir.BlockId.fromIndex(4);
    const stop = ir.BlockId.fromIndex(5);
    const selector = ir.ValueId.fromIndex(0);
    const producer_value = ir.ValueId.fromIndex(1);
    const target_value = ir.ValueId.fromIndex(2);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = incoming_source },
            .else_edge = .{ .target = producer },
        } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{ .target = closure } } },
        .{ .id = producer, .function = function_id, .parameters = &.{producer_value}, .terminator = .{ .jump = .{ .target = stop } } },
        .{ .id = closure, .function = function_id, .terminator = .{ .jump = .{ .target = target, .arguments = &.{producer_value} } } },
        .{ .id = target, .function = function_id, .parameters = &.{target_value}, .terminator = .{ .jump = .{ .target = stop } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ entry, incoming_source, producer, closure, target, stop },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = producer_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = producer, .index = 0 } } },
        .{ .id = target_value, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
    };
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = incoming_source,
        .kind = .jump,
        .target = closure,
    }};
    const program: ir.Program = .{
        .program_id = "parameterized-continuation-stop-reachability",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();

    try std.testing.expect(try analysis.canReach(target, stop));
    try std.testing.expect(!try parameterizedContinuationBridge(
        std.testing.allocator,
        &program,
        &analysis,
        closure,
        0,
        target,
        stop,
        &.{closure},
        &.{},
        &incoming,
        null,
        null,
        null,
    ));
}

test "authenticated pack continuation projection avoids repeated extension" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const closure = ir.BlockId.fromIndex(3);
    const consumer = ir.BlockId.fromIndex(4);
    const stop = ir.BlockId.fromIndex(5);
    const selector = ir.ValueId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(1);
    const source_call = ir.InstructionId.fromIndex(0);
    const clone_call = ir.InstructionId.fromIndex(1);
    const consumer_call = ir.InstructionId.fromIndex(2);
    const source_pack = ir.ValuePackId.fromIndex(0);
    const clone_pack = ir.ValuePackId.fromIndex(1);

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = producer },
            .else_edge = .{ .target = clone },
        } } },
        .{ .id = producer, .function = function_id, .instructions = &.{source_call}, .terminator = .{ .jump = .{ .target = closure } } },
        .{ .id = clone, .function = function_id, .instructions = &.{clone_call}, .terminator = .{ .jump = .{ .target = closure } } },
        .{ .id = closure, .function = function_id, .terminator = .{ .jump = .{ .target = consumer } } },
        .{ .id = consumer, .function = function_id, .instructions = &.{consumer_call}, .terminator = .{ .jump = .{ .target = stop } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, callee },
        .blocks = &.{ entry, producer, clone, closure, consumer, stop },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = callee, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = source_call,
            .block = producer,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .variadic = {} } } },
            .results = &.{},
            .pack_result = source_pack,
            .effects = ir.EffectSummary.dynamic_call,
        },
        .{
            .id = clone_call,
            .block = clone,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .variadic = {} } } },
            .results = &.{},
            .pack_result = clone_pack,
            .effects = ir.EffectSummary.dynamic_call,
        },
        .{
            .id = consumer_call,
            .block = consumer,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .argument_pack = source_pack, .result_arity = .{ .fixed = 0 } } },
            .results = &.{},
            .effects = ir.EffectSummary.dynamic_call,
        },
    };
    var packs = [_]ir.ValuePack{
        .{ .id = source_pack, .function = function_id, .origin = .{ .instruction_result = source_call } },
        .{ .id = clone_pack, .function = function_id, .origin = .{ .instruction_result = clone_call } },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = entry,
        .kind = .branch_else,
        .from = .{ .target = producer },
        .to = .{ .target = clone },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    var program: ir.Program = .{
        .program_id = "authenticated-pack-continuation-projection",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
        .edge_rewrites = &rewrites,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{ .source = clone, .kind = .jump, .target = closure }};

    var lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(std.testing.allocator, &program, &replay_index);
    defer replay_cache.deinit();

    const normalized = try normalizeIncomingThroughForwardingAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        &incoming,
    );
    defer std.testing.allocator.free(normalized);
    try std.testing.expectEqual(clone, normalized[0].source);
    try std.testing.expectEqual(@as(u8, 2), try cloneContextRankCached(
        std.testing.allocator,
        &program,
        &analysis,
        clone,
        &incoming,
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));

    try std.testing.expectEqual(
        ContinuationValueContext.contextual,
        try packCarriesContinuationContext(
            std.testing.allocator,
            &program,
            &analysis,
            source_pack,
            consumer,
            &.{closure},
            &.{consumer},
            &incoming,
            &lineage_index,
            &replay_index,
            &replay_cache,
        ),
    );

    const invalid_prefix = [_]ir.ValueType{.integer};
    packs[clone_pack.index()].shape = .{ .prefix = &invalid_prefix, .tail = .closed };
    var invalid_lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer invalid_lineage_index.deinit();
    var invalid_replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer invalid_replay_index.deinit();
    var invalid_replay_cache = ReplayCache.init(std.testing.allocator, &program, &invalid_replay_index);
    defer invalid_replay_cache.deinit();
    try std.testing.expectEqual(
        ContinuationValueContext.unavailable,
        try packCarriesContinuationContext(
            std.testing.allocator,
            &program,
            &analysis,
            source_pack,
            consumer,
            &.{closure},
            &.{consumer},
            &incoming,
            &invalid_lineage_index,
            &invalid_replay_index,
            &invalid_replay_cache,
        ),
    );

    const tampered_initial = try std.testing.allocator.dupe(ir.BlockId, &.{closure});
    const tampered = try extendContinuationClosureAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        stop,
        tampered_initial,
        &incoming,
    );
    defer std.testing.allocator.free(tampered);
    try std.testing.expectEqualSlices(ir.BlockId, &.{ closure, consumer }, tampered);
}

test "authenticated pack continuation follows transparent forwarding provenance" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const forwarding = ir.BlockId.fromIndex(3);
    const closure = ir.BlockId.fromIndex(4);
    const consumer = ir.BlockId.fromIndex(5);
    const stop = ir.BlockId.fromIndex(6);
    const selector = ir.ValueId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(1);
    const source_call = ir.InstructionId.fromIndex(0);
    const clone_call = ir.InstructionId.fromIndex(1);
    const consumer_call = ir.InstructionId.fromIndex(2);
    const source_pack = ir.ValuePackId.fromIndex(0);
    const clone_pack = ir.ValuePackId.fromIndex(1);

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = producer },
            .else_edge = .{ .target = clone },
        } } },
        .{ .id = producer, .function = function_id, .instructions = &.{source_call}, .terminator = .{ .jump = .{ .target = closure } } },
        .{ .id = clone, .function = function_id, .instructions = &.{clone_call}, .terminator = .{ .jump = .{ .target = forwarding } } },
        .{ .id = forwarding, .function = function_id, .terminator = .{ .jump = .{ .target = closure } } },
        .{ .id = closure, .function = function_id, .terminator = .{ .jump = .{ .target = consumer } } },
        .{ .id = consumer, .function = function_id, .instructions = &.{consumer_call}, .terminator = .{ .jump = .{ .target = stop } } },
        .{ .id = stop, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, callee },
        .blocks = &.{ entry, producer, clone, forwarding, closure, consumer, stop },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = callee, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = source_call,
            .block = producer,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .variadic = {} } } },
            .results = &.{},
            .pack_result = source_pack,
            .effects = ir.EffectSummary.dynamic_call,
        },
        .{
            .id = clone_call,
            .block = clone,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .variadic = {} } } },
            .results = &.{},
            .pack_result = clone_pack,
            .effects = ir.EffectSummary.dynamic_call,
        },
        .{
            .id = consumer_call,
            .block = consumer,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .argument_pack = source_pack, .result_arity = .{ .fixed = 0 } } },
            .results = &.{},
            .effects = ir.EffectSummary.dynamic_call,
        },
    };
    const packs = [_]ir.ValuePack{
        .{ .id = source_pack, .function = function_id, .origin = .{ .instruction_result = source_call } },
        .{ .id = clone_pack, .function = function_id, .origin = .{ .instruction_result = clone_call } },
    };
    const rewrite = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = entry,
        .kind = .branch_else,
        .from = .{ .target = producer },
        .to = .{ .target = clone },
        .rule = .node_split,
        .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
    }};
    var program: ir.Program = .{
        .program_id = "authenticated-pack-forwarding-provenance",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
        .edge_rewrites = &rewrite,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{ .source = forwarding, .kind = .jump, .target = closure }};

    var lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(std.testing.allocator, &program, &replay_index);
    defer replay_cache.deinit();

    try std.testing.expectEqual(
        ContinuationValueContext.contextual,
        try packCarriesContinuationContext(
            std.testing.allocator,
            &program,
            &analysis,
            source_pack,
            consumer,
            &.{closure},
            &.{consumer},
            &incoming,
            &lineage_index,
            &replay_index,
            &replay_cache,
        ),
    );

    var tampered_rewrite = rewrite;
    tampered_rewrite[0].to.arguments = &.{selector};
    program.edge_rewrites = &tampered_rewrite;
    var tampered_lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer tampered_lineage_index.deinit();
    var tampered_replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer tampered_replay_index.deinit();
    var tampered_replay_cache = ReplayCache.init(std.testing.allocator, &program, &tampered_replay_index);
    defer tampered_replay_cache.deinit();
    try std.testing.expectEqual(
        ContinuationValueContext.unavailable,
        try packCarriesContinuationContext(
            std.testing.allocator,
            &program,
            &analysis,
            source_pack,
            consumer,
            &.{closure},
            &.{consumer},
            &incoming,
            &tampered_lineage_index,
            &tampered_replay_index,
            &tampered_replay_cache,
        ),
    );
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

test "same-root iteration clones compare fresh results across split groups" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const root = ir.BlockId.fromIndex(1);
    const first_clone = ir.BlockId.fromIndex(2);
    const second_clone = ir.BlockId.fromIndex(3);
    const continuation = ir.BlockId.fromIndex(4);

    const control = ir.ValueId.fromIndex(0);
    const limit = ir.ValueId.fromIndex(1);
    const step = ir.ValueId.fromIndex(2);
    const initial = ir.ValueId.fromIndex(3);
    const root_control = ir.ValueId.fromIndex(4);
    const root_limit = ir.ValueId.fromIndex(5);
    const root_step = ir.ValueId.fromIndex(6);
    const root_initial = ir.ValueId.fromIndex(7);
    const first_control = ir.ValueId.fromIndex(8);
    const first_limit = ir.ValueId.fromIndex(9);
    const first_step = ir.ValueId.fromIndex(10);
    const first_initial = ir.ValueId.fromIndex(11);
    const second_control = ir.ValueId.fromIndex(12);
    const second_limit = ir.ValueId.fromIndex(13);
    const second_step = ir.ValueId.fromIndex(14);
    const second_initial = ir.ValueId.fromIndex(15);
    const false_value = ir.ValueId.fromIndex(16);
    const root_has = ir.ValueId.fromIndex(17);
    const root_limit_result = ir.ValueId.fromIndex(18);
    const root_step_result = ir.ValueId.fromIndex(19);
    const root_next = ir.ValueId.fromIndex(20);
    const first_has = ir.ValueId.fromIndex(21);
    const first_limit_result = ir.ValueId.fromIndex(22);
    const first_step_result = ir.ValueId.fromIndex(23);
    const first_next = ir.ValueId.fromIndex(24);
    const second_has = ir.ValueId.fromIndex(25);
    const second_limit_result = ir.ValueId.fromIndex(26);
    const second_step_result = ir.ValueId.fromIndex(27);
    const second_next = ir.ValueId.fromIndex(28);
    const continuation_has = ir.ValueId.fromIndex(29);
    const continuation_limit = ir.ValueId.fromIndex(30);
    const continuation_step = ir.ValueId.fromIndex(31);
    const continuation_next = ir.ValueId.fromIndex(32);

    const root_parameters = [_]ir.ValueId{ root_control, root_limit, root_step, root_initial };
    const first_parameters = [_]ir.ValueId{ first_control, first_limit, first_step, first_initial };
    const second_parameters = [_]ir.ValueId{ second_control, second_limit, second_step, second_initial };
    const root_results = [_]ir.ValueId{ root_has, root_limit_result, root_step_result, root_next };
    const first_results = [_]ir.ValueId{ first_has, first_limit_result, first_step_result, first_next };
    const second_results = [_]ir.ValueId{ second_has, second_limit_result, second_step_result, second_next };
    const entry_then_arguments = [_]ir.ValueId{ control, limit, step, initial };
    const root_entry_arguments = [_]ir.ValueId{ control, limit, step, initial };
    const root_state_arguments = [_]ir.ValueId{ root_next, root_limit_result, root_step_result, false_value };

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = control,
            .then_edge = .{ .target = first_clone, .arguments = entry_then_arguments[0..] },
            .else_edge = .{ .target = second_clone, .arguments = entry_then_arguments[0..] },
        } } },
        .{ .id = root, .function = function_id, .parameters = root_parameters[0..], .instructions = &.{ir.InstructionId.fromIndex(0)}, .terminator = .{ .jump = .{
            .target = continuation,
            .arguments = root_state_arguments[0..],
        } } },
        .{ .id = first_clone, .function = function_id, .parameters = first_parameters[0..], .instructions = &.{ir.InstructionId.fromIndex(1)}, .terminator = .{ .jump = .{
            .target = continuation,
            .arguments = &.{ first_next, first_limit_result, first_step_result, false_value },
        } } },
        .{ .id = second_clone, .function = function_id, .parameters = second_parameters[0..], .instructions = &.{ir.InstructionId.fromIndex(2)}, .terminator = .{ .jump = .{
            .target = continuation,
            .arguments = &.{ second_next, second_limit_result, second_step_result, false_value },
        } } },
        .{ .id = continuation, .function = function_id, .parameters = &.{ continuation_has, continuation_limit, continuation_step, continuation_next }, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ control, limit, step, initial },
        .blocks = &.{ entry, root, first_clone, second_clone, continuation },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = control, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = limit, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = step, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } },
        .{ .id = initial, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 3 } },
        .{ .id = root_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = root, .index = 0 } } },
        .{ .id = root_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = root, .index = 1 } } },
        .{ .id = root_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = root, .index = 2 } } },
        .{ .id = root_initial, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = root, .index = 3 } } },
        .{ .id = first_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = first_clone, .index = 0 } } },
        .{ .id = first_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = first_clone, .index = 1 } } },
        .{ .id = first_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = first_clone, .index = 2 } } },
        .{ .id = first_initial, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = first_clone, .index = 3 } } },
        .{ .id = second_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = second_clone, .index = 0 } } },
        .{ .id = second_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = second_clone, .index = 1 } } },
        .{ .id = second_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = second_clone, .index = 2 } } },
        .{ .id = second_initial, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = second_clone, .index = 3 } } },
        .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(3), .index = 0 } } },
        .{ .id = root_has, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 0 } } },
        .{ .id = root_limit_result, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 1 } } },
        .{ .id = root_step_result, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 2 } } },
        .{ .id = root_next, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(0), .index = 3 } } },
        .{ .id = first_has, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 0 } } },
        .{ .id = first_limit_result, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 1 } } },
        .{ .id = first_step_result, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 2 } } },
        .{ .id = first_next, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(1), .index = 3 } } },
        .{ .id = second_has, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 0 } } },
        .{ .id = second_limit_result, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 1 } } },
        .{ .id = second_step_result, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 2 } } },
        .{ .id = second_next, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(2), .index = 3 } } },
        .{ .id = continuation_has, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = continuation, .index = 0 } } },
        .{ .id = continuation_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = continuation, .index = 1 } } },
        .{ .id = continuation_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = continuation, .index = 2 } } },
        .{ .id = continuation_next, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = continuation, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = ir.InstructionId.fromIndex(0), .block = root, .operation = .{ .numeric_for_next = .{ .control = root_control, .limit = root_limit, .step = root_step, .initial = root_initial, .mode = .semantic_normalized } }, .results = root_results[0..], .effects = .numeric_for_next },
        .{ .id = ir.InstructionId.fromIndex(1), .block = first_clone, .operation = .{ .numeric_for_next = .{ .control = first_control, .limit = first_limit, .step = first_step, .initial = first_initial, .mode = .semantic_normalized } }, .results = first_results[0..], .effects = .numeric_for_next },
        .{ .id = ir.InstructionId.fromIndex(2), .block = second_clone, .operation = .{ .numeric_for_next = .{ .control = second_control, .limit = second_limit, .step = second_step, .initial = second_initial, .mode = .semantic_normalized } }, .results = second_results[0..], .effects = .numeric_for_next },
        .{ .id = ir.InstructionId.fromIndex(3), .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{ .id = ir.EdgeRewriteId.fromIndex(0), .source = entry, .kind = .branch_then, .from = .{ .target = root, .arguments = root_entry_arguments[0..] }, .to = .{ .target = first_clone, .arguments = root_entry_arguments[0..] }, .rule = .node_split, .node_split_group = ir.NodeSplitGroupId.fromIndex(0) },
        .{ .id = ir.EdgeRewriteId.fromIndex(1), .source = entry, .kind = .branch_else, .from = .{ .target = root, .arguments = root_entry_arguments[0..] }, .to = .{ .target = second_clone, .arguments = root_entry_arguments[0..] }, .rule = .node_split, .node_split_group = ir.NodeSplitGroupId.fromIndex(1) },
    };
    const program: ir.Program = .{
        .program_id = "same-root-iteration-sibling-groups",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    var lineage_index = try CloneLineageIndex.init(std.testing.allocator, &program);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.init(std.testing.allocator, &program);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(std.testing.allocator, &program, &replay_index);
    defer replay_cache.deinit();

    var projection_context = try ReplayProjectionContext.init(std.testing.allocator, &program);
    defer projection_context.deinit();
    try std.testing.expect(try projection_context.parametersEquivalent(
        continuation,
        &.{ first_next, first_limit_result, first_step_result, false_value },
        &.{ second_next, second_limit_result, second_step_result, false_value },
    ));

    try std.testing.expect(try authenticatedSameRootCloneValueMatchAlloc(
        std.testing.allocator,
        &program,
        first_next,
        second_next,
        &lineage_index,
        &replay_index,
        &replay_cache,
    ));

    var tampered_rewrites = rewrites;
    tampered_rewrites[1].to.arguments = &.{ root_control, limit, step, initial };
    var tampered_program = program;
    tampered_program.edge_rewrites = &tampered_rewrites;
    var tampered_lineage = try CloneLineageIndex.init(std.testing.allocator, &tampered_program);
    defer tampered_lineage.deinit();
    var tampered_replay = try node_split.ReplayIndex.init(std.testing.allocator, &tampered_program);
    defer tampered_replay.deinit();
    var tampered_cache = ReplayCache.init(std.testing.allocator, &tampered_program, &tampered_replay);
    defer tampered_cache.deinit();
    try std.testing.expect(!try authenticatedSameRootCloneValueMatchAlloc(
        std.testing.allocator,
        &tampered_program,
        first_next,
        second_next,
        &tampered_lineage,
        &tampered_replay,
        &tampered_cache,
    ));
}

fn collectAcyclicCollisionClosureAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    block: ir.BlockId,
) std.mem.Allocator.Error![]ir.BlockId {
    _ = analysis;
    // Seed at the collided entry.  The authenticated continuation pass below
    // owns the decision about which arm blocks carry this incoming context;
    // eagerly cloning both terminal arms turns unrelated siblings into part of
    // the semantic split and can multiply a large acyclic dispatcher.
    return allocator.dupe(ir.BlockId, &.{block});
}

fn findConditionalLoopEntrySplitAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    function_index: usize,
) std.mem.Allocator.Error!?Split {
    for (analysis.function.blocks) |header| {
        var membership = natural_loop.collect(allocator, analysis, header) catch |err| switch (err) {
            error.UnsupportedShape => continue,
            error.OutOfMemory => return error.OutOfMemory,
        } orelse continue;
        defer membership.deinit();

        const entry_count = try countConditionalLoopEntries(analysis, header, membership.bits);
        if (entry_count == 0 or countExternalLoopEntries(analysis, header, membership.bits) < 2) continue;
        const selected = try selectConditionalLoopEntry(analysis, header, membership.bits) orelse continue;

        var owned_closure = try collectConditionalLoopClosureAlloc(allocator, analysis, membership.bits);
        errdefer allocator.free(owned_closure);
        var incoming = std.ArrayList(ir.CfgEdgeRef).empty;
        defer incoming.deinit(allocator);
        try incoming.append(allocator, selected);
        const has_external_use = try hasReachableExternalClosureUseAlloc(
            allocator,
            analysis.program,
            analysis,
            owned_closure,
        );
        var prepared = prepareClosure(allocator, analysis.program, analysis, owned_closure, incoming.items);
        if (!prepared or has_external_use) {
            owned_closure = try extendClosureForExternalUsesAlloc(
                allocator,
                analysis.program,
                analysis,
                header,
                owned_closure,
                incoming.items,
            );
            prepared = prepareClosure(allocator, analysis.program, analysis, owned_closure, incoming.items);
        }
        if (!prepared) {
            allocator.free(owned_closure);
            continue;
        }

        // Redirect every external edge that the same authenticated closure
        // can own in this pass.  A sibling path may stop reaching the header
        // after one edge is redirected, turning a previously non-conditional
        // predecessor into the next scalar entry.  Batch compatible entries
        // before mutating the graph so the progress measure is stable.
        const external_entries = try collectExternalLoopEntryEdgesAlloc(
            allocator,
            analysis,
            header,
            membership.bits,
        );
        defer allocator.free(external_entries);
        if (trace_conditional_batch) std.debug.print("conditional_batch header={} entries={} selected={} external={any} closure={}\n", .{
            header.index(),
            entry_count,
            selected,
            external_entries,
            owned_closure.len,
        });
        for (external_entries) |candidate| {
            if (candidate.source == selected.source and
                candidate.kind == selected.kind and
                candidate.target == selected.target)
            {
                continue;
            }
            try incoming.append(allocator, candidate);
            if (!prepareClosure(allocator, analysis.program, analysis, owned_closure, incoming.items)) {
                if (trace_conditional_batch) std.debug.print("conditional_batch rejected header={} candidate={} incoming={any}\n", .{
                    header.index(),
                    candidate,
                    incoming.items,
                });
                _ = incoming.pop();
            } else if (trace_conditional_batch) {
                std.debug.print("conditional_batch accepted header={} candidate={} incoming={any}\n", .{
                    header.index(),
                    candidate,
                    incoming.items,
                });
            }
        }
        const owned_incoming = try incoming.toOwnedSlice(allocator);
        errdefer allocator.free(owned_incoming);
        return .{
            .allocator = allocator,
            .function_index = function_index,
            .branch = selected.source,
            .entry = header,
            .join = header,
            .incoming = owned_incoming,
            .closure = owned_closure,
            .entry_measure = entry_count,
        };
    }
    return null;
}

fn collectConditionalLoopClosureAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    membership: []const bool,
) std.mem.Allocator.Error![]ir.BlockId {
    const owned = try allocator.dupe(bool, membership);
    defer allocator.free(owned);
    var closure: std.ArrayList(ir.BlockId) = .empty;
    defer closure.deinit(allocator);
    for (analysis.function.blocks, membership) |source, is_member| {
        if (!is_member) continue;
        try closure.append(allocator, source);
    }
    var changed = true;
    while (changed) {
        changed = false;
        for (analysis.function.blocks, 0..) |candidate, candidate_index| {
            if (owned[candidate_index] or !analysis.isReachable(candidate)) continue;
            if (analysis.program.blocks[candidate.index()].terminator != .jump) continue;
            const predecessor_count = analysis.predecessorCount(candidate);
            if (predecessor_count == 0) continue;
            var exclusively_owned = true;
            for (0..predecessor_count) |predecessor_index| {
                const predecessor = analysis.predecessorAt(candidate, predecessor_index) orelse {
                    exclusively_owned = false;
                    break;
                };
                const local_index = analysis.blockIndex(predecessor) orelse {
                    exclusively_owned = false;
                    break;
                };
                if (!owned[local_index]) {
                    exclusively_owned = false;
                    break;
                }
            }
            if (!exclusively_owned) continue;
            try closure.append(allocator, candidate);
            owned[candidate_index] = true;
            changed = true;
        }
    }
    return try closure.toOwnedSlice(allocator);
}

fn countConditionalLoopEntries(
    analysis: *const cfg.Analysis,
    header: ir.BlockId,
    membership: []const bool,
) std.mem.Allocator.Error!usize {
    var count: usize = 0;
    for (analysis.function.blocks, 0..) |source, source_index| {
        if (!analysis.isReachable(source) or membership[source_index]) continue;
        if (try conditionalLoopEntryRef(analysis, header, source, membership) != null) count += 1;
    }
    return count;
}

fn collectExternalLoopEntryEdgesAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    header: ir.BlockId,
    membership: []const bool,
) std.mem.Allocator.Error![]ir.CfgEdgeRef {
    var entries: std.ArrayList(ir.CfgEdgeRef) = .empty;
    errdefer entries.deinit(allocator);
    for (analysis.function.blocks, 0..) |source, source_index| {
        if (!analysis.isReachable(source) or membership[source_index]) continue;
        const block = analysis.program.blocks[source.index()];
        switch (block.terminator) {
            .jump => |edge| {
                if (edge.target == header) {
                    const reference: ir.CfgEdgeRef = .{ .source = source, .kind = .jump, .target = header };
                    if (!edgeHasNodeSplitHistory(analysis.program, reference)) {
                        try entries.append(allocator, reference);
                    }
                }
            },
            .branch => |branch| {
                // A branch with both arms targeting the same block has no
                // unique edge slot to authenticate for a node split.
                if (branch.then_edge.target == header and branch.else_edge.target != header) {
                    const reference: ir.CfgEdgeRef = .{ .source = source, .kind = .branch_then, .target = header };
                    if (!edgeHasNodeSplitHistory(analysis.program, reference)) {
                        try entries.append(allocator, reference);
                    }
                } else if (branch.else_edge.target == header and branch.then_edge.target != header) {
                    const reference: ir.CfgEdgeRef = .{ .source = source, .kind = .branch_else, .target = header };
                    if (!edgeHasNodeSplitHistory(analysis.program, reference)) {
                        try entries.append(allocator, reference);
                    }
                }
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }
    return try entries.toOwnedSlice(allocator);
}

fn countExternalLoopEntries(
    analysis: *const cfg.Analysis,
    header: ir.BlockId,
    membership: []const bool,
) usize {
    var count: usize = 0;
    for (0..analysis.predecessorCount(header)) |predecessor_index| {
        const predecessor = analysis.predecessorAt(header, predecessor_index) orelse continue;
        const local_index = analysis.blockIndex(predecessor) orelse continue;
        if (analysis.isReachable(predecessor) and !membership[local_index]) count += 1;
    }
    return count;
}

fn countInteriorLoopEntries(
    analysis: *const cfg.Analysis,
    header: ir.BlockId,
    membership: []const bool,
) usize {
    var count: usize = 0;
    for (analysis.function.blocks, 0..) |source, source_index| {
        if (!analysis.isReachable(source) or membership[source_index]) continue;
        const terminator = analysis.program.blocks[source.index()].terminator;
        switch (terminator) {
            .jump => |edge| {
                if (isInteriorLoopTarget(analysis, header, membership, edge.target)) count += 1;
            },
            .branch => |branch| {
                if (isInteriorLoopTarget(analysis, header, membership, branch.then_edge.target)) count += 1;
                if (isInteriorLoopTarget(analysis, header, membership, branch.else_edge.target)) count += 1;
            },
            else => {},
        }
    }
    return count;
}

fn isInteriorLoopTarget(
    analysis: *const cfg.Analysis,
    header: ir.BlockId,
    membership: []const bool,
    target: ir.BlockId,
) bool {
    if (target == header) return false;
    const target_index = analysis.blockIndex(target) orelse return false;
    return membership[target_index];
}

fn directEdgeRef(program: *const ir.Program, source: ir.BlockId, target: ir.BlockId) ?ir.CfgEdgeRef {
    if (source.index() >= program.blocks.len) return null;
    return switch (program.blocks[source.index()].terminator) {
        .jump => |edge| if (edge.target == target)
            .{ .source = source, .kind = .jump, .target = target }
        else
            null,
        .branch => |branch| if (branch.then_edge.target == target and branch.else_edge.target != target)
            .{ .source = source, .kind = .branch_then, .target = target }
        else if (branch.else_edge.target == target and branch.then_edge.target != target)
            .{ .source = source, .kind = .branch_else, .target = target }
        else
            null,
        else => null,
    };
}

fn edgeHasNodeSplitHistory(program: *const ir.Program, reference: ir.CfgEdgeRef) bool {
    var current = reference.target;
    var remaining = program.edge_rewrites.len;
    while (remaining != 0) : (remaining -= 1) {
        var found = false;
        var index = program.edge_rewrites.len;
        while (index != 0) {
            index -= 1;
            const rewrite = program.edge_rewrites[index];
            if (rewrite.source != reference.source or
                rewrite.kind != reference.kind or
                rewrite.to.target != current)
            {
                continue;
            }
            found = true;
            switch (rewrite.rule) {
                .node_split, .clone_fold => return true,
                .forwarding_jump => {
                    if (rewrite.from.target == current) return false;
                    current = rewrite.from.target;
                },
                .proved_branch => return false,
            }
            break;
        }
        if (!found) return false;
    }
    return false;
}

fn selectConditionalLoopEntry(
    analysis: *const cfg.Analysis,
    header: ir.BlockId,
    membership: []const bool,
) std.mem.Allocator.Error!?ir.CfgEdgeRef {
    var selected: ?ir.CfgEdgeRef = null;
    for (analysis.function.blocks, 0..) |source, source_index| {
        if (!analysis.isReachable(source) or membership[source_index]) continue;
        const candidate = try conditionalLoopEntryRef(analysis, header, source, membership) orelse continue;
        if (selected == null or edgeRefLessThan(candidate, selected.?)) selected = candidate;
    }
    return selected;
}

fn conditionalLoopEntryRef(
    analysis: *const cfg.Analysis,
    header: ir.BlockId,
    source: ir.BlockId,
    membership: []const bool,
) std.mem.Allocator.Error!?ir.CfgEdgeRef {
    const terminator = analysis.program.blocks[source.index()].terminator;
    switch (terminator) {
        .branch => |branch| {
            if (branch.then_edge.target == header and branch.else_edge.target != header and
                !try analysis.canReach(branch.else_edge.target, header) and
                !edgeHasNodeSplitHistory(analysis.program, .{
                    .source = source,
                    .kind = .branch_then,
                    .target = header,
                }))
            {
                return .{ .source = source, .kind = .branch_then, .target = header };
            }
            if (branch.else_edge.target == header and branch.then_edge.target != header and
                !try analysis.canReach(branch.then_edge.target, header) and
                !edgeHasNodeSplitHistory(analysis.program, .{
                    .source = source,
                    .kind = .branch_else,
                    .target = header,
                }))
            {
                return .{ .source = source, .kind = .branch_else, .target = header };
            }
            return null;
        },
        .jump => |edge| {
            if (edge.target != header or
                edgeHasNodeSplitHistory(analysis.program, .{ .source = source, .kind = .jump, .target = header }))
            {
                return null;
            }
        },
        else => return null,
    }

    var current = source;
    var remaining = analysis.function.blocks.len;
    while (remaining != 0) : (remaining -= 1) {
        if (analysis.predecessorCount(current) != 1) return null;
        const predecessor = analysis.predecessorAt(current, 0) orelse return null;
        const predecessor_index = analysis.blockIndex(predecessor) orelse return null;
        if (membership[predecessor_index]) return null;
        switch (analysis.program.blocks[predecessor.index()].terminator) {
            .jump => |edge| {
                if (edge.target != current) return null;
                current = predecessor;
            },
            .branch => |branch| {
                const sibling = if (branch.then_edge.target == current and branch.else_edge.target != current)
                    branch.else_edge.target
                else if (branch.else_edge.target == current and branch.then_edge.target != current)
                    branch.then_edge.target
                else
                    return null;
                if (try analysis.canReach(sibling, header)) return null;
                return .{ .source = source, .kind = .jump, .target = header };
            },
            else => return null,
        }
    }
    return null;
}

fn edgeRefLessThan(left: ir.CfgEdgeRef, right: ir.CfgEdgeRef) bool {
    if (left.source != right.source) return left.source.index() < right.source.index();
    return @intFromEnum(left.kind) < @intFromEnum(right.kind);
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

fn selectionLessThan(left: Selection, right: Selection) bool {
    const left_max = @max(left.then_distance, left.else_distance);
    const right_max = @max(right.then_distance, right.else_distance);
    if (left_max != right_max) return left_max < right_max;
    const left_sum = @as(u64, left.then_distance) + left.else_distance;
    const right_sum = @as(u64, right.then_distance) + right.else_distance;
    if (left_sum != right_sum) return left_sum < right_sum;
    return left.join.index() < right.join.index();
}

fn convergenceIsBypassed(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    block: ir.BlockId,
    branch: ir.Branch,
    candidate: ir.BlockId,
    allowed: ?[]const bool,
    distances: ?DistancePair,
) std.mem.Allocator.Error!bool {
    for (analysis.function.blocks) |downstream| {
        if (downstream == candidate or !isIterationTransitionHeader(analysis.program, downstream)) continue;
        if (try forwardDistance(allocator, analysis, candidate, downstream, null, allowed) == null) continue;
        const then_reaches = if (distances) |pair|
            distanceAt(analysis, pair.then_distances, downstream) != null
        else
            try forwardDistance(allocator, analysis, branch.then_edge.target, downstream, null, allowed) != null;
        if (!then_reaches) continue;
        const else_reaches = if (distances) |pair|
            distanceAt(analysis, pair.else_distances, downstream) != null
        else
            try forwardDistance(allocator, analysis, branch.else_edge.target, downstream, null, allowed) != null;
        if (!else_reaches or
            try analysis.immediateStructuralPostDominatorWithin(allocator, block, downstream, allowed) == null) continue;
        if (try forwardDistance(allocator, analysis, branch.then_edge.target, downstream, candidate, allowed) != null or
            try forwardDistance(allocator, analysis, branch.else_edge.target, downstream, candidate, allowed) != null)
        {
            return true;
        }
    }
    return false;
}

fn collectArmClosureAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    start: ir.BlockId,
    join: ir.BlockId,
) std.mem.Allocator.Error!?[]ir.BlockId {
    if (start == join) return try allocator.alloc(ir.BlockId, 0);
    if (!try analysis.canReach(start, join)) return null;
    const block_count = analysis.function.blocks.len;
    const found = try allocator.alloc(bool, block_count);
    defer allocator.free(found);
    @memset(found, false);
    const pending = try allocator.alloc(ir.BlockId, block_count);
    defer allocator.free(pending);
    const start_index = analysis.blockIndex(start) orelse return null;
    found[start_index] = true;
    pending[0] = start;
    var cursor: usize = 0;
    var pending_len: usize = 1;
    while (cursor < pending_len) : (cursor += 1) {
        const current = pending[cursor];
        for (0..analysis.successorCount(current)) |successor_index| {
            const successor = analysis.successorAt(current, successor_index) orelse return null;
            if (successor == join) continue;
            if (!try analysis.canReach(successor, join)) continue;
            const local_index = analysis.blockIndex(successor) orelse return null;
            if (found[local_index]) continue;
            found[local_index] = true;
            pending[pending_len] = successor;
            pending_len += 1;
        }
    }
    return try allocator.dupe(ir.BlockId, pending[0..pending_len]);
}

fn commonClosureAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    join: ir.BlockId,
    left: []const ir.BlockId,
    right: []const ir.BlockId,
) std.mem.Allocator.Error![]ir.BlockId {
    var common: std.ArrayList(ir.BlockId) = .empty;
    defer common.deinit(allocator);
    for (left) |left_id| {
        const left_index = analysis.blockIndex(left_id) orelse continue;
        for (right) |right_id| {
            if (analysis.blockIndex(right_id) == left_index) {
                try common.append(allocator, left_id);
                break;
            }
        }
    }
    const owned = try common.toOwnedSlice(allocator);
    return try extendContinuationClosureAlloc(allocator, program, analysis, join, owned, null);
}

fn isEffectfulZeroParameterBlock(
    program: *const ir.Program,
    block_id: ir.BlockId,
) bool {
    if (block_id.index() >= program.blocks.len) return false;
    const block = program.blocks[block_id.index()];
    if (block.id != block_id or block.parameters.len != 0) return false;
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return false;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or instruction.block != block_id) return false;
        if (proof_effect_closure.hasObservableEffects(instruction.effects)) return true;
    }
    return false;
}

// A continuation edge may carry context through the target's formal block
// parameters.  Treat that as a projection only when the live edge, canonical
// parameter identities, exact value types, and replay-authenticated argument
// provenance all agree.  This keeps a shared continuation reusable without
// inventing a value or relying on a same-typed substitute.
fn authenticatedParameterProjectionForEdge(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    target: ir.BlockId,
    arguments: []const ir.ValueId,
    closure: []const ir.BlockId,
    continuation: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    if (target.index() >= program.blocks.len) return false;
    const target_block = program.blocks[target.index()];
    if (target_block.id != target or target_block.parameters.len == 0) return false;
    if (!containsBlock(continuation, target) and !containsBlock(closure, target)) return false;
    const reference = edgeReferenceForKind(program, source, kind) orelse return false;
    if (reference.target != target) return false;
    const edge = cfg_edge.value(program, reference) orelse return false;
    if (!std.mem.eql(ir.ValueId, edge.arguments, arguments)) return false;
    // A formal target does not make an edge context-independent when one of
    // its arguments was produced by the closure being cloned.  A source that
    // is itself in the continuation is cloned with the authenticated edge,
    // so its tuple is remapped before the shared target receives its formal
    // value.  A source outside the continuation still needs the conservative
    // rejection below because no remapping boundary is present here.
    const source_remaps_closure_tuple = containsBlock(continuation, source) and
        isEffectfulZeroParameterBlock(program, source);
    for (edge.arguments) |argument| {
        if (projectionValueProducer(program, argument)) |producer| {
            if (containsBlock(closure, producer) and !source_remaps_closure_tuple) return false;
        }
    }
    if (!try parameterizedContinuationArgumentsAreAuthenticated(
        allocator,
        program,
        analysis,
        source,
        target,
        edge.arguments,
        incoming,
        closure,
        continuation,
        lineage_index,
        replay_index,
        replay_cache,
        .authenticated_parameter,
    )) return false;

    // If the target is itself a clone, its formal tuple must be backed by the
    // complete replay mapping for that clone step.  A live edge alone cannot
    // authenticate a forged or partial clone history.
    if (cloneStepForTargetCached(program, target, lineage_index)) |step| {
        const direct_bridge = hasIncomingCloneBridgeCached(
            program,
            reference,
            target,
            lineage_index,
        ) or try hasAuthenticatedComposedCloneBridgeAlloc(
            allocator,
            program,
            analysis,
            reference,
            lineage_index,
            replay_index,
            replay_cache,
        );
        const unchanged_bridge = if (direct_bridge)
            true
        else
            try hasAuthenticatedUnchangedCloneBridgeForEdgeAlloc(
                allocator,
                program,
                analysis,
                reference,
                lineage_index,
                replay_index,
                replay_cache,
            );
        if (!direct_bridge and !unchanged_bridge) return false;
        if (!try cloneLineageArgumentsMatchReplayCached(
            allocator,
            program,
            step.source,
            step.clone,
            lineage_index,
            replay_index,
            replay_cache,
        )) return false;
    }
    return true;
}

const ContinuationContextUseDetector = struct {
    const Witness = union(enum) {
        value: ir.ValueId,
        pack: ir.ValuePackId,
        place: ir.PlaceId,
    };

    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    current: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    closure: []const ir.BlockId,
    continuation: []const ir.BlockId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
    closure_only: bool = false,
    found: bool = false,
    witness: ?Witness = null,

    fn mark(self: *ContinuationContextUseDetector, witness: Witness) void {
        if (self.found) return;
        self.found = true;
        self.witness = witness;
    }

    fn authenticatedParameterProjection(
        self: *ContinuationContextUseDetector,
        source: ir.BlockId,
        kind: ir.CfgEdgeKind,
        target: ir.BlockId,
        arguments: []const ir.ValueId,
    ) std.mem.Allocator.Error!bool {
        return authenticatedParameterProjectionForEdge(
            self.allocator,
            self.program,
            self.analysis,
            source,
            kind,
            target,
            arguments,
            self.closure,
            self.continuation,
            self.incoming,
            self.lineage_index,
            self.replay_index,
            self.replay_cache,
        );
    }

    pub fn value(self: *ContinuationContextUseDetector, value_id: ir.ValueId) void {
        if (self.found) return;
        if (value_id.index() >= self.program.values.len) {
            self.found = true;
            return;
        }
        const candidate_value = self.program.values[value_id.index()];
        if (candidate_value.id != value_id or candidate_value.function != self.analysis.function.id) {
            self.mark(.{ .value = value_id });
            return;
        }
        const producer = blk: switch (candidate_value.origin) {
            .parameter, .capture => return,
            .block_parameter => |origin| origin.block,
            .instruction_result => |origin| {
                if (origin.instruction.index() >= self.program.instructions.len) {
                    self.mark(.{ .value = value_id });
                    return;
                }
                const instruction = self.program.instructions[origin.instruction.index()];
                if (instruction.id != origin.instruction) {
                    self.mark(.{ .value = value_id });
                    return;
                }
                break :blk instruction.block;
            },
        };
        if (producer == self.current) return;
        if (containsBlock(self.closure, producer)) {
            self.mark(.{ .value = value_id });
            return;
        }
        if (self.closure_only) return;
        if (containsBlock(self.continuation, producer)) {
            // A dominating definition inside the candidate continuation is
            // local to the shared suffix, not an incoming context value. It
            // remains available when the suffix is reused. A non-dominating
            // definition still requires the authenticated contextual path.
            if (self.analysis.dominates(producer, self.current)) return;
            self.mark(.{ .value = value_id });
            return;
        }
        if (!hasCloneLineageCandidateForSource(self.replay_index, self.program, producer)) {
            if (self.incoming.len == 0 or definitionDominatesIncoming(self.analysis, producer, self.incoming)) return;
            self.mark(.{ .value = value_id });
            return;
        }
        switch (valueCarriesContinuationContext(
            self.allocator,
            self.program,
            self.analysis,
            value_id,
            self.current,
            self.closure,
            self.continuation,
            self.incoming,
            self.lineage_index,
            self.replay_index,
            self.replay_cache,
        ) catch {
            self.mark(.{ .value = value_id });
            return;
        }) {
            .available => {},
            .contextual, .unavailable => self.mark(.{ .value = value_id }),
        }
    }

    pub fn pack(self: *ContinuationContextUseDetector, pack_id: ir.ValuePackId) void {
        if (self.found) return;
        const producer = packProducerBlock(self.program, pack_id) orelse {
            self.mark(.{ .pack = pack_id });
            return;
        };
        if (containsBlock(self.closure, producer)) {
            self.mark(.{ .pack = pack_id });
            return;
        }
        if (self.closure_only) return;
        if (containsBlock(self.continuation, producer)) {
            // Open packs follow the same ownership rule as scalar values:
            // only a non-dominating local producer is contextual.
            if (self.analysis.dominates(producer, self.current)) return;
            self.mark(.{ .pack = pack_id });
            return;
        }
        switch (packCarriesContinuationContext(
            self.allocator,
            self.program,
            self.analysis,
            pack_id,
            self.current,
            self.closure,
            self.continuation,
            self.incoming,
            self.lineage_index,
            self.replay_index,
            self.replay_cache,
        ) catch {
            self.mark(.{ .pack = pack_id });
            return;
        }) {
            .available => {},
            .contextual, .unavailable => self.mark(.{ .pack = pack_id }),
        }
    }

    pub fn place(self: *ContinuationContextUseDetector, place_id: ir.PlaceId) void {
        if (self.found) return;
        if (place_id.index() >= self.program.places.len) {
            self.mark(.{ .place = place_id });
            return;
        }
        const candidate_place = self.program.places[place_id.index()];
        if (candidate_place.id != place_id or candidate_place.function != self.analysis.function.id) {
            self.mark(.{ .place = place_id });
            return;
        }
        const producer = blk: switch (candidate_place.origin) {
            .local, .capture => return,
            .instruction => |instruction_id| {
                if (instruction_id.index() >= self.program.instructions.len) {
                    self.mark(.{ .place = place_id });
                    return;
                }
                const instruction = self.program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id) {
                    self.mark(.{ .place = place_id });
                    return;
                }
                break :blk instruction.block;
            },
        };
        if (producer == self.current) return;
        if (containsBlock(self.closure, producer)) {
            self.mark(.{ .place = place_id });
            return;
        }
        if (self.closure_only) return;
        if (containsBlock(self.continuation, producer)) {
            self.mark(.{ .place = place_id });
            return;
        }
        if (self.incoming.len == 0 or definitionDominatesIncoming(self.analysis, producer, self.incoming)) return;
        self.mark(.{ .place = place_id });
    }
};

fn visitContinuationEdgeUses(
    detector: *ContinuationContextUseDetector,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    edge: ir.Edge,
) void {
    const projected = detector.authenticatedParameterProjection(
        source,
        kind,
        edge.target,
        edge.arguments,
    ) catch false;
    if (projected) return;
    for (edge.arguments) |argument| detector.value(argument);
}

fn visitContinuationTerminatorUses(
    detector: *ContinuationContextUseDetector,
    source: ir.BlockId,
    terminator: ir.Terminator,
) void {
    switch (terminator) {
        .jump => |edge| visitContinuationEdgeUses(detector, source, .jump, edge),
        .branch => |branch| {
            detector.value(branch.condition);
            visitContinuationEdgeUses(detector, source, .branch_then, branch.then_edge);
            visitContinuationEdgeUses(detector, source, .branch_else, branch.else_edge);
        },
        .return_values => |values| for (values) |value_id| detector.value(value_id),
        .return_pack => |pack_id| detector.pack(pack_id),
        .return_expanded => |expanded| {
            for (expanded.values) |value_id| detector.value(value_id);
            detector.pack(expanded.pack);
        },
        .throw_error => |value| {
            detector.value(value.value);
            if (value.dynamic_level) |level| detector.value(level);
        },
        .unreachable_block => {},
    }
}

fn hasReachableConditionalPredecessor(
    analysis: *const cfg.Analysis,
    block: ir.BlockId,
) bool {
    for (0..analysis.predecessorCount(block)) |predecessor_index| {
        const predecessor = analysis.predecessorAt(block, predecessor_index) orelse return true;
        if (!analysis.isReachable(predecessor)) continue;
        if (predecessor.index() >= analysis.program.blocks.len) return true;
        const predecessor_block = analysis.program.blocks[predecessor.index()];
        if (predecessor_block.id != predecessor) return true;
        switch (predecessor_block.terminator) {
            .branch => return true,
            else => {},
        }
    }
    return false;
}

fn hasReachableExternalContinuationPredecessor(
    analysis: *const cfg.Analysis,
    block: ir.BlockId,
    closure: []const ir.BlockId,
    continuation: []const ir.BlockId,
) bool {
    for (0..analysis.predecessorCount(block)) |predecessor_index| {
        const predecessor = analysis.predecessorAt(block, predecessor_index) orelse return true;
        if (!analysis.isReachable(predecessor)) continue;
        if (!containsBlock(closure, predecessor) and !containsBlock(continuation, predecessor)) return true;
    }
    return false;
}

fn uniqueReachableContinuationPredecessor(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    block: ir.BlockId,
    closure: []const ir.BlockId,
    continuation: []const ir.BlockId,
) ?ir.CfgEdgeRef {
    var selected: ?ir.CfgEdgeRef = null;
    for (0..analysis.predecessorCount(block)) |predecessor_index| {
        const predecessor = analysis.predecessorAt(block, predecessor_index) orelse return null;
        if (!analysis.isReachable(predecessor)) continue;
        if (!containsBlock(closure, predecessor) and !containsBlock(continuation, predecessor)) return null;
        for (0..analysis.successorCount(predecessor)) |successor_index| {
            const successor = analysis.successorAt(predecessor, successor_index) orelse return null;
            if (successor != block) continue;
            const reference = successorEdgeRef(program, predecessor, successor_index) orelse return null;
            if (selected != null) return null;
            selected = reference;
        }
    }
    return selected;
}

fn blockUsesContinuationContext(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    block: ir.Block,
    current: ir.BlockId,
    closure: []const ir.BlockId,
    continuation: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
    stop: ir.BlockId,
) std.mem.Allocator.Error!bool {
    var detector = ContinuationContextUseDetector{
        .allocator = allocator,
        .program = program,
        .analysis = analysis,
        .current = current,
        .incoming = incoming,
        .closure = closure,
        .continuation = continuation,
        .lineage_index = lineage_index,
        .replay_index = replay_index,
        .replay_cache = replay_cache,
    };
    var has_observable_effect = false;
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return true;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or instruction.block != block.id) return true;
        has_observable_effect = has_observable_effect or
            proof_effect_closure.hasObservableEffects(instruction.effects);
        runtime_uses.visitOperationUses(instruction.operation, &detector);
        if (detector.found) {
            traceStructural("structural_extension_witness block={} current={} witness={any}\n", .{
                block.id.index(),
                current.index(),
                detector.witness,
            });
            return true;
        }
    }
    visitContinuationTerminatorUses(&detector, block.id, block.terminator);
    if (detector.found) {
        traceStructural("structural_extension_witness block={} current={} witness={any} terminator=true\n", .{
            block.id.index(),
            current.index(),
            detector.witness,
        });
    }
    // Observable work cannot be shared across an ownership split merely
    // because its operands are context-independent.  The alternate incoming
    // edge selects a distinct execution path, so a zero-parameter effectful
    // continuation block must be cloned with that path.  A shared block may
    // have only jump predecessors: in that shape there is no immediate
    // conditional predecessor to expose the ownership boundary, but a
    // reachable predecessor outside this path proves that the block is a
    // shared suffix.  Otherwise the split leaves the path entering an
    // already-owned effectful block and the next structural pass is forced
    // into one-block-at-a-time collision replay.
    if (!detector.found and block.parameters.len == 0 and has_observable_effect) {
        if (hasReachableConditionalPredecessor(analysis, current) or
            hasReachableExternalContinuationPredecessor(
                analysis,
                current,
                closure,
                continuation,
            )) return true;

        // A uniquely owned effectful suffix still has to be cloned when it
        // completes an authenticated iteration handoff.  Without this
        // criterion, repeated node splits copy only the preceding block and
        // rediscover the same suffix on every feedback iteration.
        if (closure.len != 0 and incoming.len != 0) {
            if (uniqueReachableContinuationPredecessor(
                program,
                analysis,
                current,
                closure,
                continuation,
            )) |boundary| {
                if (try authenticatedIterationHandoffBoundaryAtIncoming(
                    program,
                    analysis,
                    closure[0],
                    closure,
                    boundary,
                    incoming,
                    stop,
                )) {
                    traceStructural("structural_extension_authenticated_unique_handoff block={} predecessor={} stop={}\n", .{
                        current.index(),
                        boundary.source.index(),
                        stop.index(),
                    });
                    return true;
                }
            }
        }
    }
    return detector.found;
}

// A rejected parameterized bridge can still lead to a later block that uses a
// value produced by the clone closure.  The ordinary continuation walk stops
// at that bridge because it cannot yet authenticate the intermediate formal
// tuple.  Find only the delayed paths that directly consume closure-local
// values; prepareClosure remains responsible for authenticating every block
// and edge added by this fallback.
fn blockUsesDelayedClosureValue(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    block: ir.Block,
    closure: []const ir.BlockId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) bool {
    var detector = ContinuationContextUseDetector{
        .allocator = allocator,
        .program = program,
        .analysis = analysis,
        .current = block.id,
        .incoming = &.{},
        .closure = closure,
        .continuation = &.{},
        .lineage_index = lineage_index,
        .replay_index = replay_index,
        .replay_cache = replay_cache,
        .closure_only = true,
    };
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return true;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or instruction.block != block.id) return true;
        runtime_uses.visitOperationUses(instruction.operation, &detector);
        if (detector.found) return true;
    }
    runtime_uses.visitTerminatorUses(block.terminator, &detector);
    return detector.found;
}

fn hasReachableExternalClosureUseAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []const ir.BlockId,
) std.mem.Allocator.Error!bool {
    var lineage_index = try CloneLineageIndex.initForFunction(allocator, program, analysis.function.id);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.initForFunction(allocator, program, analysis.function.id);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(allocator, program, &replay_index);
    defer replay_cache.deinit();

    for (analysis.function.blocks) |block_id| {
        if (!analysis.isReachable(block_id) or containsBlock(closure, block_id)) continue;
        if (block_id.index() >= program.blocks.len) return true;
        if (blockUsesDelayedClosureValue(
            allocator,
            program,
            analysis,
            program.blocks[block_id.index()],
            closure,
            &lineage_index,
            &replay_index,
            &replay_cache,
        )) return true;
    }
    return false;
}

fn successorEdgeRef(
    program: *const ir.Program,
    source: ir.BlockId,
    successor_index: usize,
) ?ir.CfgEdgeRef {
    if (source.index() >= program.blocks.len) return null;
    const block = program.blocks[source.index()];
    if (block.id != source) return null;
    return switch (block.terminator) {
        .jump => |edge| if (successor_index == 0)
            .{ .source = source, .kind = .jump, .target = edge.target }
        else
            null,
        .branch => |branch| switch (successor_index) {
            0 => .{ .source = source, .kind = .branch_then, .target = branch.then_edge.target },
            1 => .{ .source = source, .kind = .branch_else, .target = branch.else_edge.target },
            else => null,
        },
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => null,
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

const ContinuationExtensionMode = enum {
    contextual,
    closure_only,
};

fn hasCloneLineageCandidateForSource(
    replay_index: *const node_split.ReplayIndex,
    program: *const ir.Program,
    source: ir.BlockId,
) bool {
    if (source.index() >= program.blocks.len or program.blocks[source.index()].id != source) return false;
    const source_function = program.blocks[source.index()].function;
    for (replay_index.candidateCloneTargetsForSource(program, source)) |candidate| {
        if (candidate.index() >= program.blocks.len or program.blocks[candidate.index()].id != candidate) continue;
        if (candidate != source and program.blocks[candidate.index()].function == source_function) return true;
    }
    return false;
}

fn hasAuthenticatedDirectValueCloneForIncoming(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    producer: ir.BlockId,
    source_value: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: ?*const CloneLineageIndex,
) std.mem.Allocator.Error!bool {
    if (incoming.len == 0) return false;
    for (incoming) |reference| {
        const edge = cfg_edge.value(program, reference) orelse return false;
        var carried = false;
        for (program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.from.target != producer) continue;
            const candidate = rewrite.to.target;
            if (candidate == producer or candidate.index() >= program.blocks.len or
                analysis.blockIndex(candidate) == null)
            {
                continue;
            }
            // Context reachability authenticates which clone is live for this
            // incoming edge, while the edge argument authenticates the value
            // identity.  Lineage alone is insufficient because a descendant
            // clone may carry a different mapped value.
            const one = [_]ir.CfgEdgeRef{reference};
            if (!try cloneContextMatchesIncomingCached(program, analysis, candidate, &one, lineage_index)) continue;
            const mapped = mapValueByCloneShape(program, producer, candidate, source_value) orelse continue;
            for (edge.arguments) |argument| {
                if (argument == mapped) {
                    carried = true;
                    break;
                }
            }
            if (carried) break;
        }
        if (!carried) return false;
    }
    return true;
}

fn hasAuthenticatedComposedValueCloneForIncoming(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    producer: ir.BlockId,
    source_value: ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!bool {
    if (incoming.len == 0 or lineage_index == null or replay_index == null) return false;
    for (incoming) |reference| {
        const one = [_]ir.CfgEdgeRef{reference};
        const mapping = try findIncomingCloneLineageValueMappingAllocWithReplayCache(
            allocator,
            program,
            analysis,
            producer,
            source_value,
            &one,
            lineage_index,
            replay_index,
            replay_cache,
        );
        if (mapping.ambiguous or mapping.value == null) return false;
    }
    return true;
}

fn isRematerializableConstant(
    program: *const ir.Program,
    value_id: ir.ValueId,
    function_id: ir.FunctionId,
) bool {
    if (value_id.index() >= program.values.len) return false;
    const value = program.values[value_id.index()];
    const origin = switch (value.origin) {
        .instruction_result => |instruction_origin| instruction_origin,
        .parameter, .capture, .block_parameter => return false,
    };
    if (origin.instruction.index() >= program.instructions.len) return false;
    const instruction = program.instructions[origin.instruction.index()];
    if (instruction.id != origin.instruction or instruction.block.index() >= program.blocks.len) {
        return false;
    }
    if (instruction.results.len <= origin.index or instruction.results[origin.index] != value_id or
        program.blocks[instruction.block.index()].function != function_id or
        !std.meta.eql(instruction.effects, ir.EffectSummary.pure))
    {
        return false;
    }
    return switch (instruction.operation) {
        .constant => true,
        else => false,
    };
}

fn valueCarriesContinuationContext(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    value_id: ir.ValueId,
    source: ir.BlockId,
    closure: []const ir.BlockId,
    continuation: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!ContinuationValueContext {
    return valueCarriesContinuationContextWithPolicy(
        allocator,
        program,
        analysis,
        value_id,
        source,
        closure,
        continuation,
        incoming,
        lineage_index,
        replay_index,
        replay_cache,
        .ordinary,
    );
}

fn valueCarriesContinuationContextWithPolicy(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    value_id: ir.ValueId,
    source: ir.BlockId,
    closure: []const ir.BlockId,
    continuation: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
    policy: ContinuationValuePolicy,
) std.mem.Allocator.Error!ContinuationValueContext {
    if (value_id.index() >= program.values.len) return .unavailable;
    const value = program.values[value_id.index()];
    if (value.id != value_id or value.function != analysis.function.id) return .unavailable;
    const producer = switch (value.origin) {
        .parameter, .capture => return .available,
        .block_parameter => |origin| origin.block,
        .instruction_result => |origin| blk: {
            if (origin.instruction.index() >= program.instructions.len) return .unavailable;
            const instruction = program.instructions[origin.instruction.index()];
            if (instruction.id != origin.instruction or instruction.block.index() >= program.blocks.len) return .unavailable;
            break :blk instruction.block;
        },
    };
    if (producer == source or containsBlock(closure, producer) or containsBlock(continuation, producer)) return .contextual;
    if ((policy == .ordinary or policy == .incoming_parameter_bridge) and
        isRematerializableConstant(program, value_id, analysis.function.id)) return .available;

    if (replay_index) |cached| {
        if (!hasCloneLineageCandidateForSource(cached, program, producer)) {
            return if (definitionDominatesIncoming(analysis, producer, incoming)) .available else .unavailable;
        }
    }

    // A clone lineage is a stronger ownership fact than ordinary CFG
    // dominance.  The latter describes the unrewritten graph and can still
    // report a source producer as dominant after a contextual edge has been
    // redirected through a clone.
    if (try hasAuthenticatedDirectValueCloneForIncoming(
        program,
        analysis,
        producer,
        value_id,
        incoming,
        lineage_index,
    )) return .contextual;

    if (try hasAuthenticatedComposedValueCloneForIncoming(
        allocator,
        program,
        analysis,
        producer,
        value_id,
        incoming,
        lineage_index,
        replay_index,
        replay_cache,
    )) return .contextual;

    // A clone can hand control to a shared continuation without carrying its
    // formal IDs on every intervening edge.  The original value is still
    // usable only when the existing external-mapping proof selects one
    // replay-authenticated clone that dominates every incoming edge source.
    // Reuse that mapping here so closure discovery and closure remapping agree
    // on the same ownership fact.
    if (policy != .ordinary and lineage_index != null and replay_index != null) {
        if (try findExistingValueCloneAlloc(
            allocator,
            program,
            analysis,
            producer,
            value_id,
            incoming,
            closure,
            lineage_index,
            replay_index.?,
            replay_cache,
        )) |mapped| {
            if (mapped != value_id) return .contextual;
        }
    }

    if (definitionDominatesIncoming(analysis, producer, incoming)) return .available;

    // A bypassed producer is usable only when an earlier authenticated split
    // already maps this value into the incoming context. Non-dominance alone
    // is not evidence that the value can be reconstructed.
    return .unavailable;
}

fn hasAuthenticatedPackCloneForIncoming(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    producer: ir.BlockId,
    source_pack: ir.ValuePackId,
    incoming: []const ir.CfgEdgeRef,
    closure: []const ir.BlockId,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!bool {
    const replay = replay_index orelse return false;
    if (incoming.len == 0) return false;
    const mapped = try findExistingPackCloneAlloc(
        allocator,
        program,
        analysis,
        producer,
        source_pack,
        incoming,
        closure,
        lineage_index,
        replay,
        replay_cache,
    ) orelse return false;

    // A non-dominating producer can only be projected through a distinct pack
    // identity. Reusing the source identity would not establish which branch
    // produced the pack at the continuation boundary.
    return mapped != source_pack;
}

fn packCarriesContinuationContext(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    pack_id: ir.ValuePackId,
    source: ir.BlockId,
    closure: []const ir.BlockId,
    continuation: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!ContinuationValueContext {
    if (pack_id.index() >= program.value_packs.len) return .unavailable;
    const pack = program.value_packs[pack_id.index()];
    if (pack.id != pack_id or pack.function != analysis.function.id) return .unavailable;
    const producer = switch (pack.origin) {
        .varargs => return .available,
        .instruction_result => |instruction_id| blk: {
            if (instruction_id.index() >= program.instructions.len) return .unavailable;
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or instruction.block.index() >= program.blocks.len) return .unavailable;
            break :blk instruction.block;
        },
    };
    if (producer == source or containsBlock(closure, producer) or containsBlock(continuation, producer)) {
        if (containsBlock(continuation, producer) and
            analysis.dominates(producer, source))
        {
            return .available;
        }
        return .contextual;
    }

    const replay = replay_index orelse return if (definitionDominatesIncoming(analysis, producer, incoming))
        .available
    else
        .unavailable;
    if (!hasCloneLineageCandidateForSource(replay, program, producer)) {
        return if (definitionDominatesIncoming(analysis, producer, incoming)) .available else .unavailable;
    }

    if (try hasAuthenticatedPackCloneForIncoming(
        allocator,
        program,
        analysis,
        producer,
        pack_id,
        incoming,
        closure,
        lineage_index,
        replay_index,
        replay_cache,
    )) return .contextual;

    if (definitionDominatesIncoming(analysis, producer, incoming)) return .available;
    return .unavailable;
}

fn sameContinuationValueType(
    program: *const ir.Program,
    left: ir.ValueId,
    right: ir.ValueId,
) bool {
    if (left.index() >= program.values.len or right.index() >= program.values.len) return false;
    const left_value = program.values[left.index()];
    const right_value = program.values[right.index()];
    return left_value.id == left and right_value.id == right and
        left_value.function == right_value.function and
        left_value.type.kind == right_value.type.kind and
        left_value.type.bit_width == right_value.type.bit_width and
        left_value.type.signed == right_value.type.signed;
}

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

fn hasLiveIncomingEdgeWithArguments(
    program: *const ir.Program,
    target: ir.BlockId,
    arguments: []const ir.ValueId,
) bool {
    if (target.index() >= program.blocks.len) return false;
    const target_block = program.blocks[target.index()];
    if (target_block.id != target or arguments.len != target_block.parameters.len) return false;

    for (program.blocks) |source| {
        if (source.id.index() >= program.blocks.len or source.id == target and source.function != target_block.function) continue;
        if (source.function != target_block.function) continue;
        switch (source.terminator) {
            .jump => |edge| {
                if (edge.target == target and std.mem.eql(ir.ValueId, edge.arguments, arguments)) return true;
            },
            .branch => |branch| {
                if ((branch.then_edge.target == target and
                    std.mem.eql(ir.ValueId, branch.then_edge.arguments, arguments)) or
                    (branch.else_edge.target == target and
                        std.mem.eql(ir.ValueId, branch.else_edge.arguments, arguments))) return true;
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }
    return false;
}

fn hasLiveIncomingEdgeToTarget(
    program: *const ir.Program,
    target: ir.BlockId,
) bool {
    if (target.index() >= program.blocks.len) return false;
    const target_block = program.blocks[target.index()];
    if (target_block.id != target) return false;

    for (program.blocks) |source| {
        if (source.id.index() >= program.blocks.len or source.function != target_block.function) continue;
        switch (source.terminator) {
            .jump => |edge| if (edge.target == target) return true,
            .branch => |branch| if (branch.then_edge.target == target or branch.else_edge.target == target) return true,
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }
    return false;
}

// A numeric transition consumes a fresh four-slot state tuple on every
// iteration.  When that tuple is carried through an effectful or branched
// continuation, its SSA identities need not be the direct results of the
// transition instruction.  A canonical complete back edge into the same
// numeric header is still a semantic loop-state entry: the header's
// `numeric_for_next` operation defines how those slots are consumed.  Keep
// this proof separate from generic value equivalence so arbitrary same-typed
// values or acyclic joins cannot cross the continuation boundary.
fn authenticatedNumericLoopCarriedTupleProjection(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    reference: ir.CfgEdgeRef,
    expected: []const ir.ValueId,
    actual: []const ir.ValueId,
) std.mem.Allocator.Error!bool {
    if (reference.target.index() >= program.blocks.len or
        expected.len != 4 or actual.len != 4 or
        std.mem.eql(ir.ValueId, expected, actual) or
        !incomingEdgeIsCanonical(program, analysis, reference) or
        !isIterationTransitionHeader(program, reference.target) or
        !try analysis.canReach(reference.target, reference.source) or
        !try analysis.canReach(reference.source, reference.target) or
        !hasLiveIncomingEdgeWithArguments(program, reference.target, expected))
    {
        return false;
    }

    const block = program.blocks[reference.target.index()];
    if (block.id != reference.target or
        block.function != analysis.function.id or
        !node_split.parametersAreCanonical(program.values, block) or
        actual.len != block.parameters.len)
    {
        return false;
    }
    for (block.parameters, actual) |formal, argument| {
        if (!sameContinuationValueType(program, formal, argument)) return false;
    }
    return true;
}

fn hasActiveNodeSplitIntoTargetWithArguments(
    program: *const ir.Program,
    target: ir.BlockId,
    arguments: []const ir.ValueId,
) bool {
    for (program.edge_rewrites) |rewrite| {
        if (rewrite.rule != .node_split or rewrite.to.target != target or
            !std.mem.eql(ir.ValueId, rewrite.to.arguments, arguments)) continue;
        if (activeNodeSplitRewrite(program, rewrite)) return true;
    }
    return false;
}

// Authenticate the common non-numeric loop-carried parameter shape.  The
// target formal tuple must be canonical, the owner tuple must be a live edge
// into that target, and a split target must retain complete replay lineage.
// Requiring the re-entry tuple to be the target's own formals prevents a
// same-typed value from being promoted merely because it reaches the block.
fn parameterizedForwardingReentryMatches(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    target: ir.BlockId,
    expected: []const ir.ValueId,
    actual: []const ir.ValueId,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    if (target.index() >= program.blocks.len) return false;
    const target_block = program.blocks[target.index()];
    if (target_block.id != target or target_block.parameters.len == 0 or
        expected.len != target_block.parameters.len or
        actual.len != target_block.parameters.len or
        !node_split.parametersAreCanonical(program.values, target_block) or
        !std.mem.eql(ir.ValueId, actual, target_block.parameters))
    {
        return false;
    }

    for (target_block.parameters, expected) |formal, incoming| {
        if (!sameContinuationValueType(program, formal, incoming)) return false;
    }
    // `actual` is the target's canonical formal tuple, so it is represented
    // by the block entry contract rather than by a second edge.  The owner
    // tuple must still be carried by a live edge; requiring another edge with
    // the formal IDs rejects legitimate cloned continuation entries.
    if (!hasLiveIncomingEdgeWithArguments(program, target, expected)) return false;

    if (cloneStepForTargetCached(program, target, lineage_index)) |step| {
        if (!hasActiveNodeSplitIntoTargetWithArguments(program, target, expected) or
            !try cloneLineageArgumentsMatchReplayCached(
                allocator,
                program,
                step.source,
                target,
                lineage_index,
                replay_index,
                replay_cache,
            )) return false;
    }
    return true;
}

// A parameterized continuation can carry a loop state tuple whose producers
// are reached only after the target is entered.  Admit that cycle as one
// authenticated unit: every deferred producer must be in the same reachable
// SCC as the edge source and target.  Values outside the SCC still need the
// ordinary incoming-context proof below.
fn loopCarriedValueIsInContinuationScc(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.BlockId,
    target: ir.BlockId,
    value_id: ir.ValueId,
) std.mem.Allocator.Error!bool {
    if (source.index() >= program.blocks.len or target.index() >= program.blocks.len or
        program.blocks[source.index()].function != analysis.function.id or
        program.blocks[target.index()].function != analysis.function.id or
        !try analysis.canReach(target, source)) return false;
    const producer = projectionValueProducer(program, value_id) orelse return false;
    if (producer.index() >= program.blocks.len or
        program.blocks[producer.index()].function != analysis.function.id)
    {
        return false;
    }
    return try analysis.canReach(target, producer) and
        try analysis.canReach(producer, source);
}

// A multi-entry, parameterless forwarding join can be the shared boundary of
// a loop-carried tuple.  Its successor owns the tuple contract; cloning the
// join would root the clone before the tuple's producer and manufacture a
// non-dominating value.  Keep this boundary shared when every forwarded value
// is authenticated by the same loop SCC.
fn isSharedLoopForwardingBoundary(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    block_id: ir.BlockId,
) std.mem.Allocator.Error!bool {
    if (!isParameterlessForwardingBlock(program, analysis, block_id)) return false;

    var reachable_predecessors: usize = 0;
    var predecessor_index: usize = 0;
    while (analysis.predecessorAt(block_id, predecessor_index)) |predecessor| : (predecessor_index += 1) {
        if (analysis.isReachable(predecessor)) reachable_predecessors += 1;
    }
    if (reachable_predecessors < 2) return false;

    const block = program.blocks[block_id.index()];
    const edge = switch (block.terminator) {
        .jump => |value| value,
        .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
    };
    if (edge.target.index() >= program.blocks.len) return false;
    const target = program.blocks[edge.target.index()];
    if (target.id != edge.target or target.function != analysis.function.id or
        target.parameters.len == 0 or edge.arguments.len != target.parameters.len or
        !node_split.parametersAreCanonical(program.values, target) or
        !try analysis.canReach(edge.target, block_id))
    {
        return false;
    }
    for (edge.arguments) |argument| {
        if (!try loopCarriedValueIsInContinuationScc(
            program,
            analysis,
            block_id,
            edge.target,
            argument,
        )) return false;
    }
    return true;
}

// A block-parameter projection may cross a loop-carried source clone rather
// than a direct node-split bridge. Require the value producer to be reachable
// after the incoming context and to dominate the replay-stable source edge.
// This authenticates an existing value on the carried path; it does not invent
// a value or relax ordinary dominance.
fn valueIsAvailableFromIncomingContext(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    value_id: ir.ValueId,
) std.mem.Allocator.Error!bool {
    if (incoming.len == 0 or source.index() >= program.blocks.len or
        program.blocks[source.index()].function != analysis.function.id)
    {
        return false;
    }
    const producer = projectionValueProducer(program, value_id) orelse return false;
    if (producer.index() >= program.blocks.len or
        program.blocks[producer.index()].function != analysis.function.id)
    {
        return false;
    }
    for (incoming) |reference| {
        if (!incomingEdgeIsCanonical(program, analysis, reference) or
            !try analysis.canReach(reference.target, source) or
            !try analysis.canReach(reference.target, producer) or
            !try analysis.canReach(producer, source) or
            !analysis.dominates(producer, source))
        {
            return false;
        }
    }
    return true;
}

// A normalized iteration tuple may be forwarded through a shared
// parameterized continuation. Authenticate it against the complete incoming
// tuple at the iteration header before treating the forwarding edge as
// context-independent. Ordinary tuples continue through per-value checks.
fn authenticatedIterationTupleForwardingForIncomingAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.BlockId,
    target: ir.BlockId,
    arguments: []const ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!bool {
    if (arguments.len != 4 or
        iterationStateTupleTransition(program, arguments) == null or
        incoming.len == 0)
    {
        return false;
    }
    for (incoming) |reference| {
        if (!incomingEdgeIsCanonical(program, analysis, reference) or
            !isIterationTransitionHeader(program, reference.target) or
            !try analysis.canReach(reference.target, source) or
            !try analysis.canReach(source, target))
        {
            return false;
        }
        const edge = cfg_edge.value(program, reference) orelse return false;
        if (edge.arguments.len != arguments.len) return false;
        if (!try authenticatedIterationStateTupleEquivalentAlloc(
            allocator,
            program,
            reference.target,
            edge.arguments,
            arguments,
            lineage_index,
            replay_index,
            replay_cache,
        )) return false;
    }
    return true;
}

// A parameterized continuation is usable only when its formal tuple is
// carried positionally by the authenticated incoming edge. This keeps the
// projection semantic: equal-looking values or a guessed re-materialization
// cannot stand in for a missing block-parameter identity.
fn parameterizedContinuationArgumentsAreAuthenticated(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.BlockId,
    target: ir.BlockId,
    arguments: []const ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
    closure: []const ir.BlockId,
    continuation: []const ir.BlockId,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
    policy: ContinuationValuePolicy,
) std.mem.Allocator.Error!bool {
    if (target.index() >= program.blocks.len or incoming.len == 0) return false;
    const target_block = program.blocks[target.index()];
    if (target_block.id != target or target_block.parameters.len == 0 or
        arguments.len != target_block.parameters.len or
        !node_split.parametersAreCanonical(program.values, target_block))
    {
        return false;
    }

    for (target_block.parameters, arguments) |parameter, argument| {
        if (!sameContinuationValueType(program, parameter, argument)) return false;
    }

    if (policy == .authenticated_parameter) {
        if (lineage_index) |lineage| {
            if (replay_index) |replay| {
                if (replay_cache) |cache| {
                    if (try authenticatedIterationTupleForwardingForIncomingAlloc(
                        allocator,
                        program,
                        analysis,
                        source,
                        target,
                        arguments,
                        incoming,
                        lineage,
                        replay,
                        cache,
                    )) return true;
                }
            }
        }
    }

    for (target_block.parameters, arguments) |parameter, argument| {
        const context = try valueCarriesContinuationContextWithPolicy(
            allocator,
            program,
            analysis,
            argument,
            source,
            closure,
            continuation,
            incoming,
            lineage_index,
            replay_index,
            replay_cache,
            policy,
        );
        if (trace_structural_phases and closure.len <= 2 and incoming.len == 1) {
            traceStructural("parameter_bridge_context source={} target={} parameter={} argument={} policy={s} context={s}\n", .{
                source.index(),
                target.index(),
                parameter.index(),
                argument.index(),
                @tagName(policy),
                @tagName(context),
            });
        }
        switch (context) {
            .available, .contextual => {},
            .unavailable => {
                const in_scc = if (policy == .incoming_parameter_bridge)
                    try valueIsAvailableFromIncomingContext(program, analysis, source, incoming, argument)
                else
                    try loopCarriedValueIsInContinuationScc(program, analysis, source, target, argument);
                if (!in_scc) {
                    if (trace_structural_phases and closure.len >= 50) {
                        std.debug.print("parameter_bridge_argument_rejected source={} target={} parameter={} argument={} policy={s} context={s} closure={}\n", .{
                            source.index(),
                            target.index(),
                            parameter.index(),
                            argument.index(),
                            @tagName(policy),
                            @tagName(context),
                            closure.len,
                        });
                        if (projectionValueProducer(program, argument)) |argument_producer| {
                            std.debug.print("parameter_bridge_scc_detail source={} target={} producer={} target_to_source={} target_to_producer={} producer_to_source={} source_to_target={}\n", .{
                                source.index(),
                                target.index(),
                                argument_producer.index(),
                                try analysis.canReach(target, source),
                                try analysis.canReach(target, argument_producer),
                                try analysis.canReach(argument_producer, source),
                                try analysis.canReach(source, target),
                            });
                            for (incoming) |reference| {
                                std.debug.print("parameter_bridge_incoming_scc source={} incoming_source={} incoming_target={} incoming_target_to_producer={} producer_to_source={} source_to_incoming_target={}\n", .{
                                    source.index(),
                                    reference.source.index(),
                                    reference.target.index(),
                                    try analysis.canReach(reference.target, argument_producer),
                                    try analysis.canReach(argument_producer, source),
                                    try analysis.canReach(source, reference.target),
                                });
                                std.debug.print("parameter_bridge_dominance producer={} source={} dominates={}\n", .{
                                    argument_producer.index(),
                                    source.index(),
                                    analysis.dominates(argument_producer, source),
                                });
                            }
                        }
                    }
                    return false;
                }
                if (trace_structural_phases and closure.len >= 50) {
                    std.debug.print("parameter_bridge_argument_scc source={} target={} parameter={} argument={} policy={s} closure={}\n", .{
                        source.index(),
                        target.index(),
                        parameter.index(),
                        argument.index(),
                        @tagName(policy),
                        closure.len,
                    });
                }
            },
        }
    }
    return true;
}

fn edgeCarriesContinuationContext(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.BlockId,
    successor_index: usize,
    closure: []const ir.BlockId,
    continuation: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!bool {
    const reference = successorEdgeRef(program, source, successor_index) orelse return false;
    const edge = cfg_edge.value(program, reference) orelse return false;
    if (edge.target != reference.target or edge.target.index() >= program.blocks.len) return false;
    const target_block = program.blocks[edge.target.index()];
    if (target_block.id != edge.target) return false;
    const parameterized = target_block.parameters.len != 0;
    if (parameterized and !try parameterizedContinuationArgumentsAreAuthenticated(
        allocator,
        program,
        analysis,
        source,
        edge.target,
        edge.arguments,
        incoming,
        closure,
        continuation,
        lineage_index,
        replay_index,
        replay_cache,
        .authenticated_parameter,
    )) return false;
    if (parameterized) return true;
    for (edge.arguments) |argument| {
        switch (try valueCarriesContinuationContext(
            allocator,
            program,
            analysis,
            argument,
            source,
            closure,
            continuation,
            incoming,
            lineage_index,
            replay_index,
            replay_cache,
        )) {
            .available => {},
            .contextual => {},
            .unavailable => return false,
        }
    }
    return true;
}

fn edgeArgumentsCarryClosureValue(
    program: *const ir.Program,
    source: ir.BlockId,
    target: ir.BlockId,
    closure: []const ir.BlockId,
) bool {
    const source_block = if (source.index() < program.blocks.len) program.blocks[source.index()] else return true;
    if (source_block.id != source) return true;
    switch (source_block.terminator) {
        .jump => |edge| if (edge.target == target) for (edge.arguments) |argument| {
            const producer = projectionValueProducer(program, argument) orelse continue;
            if (containsBlock(closure, producer)) return true;
        },
        .branch => |branch| for (&[_]ir.Edge{ branch.then_edge, branch.else_edge }) |edge| {
            if (edge.target != target) continue;
            for (edge.arguments) |argument| {
                const producer = projectionValueProducer(program, argument) orelse continue;
                if (containsBlock(closure, producer)) return true;
            }
        },
        else => {},
    }
    return false;
}

fn terminatorCarriesClosureValue(
    program: *const ir.Program,
    source: ir.BlockId,
    closure: []const ir.BlockId,
) bool {
    if (source.index() >= program.blocks.len) return true;
    const block = program.blocks[source.index()];
    if (block.id != source) return true;
    return switch (block.terminator) {
        .jump => |edge| edgeArgumentsCarryClosureValue(program, source, edge.target, closure),
        .branch => |branch| edgeArgumentsCarryClosureValue(program, source, branch.then_edge.target, closure) or
            edgeArgumentsCarryClosureValue(program, source, branch.else_edge.target, closure),
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => false,
    };
}

fn parameterizedContinuationBridge(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    source: ir.BlockId,
    successor_index: usize,
    target: ir.BlockId,
    stop: ir.BlockId,
    closure: []const ir.BlockId,
    continuation: []const ir.BlockId,
    incoming: ?[]const ir.CfgEdgeRef,
    lineage_index: ?*const CloneLineageIndex,
    replay_index: ?*const node_split.ReplayIndex,
    replay_cache: ?*ReplayCache,
) std.mem.Allocator.Error!bool {
    if (target.index() >= program.blocks.len or program.blocks[target.index()].parameters.len == 0) return false;
    const target_block = program.blocks[target.index()];
    if (target_block.id != target) return false;
    const references = incoming orelse return false;
    _ = stop;
    const reference = successorEdgeRef(program, source, successor_index) orelse return false;
    const edge = cfg_edge.value(program, reference) orelse return false;
    if (edge.target != reference.target or edge.arguments.len != target_block.parameters.len) return false;
    // A complete iteration-state tuple returning to its own header is a
    // back-edge, not a new contextual continuation.  If that header already
    // dominates every incoming source, its transition has executed before
    // the contextual entry and must remain shared.  Cloning it would turn the
    // back-edge's result into the first input of the cloned header, creating a
    // self-dependent initial iteration.
    if (sharedIterationHeaderBoundaryAtIncoming(
        program,
        analysis,
        target,
        edge.arguments,
        references,
    )) return false;
    return edgeCarriesContinuationContext(
        allocator,
        program,
        analysis,
        source,
        successor_index,
        closure,
        continuation,
        references,
        lineage_index,
        replay_index,
        replay_cache,
    );
}

fn sharedIterationHeaderBoundaryAtIncoming(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    target: ir.BlockId,
    arguments: []const ir.ValueId,
    incoming: []const ir.CfgEdgeRef,
) bool {
    if (incoming.len == 0 or !isIterationTransitionHeader(program, target)) return false;
    const transition = iterationStateTupleTransition(program, arguments) orelse return false;
    if (transition.block != target) return false;

    for (incoming) |reference| {
        if (!incomingEdgeIsCanonical(program, analysis, reference) or
            reference.source == target or
            !analysis.isReachable(reference.source) or
            !analysis.dominates(target, reference.source))
        {
            return false;
        }
    }
    return true;
}

// A collision suffix may end at a shared zero-parameter forwarding chain
// before it hands the complete iteration state back to its header.  The
// forwarding blocks are not part of the clone, so authenticate this boundary
// separately from ordinary continuation-context uses.  Keep the chain
// straight-line and bounded: a branch, parameterized carrier, incoming-source
// hop, or non-terminating cycle is not an iteration handoff proof.
fn authenticatedIterationHandoffBoundaryAtIncoming(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    entry: ir.BlockId,
    closure: []const ir.BlockId,
    boundary: ir.CfgEdgeRef,
    incoming: []const ir.CfgEdgeRef,
    expected_header: ?ir.BlockId,
) std.mem.Allocator.Error!bool {
    if (incoming.len == 0 or boundary.source != entry and !containsBlock(closure, boundary.source)) return false;

    var handoff = boundary;
    var hops: usize = 0;
    while (hops <= analysis.function.blocks.len) : (hops += 1) {
        if (handoff.target.index() >= program.blocks.len or
            !analysis.isReachable(handoff.target) or
            handoff.target == entry or
            containsBlock(closure, handoff.target) or
            !incomingEdgeIsCanonical(program, analysis, handoff))
        {
            return false;
        }
        for (incoming) |reference| {
            if (handoff.target == reference.source) return false;
        }

        const edge = cfg_edge.value(program, handoff) orelse return false;
        const block = program.blocks[handoff.target.index()];
        if (block.id != handoff.target or block.function != analysis.function.id or
            edge.arguments.len != block.parameters.len)
        {
            return false;
        }

        if (isIterationTransitionHeader(program, handoff.target)) {
            // `stop` is usually the collision block that bounds the
            // continuation, not an iteration header.  Constrain the handoff
            // only when the caller supplied an actual iteration-header stop;
            // otherwise a valid handoff to the loop's own header would be
            // rejected merely because the collision block has a different id.
            if (expected_header) |expected| {
                if (isIterationTransitionHeader(program, expected) and handoff.target != expected) return false;
            }
            if (!try analysis.canReach(handoff.target, entry)) return false;
            return sharedIterationHeaderBoundaryAtIncoming(
                program,
                analysis,
                handoff.target,
                edge.arguments,
                incoming,
            );
        }

        if (block.parameters.len != 0) return false;
        switch (block.terminator) {
            .jump => |next| {
                if (next.target.index() >= program.blocks.len or
                    (!isIterationTransitionHeader(program, next.target) and next.arguments.len != 0)) return false;
                handoff = .{ .source = handoff.target, .kind = .jump, .target = next.target };
            },
            .branch, .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => return false,
        }
    }
    return false;
}

test "contextual continuation stops before a shared iteration header" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const header = ir.BlockId.fromIndex(1);
    const body = ir.BlockId.fromIndex(2);
    const incoming_source = ir.BlockId.fromIndex(3);
    const continuation = ir.BlockId.fromIndex(4);

    const control = ir.ValueId.fromIndex(0);
    const limit = ir.ValueId.fromIndex(1);
    const step = ir.ValueId.fromIndex(2);
    const header_control = ir.ValueId.fromIndex(3);
    const header_limit = ir.ValueId.fromIndex(4);
    const header_step = ir.ValueId.fromIndex(5);
    const header_initial = ir.ValueId.fromIndex(6);
    const false_value = ir.ValueId.fromIndex(7);
    const has_next = ir.ValueId.fromIndex(8);
    const normalized_limit = ir.ValueId.fromIndex(9);
    const normalized_step = ir.ValueId.fromIndex(10);
    const next_control = ir.ValueId.fromIndex(11);
    const false_instruction = ir.InstructionId.fromIndex(0);
    const transition_instruction = ir.InstructionId.fromIndex(1);

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .instructions = &.{false_instruction}, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &.{ control, limit, step, false_value },
        } } },
        .{ .id = header, .function = function_id, .parameters = &.{
            header_control, header_limit, header_step, header_initial,
        }, .instructions = &.{transition_instruction}, .terminator = .{ .branch = .{
            .condition = has_next,
            .then_edge = .{ .target = body },
            .else_edge = .{ .target = incoming_source },
        } } },
        .{ .id = body, .function = function_id, .terminator = .{ .jump = .{
            .target = header,
            .arguments = &.{ next_control, normalized_limit, normalized_step, false_value },
        } } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{ .target = continuation } } },
        .{ .id = continuation, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ control, limit, step },
        .blocks = &.{ entry, header, body, incoming_source, continuation },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = control, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 0 } },
        .{ .id = limit, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 1 } },
        .{ .id = step, .function = function_id, .type = .dynamic, .origin = .{ .parameter = 2 } },
        .{ .id = header_control, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header, .index = 0 } } },
        .{ .id = header_limit, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header, .index = 1 } } },
        .{ .id = header_step, .function = function_id, .type = .dynamic, .origin = .{ .block_parameter = .{ .block = header, .index = 2 } } },
        .{ .id = header_initial, .function = function_id, .type = .boolean, .origin = .{ .block_parameter = .{ .block = header, .index = 3 } } },
        .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_instruction, .index = 0 } } },
        .{ .id = has_next, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 0 } } },
        .{ .id = normalized_limit, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 1 } } },
        .{ .id = normalized_step, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 2 } } },
        .{ .id = next_control, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = transition_instruction, .index = 3 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = false_instruction, .block = entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = transition_instruction, .block = header, .operation = .{ .numeric_for_next = .{
            .control = header_control,
            .limit = header_limit,
            .step = header_step,
            .initial = header_initial,
            .mode = .semantic_normalized,
        } }, .results = &.{ has_next, normalized_limit, normalized_step, next_control }, .effects = .numeric_for_next },
    };
    const program = ir.Program{
        .program_id = "shared-iteration-header-boundary",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();

    const incoming = [_]ir.CfgEdgeRef{.{
        .source = incoming_source,
        .kind = .jump,
        .target = continuation,
    }};
    try std.testing.expect(sharedIterationHeaderBoundaryAtIncoming(
        &program,
        &analysis,
        header,
        &.{ next_control, normalized_limit, normalized_step, false_value },
        &incoming,
    ));
    try std.testing.expect(!try parameterizedContinuationBridge(
        std.testing.allocator,
        &program,
        &analysis,
        body,
        0,
        header,
        continuation,
        &.{continuation},
        &.{},
        &incoming,
        null,
        null,
        null,
    ));
}

const SharedSuffixContextDetector = struct {
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    region: []const bool,
    incoming: []const ir.CfgEdgeRef,
    found: bool = false,

    fn mark(self: *SharedSuffixContextDetector) void {
        self.found = true;
    }

    fn blockIsShared(self: *const SharedSuffixContextDetector, block_id: ir.BlockId) bool {
        const local_index = self.analysis.blockIndex(block_id) orelse return false;
        return local_index < self.region.len and self.region[local_index];
    }

    fn externalDefinitionIsAvailable(
        self: *const SharedSuffixContextDetector,
        producer: ir.BlockId,
    ) bool {
        return self.blockIsShared(producer) or
            definitionDominatesIncoming(self.analysis, producer, self.incoming);
    }

    pub fn value(self: *SharedSuffixContextDetector, value_id: ir.ValueId) void {
        if (self.found) return;
        if (value_id.index() >= self.program.values.len) {
            self.mark();
            return;
        }
        const item = self.program.values[value_id.index()];
        if (item.id != value_id or item.function != self.analysis.function.id) {
            self.mark();
            return;
        }
        switch (item.origin) {
            .parameter, .capture => {},
            .block_parameter => |origin| {
                if (!self.externalDefinitionIsAvailable(origin.block)) self.mark();
            },
            .instruction_result => |origin| {
                if (origin.instruction.index() >= self.program.instructions.len) {
                    self.mark();
                    return;
                }
                const instruction = self.program.instructions[origin.instruction.index()];
                if (instruction.id != origin.instruction or
                    !self.externalDefinitionIsAvailable(instruction.block))
                {
                    self.mark();
                }
            },
        }
    }

    pub fn pack(self: *SharedSuffixContextDetector, pack_id: ir.ValuePackId) void {
        if (self.found) return;
        if (pack_id.index() >= self.program.value_packs.len) {
            self.mark();
            return;
        }
        const item = self.program.value_packs[pack_id.index()];
        if (item.id != pack_id or item.function != self.analysis.function.id) {
            self.mark();
            return;
        }
        switch (item.origin) {
            .varargs => {},
            .instruction_result => |instruction_id| {
                if (instruction_id.index() >= self.program.instructions.len) {
                    self.mark();
                    return;
                }
                const instruction = self.program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or
                    !self.externalDefinitionIsAvailable(instruction.block))
                {
                    self.mark();
                }
            },
        }
    }

    pub fn place(self: *SharedSuffixContextDetector, place_id: ir.PlaceId) void {
        if (self.found) return;
        if (place_id.index() >= self.program.places.len) {
            self.mark();
            return;
        }
        const item = self.program.places[place_id.index()];
        if (item.id != place_id or item.function != self.analysis.function.id) {
            self.mark();
            return;
        }
        switch (item.origin) {
            .local, .capture => {},
            .instruction => |instruction_id| {
                if (instruction_id.index() >= self.program.instructions.len) {
                    self.mark();
                    return;
                }
                const instruction = self.program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or
                    !self.externalDefinitionIsAvailable(instruction.block))
                {
                    self.mark();
                }
            },
        }
    }
};

fn blockUsesSharedSuffixContext(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    block: ir.Block,
    region: []const bool,
    incoming: []const ir.CfgEdgeRef,
) bool {
    var detector = SharedSuffixContextDetector{
        .program = program,
        .analysis = analysis,
        .region = region,
        .incoming = incoming,
    };
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return true;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or instruction.block != block.id) return true;
        if (proof_effect_closure.hasObservableEffects(instruction.effects)) return true;
        runtime_uses.visitOperationUses(instruction.operation, &detector);
        if (detector.found) return true;
    }
    switch (block.terminator) {
        .throw_error => return true,
        else => {},
    }
    runtime_uses.visitTerminatorUses(block.terminator, &detector);
    return detector.found;
}

fn isSharedSuffixBoundary(
    block: ir.BlockId,
    stop: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
) bool {
    if (block == stop) return true;
    for (incoming) |reference| if (reference.target == block) return true;
    return false;
}

fn regionHasRetainedInClosurePredecessor(
    analysis: *const cfg.Analysis,
    membership: []const bool,
    removed: []const bool,
    region: []const bool,
    stop: ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    block: ir.BlockId,
) bool {
    var predecessor_index: usize = 0;
    while (analysis.predecessorAt(block, predecessor_index)) |predecessor| : (predecessor_index += 1) {
        const predecessor_local = analysis.blockIndex(predecessor) orelse return true;
        if (!membership[predecessor_local] or
            region[predecessor_local] or
            removed[predecessor_local] or
            isSharedSuffixBoundary(predecessor, stop, incoming))
        {
            continue;
        }
        return true;
    }
    return false;
}

fn trimContextIndependentSharedSuffixAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    stop: ir.BlockId,
    closure: []ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
) std.mem.Allocator.Error![]ir.BlockId {
    if (closure.len < 2 or incoming.len == 0) return closure;

    if (trace_structural_phases and closure.len >= 100) {
        traceStructural("shared_suffix_trim_begin stop={} closure={} incoming={}\n", .{
            stop.index(),
            closure.len,
            incoming.len,
        });
    }

    const function_block_count = analysis.function.blocks.len;
    const membership = try allocator.alloc(bool, function_block_count);
    defer allocator.free(membership);
    @memset(membership, false);
    for (closure) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return closure;
        membership[local_index] = true;
    }

    const removed = try allocator.alloc(bool, function_block_count);
    defer allocator.free(removed);
    @memset(removed, false);
    var changed = true;
    while (changed) {
        changed = false;
        for (closure) |start| {
            const start_index = analysis.blockIndex(start) orelse return closure;
            if (removed[start_index] or isSharedSuffixBoundary(start, stop, incoming)) {
                continue;
            }
            const start_block = program.blocks[start.index()];
            if (start_block.id != start) continue;
            if (start_block.parameters.len != 0) {
                if (!node_split.parametersAreCanonical(program.values, start_block)) continue;
            }

            const region = try allocator.alloc(bool, function_block_count);
            @memset(region, false);
            defer allocator.free(region);
            var pending: std.ArrayList(ir.BlockId) = .empty;
            defer pending.deinit(allocator);
            try pending.append(allocator, start);
            var valid = true;
            while (pending.pop()) |current| {
                const current_index = analysis.blockIndex(current) orelse {
                    valid = false;
                    break;
                };
                if (region[current_index]) continue;
                if (!membership[current_index] or removed[current_index]) {
                    valid = false;
                    break;
                }
                // The preserved stop/incoming boundary is shared by the
                // original graph.  A pure region may hand control back to it;
                // it must not become part of the clone closure itself.
                if (isSharedSuffixBoundary(current, stop, incoming)) continue;
                const current_block = program.blocks[current.index()];
                if (current_block.id != current or
                    !node_split.parametersAreCanonical(program.values, current_block))
                {
                    valid = false;
                    break;
                }
                region[current_index] = true;
                if (blockUsesSharedSuffixContext(program, analysis, current_block, region, incoming)) {
                    if (trace_structural_phases and closure.len >= 100) {
                        traceStructural("shared_suffix_trim_context_reject start={} current={}\n", .{
                            start.index(),
                            current.index(),
                        });
                    }
                    valid = false;
                    break;
                }
                for (0..analysis.successorCount(current)) |successor_index| {
                    const successor = analysis.successorAt(current, successor_index) orelse {
                        valid = false;
                        break;
                    };
                    const successor_local = analysis.blockIndex(successor) orelse continue;
                    if (membership[successor_local]) try pending.append(allocator, successor);
                }
                if (!valid) break;
            }
            if (!valid) continue;

            // Do not remove a pure tail independently when a retained
            // in-closure predecessor still transfers into it.  A complete
            // pure suffix can be removed, but an effectful predecessor keeps
            // its downstream control-flow tail in the clone closure.
            for (closure) |candidate| {
                const candidate_index = analysis.blockIndex(candidate) orelse {
                    valid = false;
                    break;
                };
                if (region[candidate_index] and regionHasRetainedInClosurePredecessor(
                    analysis,
                    membership,
                    removed,
                    region,
                    stop,
                    incoming,
                    candidate,
                )) {
                    valid = false;
                    break;
                }
            }
            if (!valid) continue;

            if (trace_structural_phases and closure.len >= 100) {
                traceStructural("shared_suffix_trim_region start={} size={}\n", .{
                    start.index(),
                    std.mem.countScalar(bool, region, true),
                });
            }

            for (analysis.function.blocks, 0..) |_, local_index| {
                if (region[local_index] and !removed[local_index]) {
                    removed[local_index] = true;
                    changed = true;
                }
            }
        }
    }

    var removed_count: usize = 0;
    for (closure) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return closure;
        if (removed[local_index]) removed_count += 1;
    }
    if (removed_count == 0) return closure;

    var retained: std.ArrayList(ir.BlockId) = .empty;
    errdefer retained.deinit(allocator);
    try retained.ensureTotalCapacity(allocator, closure.len - removed_count);
    for (closure) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return closure;
        if (!removed[local_index]) try retained.append(allocator, block_id);
    }
    const owned = try retained.toOwnedSlice(allocator);
    allocator.free(closure);
    return owned;
}

fn trimShadowedUnreachableCloneBlocksAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    entry: ir.BlockId,
    closure: []ir.BlockId,
    lineage_index: *const CloneLineageIndex,
) std.mem.Allocator.Error![]ir.BlockId {
    if (closure.len < 2) return closure;

    const block_count = analysis.function.blocks.len;
    const membership = try allocator.alloc(bool, block_count);
    defer allocator.free(membership);
    @memset(membership, false);
    for (closure) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return closure;
        if (membership[local_index]) return closure;
        membership[local_index] = true;
    }

    const entry_index = analysis.blockIndex(entry) orelse return closure;
    if (!membership[entry_index]) return closure;

    const reachable = try allocator.alloc(bool, block_count);
    defer allocator.free(reachable);
    @memset(reachable, false);
    const pending = try allocator.alloc(ir.BlockId, closure.len);
    defer allocator.free(pending);
    reachable[entry_index] = true;
    pending[0] = entry;
    var cursor: usize = 0;
    var pending_len: usize = 1;
    while (cursor < pending_len) : (cursor += 1) {
        const current = pending[cursor];
        for (0..analysis.successorCount(current)) |successor_index| {
            const successor = analysis.successorAt(current, successor_index) orelse return closure;
            const successor_index_local = analysis.blockIndex(successor) orelse return closure;
            if (!membership[successor_index_local] or reachable[successor_index_local]) continue;
            reachable[successor_index_local] = true;
            if (pending_len >= pending.len) return closure;
            pending[pending_len] = successor;
            pending_len += 1;
        }
    }

    const shadowed = try allocator.alloc(bool, block_count);
    defer allocator.free(shadowed);
    @memset(shadowed, false);
    var removed_count: usize = 0;
    for (closure) |block_id| {
        const block_index = analysis.blockIndex(block_id) orelse return closure;
        if (reachable[block_index]) continue;
        if (cloneStepForTargetCached(program, block_id, lineage_index)) |step| {
            const source_index = analysis.blockIndex(step.source) orelse continue;
            if (!membership[source_index]) {
                shadowed[block_index] = true;
                removed_count += 1;
                continue;
            }
        }
        for (closure) |candidate| {
            const candidate_index = analysis.blockIndex(candidate) orelse return closure;
            if (!reachable[candidate_index]) continue;
            const step = cloneStepForTargetCached(program, candidate, lineage_index) orelse continue;
            if (step.source != block_id) continue;
            shadowed[block_index] = true;
            removed_count += 1;
            break;
        }
    }
    if (removed_count == 0) return closure;

    var retained: std.ArrayList(ir.BlockId) = .empty;
    errdefer retained.deinit(allocator);
    try retained.ensureTotalCapacity(allocator, closure.len - removed_count);
    for (closure) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return closure;
        if (!shadowed[local_index]) try retained.append(allocator, block_id);
    }
    const owned = try retained.toOwnedSlice(allocator);
    allocator.free(closure);
    return owned;
}

// A contextual split may discover a continuation path that loops back to the
// source of the edge being redirected.  Cloning that source would also clone
// the edge itself and make the new entry self-owned.  Treat incoming sources
// as external cycle boundaries, retaining only the part of the candidate that
// remains reachable from its entry without crossing one of those sources.
fn trimIncomingSourceClosureAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    entry: ir.BlockId,
    closure: []ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
) std.mem.Allocator.Error!?[]ir.BlockId {
    if (closure.len == 0 or incoming.len == 0) return closure;

    const block_count = analysis.function.blocks.len;
    const membership = try allocator.alloc(bool, block_count);
    defer allocator.free(membership);
    @memset(membership, false);

    var has_internal_source = false;
    for (closure) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return null;
        if (local_index >= membership.len or membership[local_index]) return null;
        membership[local_index] = true;
        for (incoming) |reference| {
            if (reference.source == block_id) {
                has_internal_source = true;
                break;
            }
        }
    }
    if (!has_internal_source) return closure;

    const entry_index = analysis.blockIndex(entry) orelse return null;
    if (!membership[entry_index]) return null;
    for (incoming) |reference| if (reference.source == entry) return null;

    const reachable = try allocator.alloc(bool, block_count);
    defer allocator.free(reachable);
    @memset(reachable, false);
    const pending = try allocator.alloc(ir.BlockId, closure.len);
    defer allocator.free(pending);

    reachable[entry_index] = true;
    pending[0] = entry;
    var cursor: usize = 0;
    var pending_len: usize = 1;
    while (cursor < pending_len) : (cursor += 1) {
        const current = pending[cursor];
        for (0..analysis.successorCount(current)) |successor_index| {
            const successor = analysis.successorAt(current, successor_index) orelse return null;
            const successor_index_local = analysis.blockIndex(successor) orelse return null;
            if (!membership[successor_index_local] or reachable[successor_index_local]) continue;
            var is_incoming_source = false;
            for (incoming) |reference| {
                if (reference.source == successor) {
                    is_incoming_source = true;
                    break;
                }
            }
            if (is_incoming_source) continue;
            reachable[successor_index_local] = true;
            if (pending_len >= pending.len) return null;
            pending[pending_len] = successor;
            pending_len += 1;
        }
    }

    var retained_count: usize = 0;
    for (closure) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return null;
        if (reachable[local_index]) retained_count += 1;
    }
    if (retained_count == 0) return null;
    if (retained_count == closure.len) return closure;

    var retained: std.ArrayList(ir.BlockId) = .empty;
    errdefer retained.deinit(allocator);
    try retained.ensureTotalCapacity(allocator, retained_count);
    for (closure) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return null;
        if (reachable[local_index]) try retained.append(allocator, block_id);
    }
    const owned = try retained.toOwnedSlice(allocator);
    allocator.free(closure);
    return owned;
}

fn appendDelayedUseContinuationAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    stop: ir.BlockId,
    closure: []const ir.BlockId,
    seeds: []const ir.BlockId,
    incoming: ?[]const ir.CfgEdgeRef,
    continuation: *std.ArrayList(ir.BlockId),
    lineage_index: *const CloneLineageIndex,
    replay_index: *const node_split.ReplayIndex,
    replay_cache: *ReplayCache,
) std.mem.Allocator.Error!void {
    if (seeds.len == 0) return;

    const block_count = analysis.function.blocks.len;
    const candidate = try allocator.alloc(bool, block_count);
    defer allocator.free(candidate);
    @memset(candidate, false);

    var pending: std.ArrayList(ir.BlockId) = .empty;
    defer pending.deinit(allocator);
    var candidates: std.ArrayList(ir.BlockId) = .empty;
    defer candidates.deinit(allocator);

    for (seeds) |seed| {
        if (seed == stop or containsBlock(closure, seed) or seed.index() >= program.blocks.len) continue;
        try pending.append(allocator, seed);
    }
    while (pending.pop()) |block_id| {
        if (block_id == stop or containsBlock(closure, block_id) or block_id.index() >= program.blocks.len) continue;
        const local_index = analysis.blockIndex(block_id) orelse continue;
        if (candidate[local_index]) continue;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id or block.function != analysis.function.id or
            !node_split.parametersAreCanonical(program.values, block)) continue;
        candidate[local_index] = true;
        try candidates.append(allocator, block_id);

        for (0..analysis.successorCount(block_id)) |successor_index| {
            const successor = analysis.successorAt(block_id, successor_index) orelse continue;
            if (successor == stop or containsBlock(closure, successor) or
                successor.index() >= program.blocks.len)
            {
                continue;
            }
            try pending.append(allocator, successor);
        }
    }
    if (trace_structural_phases and closure.len >= 20) {
        traceStructural("structural_delayed_frontier closure={} seeds={} candidates={}\n", .{
            closure.len,
            seeds.len,
            candidates.items.len,
        });
    }
    if (candidates.items.len == 0) return;

    const needed = try allocator.alloc(bool, block_count);
    defer allocator.free(needed);
    @memset(needed, false);
    const direct_needed = try allocator.alloc(bool, block_count);
    defer allocator.free(direct_needed);
    @memset(direct_needed, false);

    var needed_blocks: std.ArrayList(ir.BlockId) = .empty;
    defer needed_blocks.deinit(allocator);
    for (candidates.items) |block_id| {
        if (blockUsesDelayedClosureValue(
            allocator,
            program,
            analysis,
            program.blocks[block_id.index()],
            closure,
            lineage_index,
            replay_index,
            replay_cache,
        )) {
            const local_index = analysis.blockIndex(block_id) orelse continue;
            needed[local_index] = true;
            direct_needed[local_index] = true;
            try needed_blocks.append(allocator, block_id);
        }
    }
    if (trace_structural_phases and closure.len == 1 and incoming != null) {
        traceStructural("structural_delayed_candidates closure_entry={} seeds={} candidates={} direct={any}\n", .{
            closure[0].index(),
            seeds.len,
            candidates.items.len,
            needed_blocks.items,
        });
    }
    if (trace_structural_phases and closure.len >= 20) {
        traceStructural("structural_delayed_direct_uses closure={} direct={}\n", .{
            closure.len,
            needed_blocks.items.len,
        });
    }

    // Any predecessor on a candidate path to a delayed use must be cloned as
    // well.  This deliberately does not cross the existing stop boundary or
    // the original closure; prepareClosure will reject an unauthenticated
    // path instead of letting this discovery pass invent one.
    var needed_index: usize = 0;
    while (needed_index < needed_blocks.items.len) : (needed_index += 1) {
        const block_id = needed_blocks.items[needed_index];
        const target_local_index = analysis.blockIndex(block_id) orelse continue;
        var predecessor_index: usize = 0;
        while (analysis.predecessorAt(block_id, predecessor_index)) |predecessor| : (predecessor_index += 1) {
            const local_index = analysis.blockIndex(predecessor) orelse continue;
            if ((!candidate[local_index] and !containsBlock(continuation.items, predecessor)) or
                needed[local_index]) continue;
            var carries_closure_value = false;

            // An authenticated parameterized handoff is a semantic boundary:
            // the target owns the continuation context and the predecessor is
            // not required merely to keep reverse propagation connected.
            // Crossing it would pull an unrelated producer path into the
            // clone and turn an available incoming value into a non-dominating
            // internal definition.
            if (incoming) |references| {
                if (references.len != 0) {
                    var bridge = false;
                    for (0..analysis.successorCount(predecessor)) |successor_index| {
                        const successor = analysis.successorAt(predecessor, successor_index) orelse continue;
                        if (successor != block_id) continue;
                        bridge = try parameterizedContinuationBridge(
                            allocator,
                            program,
                            analysis,
                            predecessor,
                            successor_index,
                            successor,
                            stop,
                            closure,
                            continuation.items,
                            references,
                            lineage_index,
                            replay_index,
                            replay_cache,
                        );
                        if (trace_structural_phases and closure.len == 1) {
                            traceStructural("delayed_bridge_check source={} target={} result={}\n", .{
                                predecessor.index(),
                                successor.index(),
                                bridge,
                            });
                        }
                        break;
                    }
                    carries_closure_value = edgeArgumentsCarryClosureValue(
                        program,
                        predecessor,
                        block_id,
                        closure,
                    );
                    const direct_use = if (analysis.blockIndex(block_id)) |index|
                        direct_needed[index]
                    else
                        false;
                    if (!carries_closure_value and
                        isAuthenticatedParameterlessForwardingBlock(
                            program,
                            analysis,
                            block_id,
                            closure,
                            lineage_index,
                        ) and
                        (!direct_use or analysis.predecessorCount(block_id) != 1)) continue;
                    if (trace_structural_phases and closure.len == 1) {
                        traceStructural("delayed_reverse source={} target={} bridge={} carries_closure={} direct_target={} source_forwarding={}\n", .{
                            predecessor.index(),
                            block_id.index(),
                            bridge,
                            carries_closure_value,
                            direct_use,
                            isAuthenticatedParameterlessForwardingBlock(
                                program,
                                analysis,
                                predecessor,
                                closure,
                                lineage_index,
                            ),
                        });
                    }
                    if (bridge and !carries_closure_value and
                        !isAuthenticatedParameterlessForwardingBlock(
                            program,
                            analysis,
                            predecessor,
                            closure,
                            lineage_index,
                        ) and !direct_use) continue;
                }
            }
            needed[local_index] = true;
            direct_needed[local_index] = direct_needed[local_index] or
                direct_needed[target_local_index] or
                carries_closure_value;
            try needed_blocks.append(allocator, predecessor);
        }
    }

    for (candidates.items) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse continue;
        if (needed[local_index] and !containsBlock(continuation.items, block_id)) {
            try continuation.append(allocator, block_id);
        }
    }
    if (trace_structural_phases and closure.len >= 20) {
        traceStructural("structural_delayed_retained continuation={}\n", .{continuation.items.len});
    }
}

fn extendContinuationClosureAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    stop: ir.BlockId,
    closure: []ir.BlockId,
    incoming: ?[]const ir.CfgEdgeRef,
) std.mem.Allocator.Error![]ir.BlockId {
    return extendContinuationClosureWithModeAlloc(
        allocator,
        program,
        analysis,
        stop,
        closure,
        incoming,
        .contextual,
    );
}

fn extendClosureForExternalUsesAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    stop: ir.BlockId,
    closure: []ir.BlockId,
    incoming: ?[]const ir.CfgEdgeRef,
) std.mem.Allocator.Error![]ir.BlockId {
    var projected = try extendContinuationClosureWithModeAlloc(
        allocator,
        program,
        analysis,
        stop,
        closure,
        incoming,
        .closure_only,
    );

    // A closure-only pass can add a continuation block whose definitions are
    // then consumed farther downstream.  Re-scan once so ownership discovery
    // reaches that next consumer, but keep the pass bounded; the final
    // projected-boundary and clone-availability checks remain authoritative.
    const rescanned = try extendContinuationClosureWithModeAlloc(
        allocator,
        program,
        analysis,
        stop,
        projected,
        incoming,
        .closure_only,
    );
    if (trace_structural_phases and
        (rescanned.ptr != projected.ptr or rescanned.len != projected.len))
    {
        traceStructural("structural_external_rescan before={} after={} stop={}\n", .{
            projected.len,
            rescanned.len,
            stop.index(),
        });
    }
    projected = rescanned;
    return projected;
}

fn extendContinuationClosureWithModeAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    stop: ir.BlockId,
    closure: []ir.BlockId,
    incoming: ?[]const ir.CfgEdgeRef,
    mode: ContinuationExtensionMode,
) std.mem.Allocator.Error![]ir.BlockId {
    if (closure.len == 0) return closure;
    const function_id = analysis.function.id;

    const index_start = structuralPhaseNow();
    var lineage_index = try CloneLineageIndex.initForFunction(allocator, program, function_id);
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.initForFunction(allocator, program, function_id);
    defer replay_index.deinit();
    var replay_cache = ReplayCache.init(allocator, program, &replay_index);
    defer replay_cache.deinit();
    const index_ms = structuralPhaseMillis(index_start);

    var visited = try allocator.alloc(bool, analysis.function.blocks.len);
    defer allocator.free(visited);
    @memset(visited, false);
    var parameterized_admitted = try allocator.alloc(bool, analysis.function.blocks.len);
    defer allocator.free(parameterized_admitted);
    @memset(parameterized_admitted, false);
    var pending: std.ArrayList(ir.BlockId) = .empty;
    defer pending.deinit(allocator);
    var continuation: std.ArrayList(ir.BlockId) = .empty;
    defer continuation.deinit(allocator);
    var delayed_seeds: std.ArrayList(ir.BlockId) = .empty;
    defer delayed_seeds.deinit(allocator);

    const discovery_start = structuralPhaseNow();
    for (closure) |source_id| {
        if (source_id.index() >= program.blocks.len) continue;
        for (0..analysis.successorCount(source_id)) |successor_index| {
            const target = analysis.successorAt(source_id, successor_index) orelse continue;
            if (target == stop or containsBlock(closure, target) or target.index() >= program.blocks.len) continue;
            const target_block = program.blocks[target.index()];
            const parameterized_bridge = try parameterizedContinuationBridge(
                allocator,
                program,
                analysis,
                source_id,
                successor_index,
                target,
                stop,
                closure,
                continuation.items,
                incoming,
                &lineage_index,
                &replay_index,
                &replay_cache,
            );
            if (target_block.function == function_id) {
                if (try isSharedLoopForwardingBoundary(program, analysis, target) and
                    !terminatorCarriesClosureValue(program, target, closure)) continue;
                const closure_owned_bridge = parameterized_bridge and
                    edgeArgumentsCarryClosureValue(program, source_id, target, closure);
                if (target_block.parameters.len == 0 or (parameterized_bridge and !closure_owned_bridge)) {
                    if (parameterized_bridge) {
                        const target_index = analysis.blockIndex(target) orelse continue;
                        parameterized_admitted[target_index] = true;
                    }
                    try pending.append(allocator, target);
                } else {
                    try delayed_seeds.append(allocator, target);
                }
            }
        }
    }

    while (pending.pop()) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse continue;
        if (visited[local_index] or containsBlock(closure, block_id)) continue;
        if (block_id.index() >= program.blocks.len) continue;
        const block = program.blocks[block_id.index()];
        if (block.function != function_id or
            (block.parameters.len != 0 and
                !(try analysis.canReach(block_id, stop)) and !parameterized_admitted[local_index])) continue;
        visited[local_index] = true;
        try continuation.append(allocator, block_id);
        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) return closure;
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or instruction.block != block.id) return closure;
        }
        for (0..analysis.successorCount(block_id)) |successor_index| {
            const target = analysis.successorAt(block_id, successor_index) orelse continue;
            if (target == stop or containsBlock(closure, target) or target.index() >= program.blocks.len) continue;
            const target_block = program.blocks[target.index()];
            const parameterized_bridge = try parameterizedContinuationBridge(
                allocator,
                program,
                analysis,
                block_id,
                successor_index,
                target,
                stop,
                closure,
                continuation.items,
                incoming,
                &lineage_index,
                &replay_index,
                &replay_cache,
            );
            if (target_block.function == function_id) {
                if (try isSharedLoopForwardingBoundary(program, analysis, target) and
                    !terminatorCarriesClosureValue(program, target, closure)) continue;
                const closure_owned_bridge = parameterized_bridge and
                    edgeArgumentsCarryClosureValue(program, block_id, target, closure);
                if (target_block.parameters.len == 0 or (parameterized_bridge and !closure_owned_bridge)) {
                    if (parameterized_bridge) {
                        const target_index = analysis.blockIndex(target) orelse continue;
                        parameterized_admitted[target_index] = true;
                    }
                    try pending.append(allocator, target);
                } else {
                    try delayed_seeds.append(allocator, target);
                }
            }
        }
    }

    if (trace_structural_phases and closure.len >= 20) {
        traceStructural("structural_delayed_seed_state closure={} seeds={} continuation={}\n", .{
            closure.len,
            delayed_seeds.items.len,
            continuation.items.len,
        });
    }

    try appendDelayedUseContinuationAlloc(
        allocator,
        program,
        analysis,
        stop,
        closure,
        delayed_seeds.items,
        incoming,
        &continuation,
        &lineage_index,
        &replay_index,
        &replay_cache,
    );

    if (trace_structural_phases and closure.len == 1 and incoming != null) {
        traceStructural("structural_continuation_membership stop={} has_4057={} has_4036={} count={}\n", .{
            stop.index(),
            containsBlock(continuation.items, ir.BlockId.fromIndex(4057)),
            containsBlock(continuation.items, ir.BlockId.fromIndex(4036)),
            continuation.items.len,
        });
        traceStructural("structural_continuation_ids {any}\n", .{continuation.items});
        traceStructural("structural_continuation_boundary closure_entry={} incoming={any}\n", .{
            closure[0].index(),
            incoming.?,
        });
    }

    const discovery_ms = structuralPhaseMillis(discovery_start);
    if (continuation.items.len == 0) return closure;

    const needed = try allocator.alloc(bool, analysis.function.blocks.len);
    defer allocator.free(needed);
    @memset(needed, false);
    const direct_needed = try allocator.alloc(bool, analysis.function.blocks.len);
    defer allocator.free(direct_needed);
    @memset(direct_needed, false);
    const references = incoming orelse &.{};
    const context_scan_start = structuralPhaseNow();
    for (continuation.items) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return closure;
        const block = program.blocks[block_id.index()];
        const uses_context = if (mode == .closure_only)
            blockUsesDelayedClosureValue(
                allocator,
                program,
                analysis,
                block,
                closure,
                &lineage_index,
                &replay_index,
                &replay_cache,
            )
        else
            try blockUsesContinuationContext(
                allocator,
                program,
                analysis,
                block,
                block_id,
                closure,
                continuation.items,
                references,
                &lineage_index,
                &replay_index,
                &replay_cache,
                stop,
            );
        if (uses_context) {
            needed[local_index] = true;
            direct_needed[local_index] = true;
            if (trace_structural_phases and closure.len == 1 and incoming != null) {
                traceStructural("structural_continuation_context block={} direct=true witness=continuation\n", .{
                    block_id.index(),
                });
            }
        }
    }
    const context_scan_ms = structuralPhaseMillis(context_scan_start);

    // Retain only paths that carry closure-local or otherwise unauthenticated
    // context. Unrelated siblings must not be cloned just because one path
    // below the same continuation needs a mapping.
    const propagation_start = structuralPhaseNow();
    var changed = true;
    while (changed) {
        changed = false;
        for (continuation.items) |block_id| {
            const local_index = analysis.blockIndex(block_id) orelse return closure;
            if (needed[local_index]) continue;
            for (0..analysis.successorCount(block_id)) |successor_index| {
                const successor = analysis.successorAt(block_id, successor_index) orelse return closure;
                const successor_local_index = analysis.blockIndex(successor) orelse continue;
                if (containsBlock(continuation.items, successor) and needed[successor_local_index]) {
                    const carries_closure_value = edgeArgumentsCarryClosureValue(
                        program,
                        block_id,
                        successor,
                        closure,
                    );
                    const successor_forwarding = isAuthenticatedParameterlessForwardingBlock(
                        program,
                        analysis,
                        successor,
                        closure,
                        &lineage_index,
                    );
                    if (!carries_closure_value and
                        successor_forwarding and
                        (!direct_needed[successor_local_index] or
                            analysis.predecessorCount(successor) != 1)) continue;
                    const bridge = if (references.len != 0)
                        try parameterizedContinuationBridge(
                            allocator,
                            program,
                            analysis,
                            block_id,
                            successor_index,
                            successor,
                            stop,
                            closure,
                            continuation.items,
                            references,
                            &lineage_index,
                            &replay_index,
                            &replay_cache,
                        )
                    else
                        false;
                    const predecessor_forwarding = isAuthenticatedParameterlessForwardingBlock(
                        program,
                        analysis,
                        block_id,
                        closure,
                        &lineage_index,
                    );
                    if (trace_structural_phases and closure.len == 1 and incoming != null) {
                        traceStructural("structural_continuation_reverse source={} target={} bridge={} carries_closure={} successor_forwarding={} predecessor_forwarding={} direct_target={}\n", .{
                            block_id.index(),
                            successor.index(),
                            bridge,
                            carries_closure_value,
                            successor_forwarding,
                            predecessor_forwarding,
                            direct_needed[successor_local_index],
                        });
                    }
                    if (bridge and
                        !carries_closure_value and
                        !predecessor_forwarding and
                        !direct_needed[successor_local_index]) continue;
                    needed[local_index] = true;
                    direct_needed[local_index] = direct_needed[local_index] or
                        direct_needed[successor_local_index] or
                        carries_closure_value;
                    changed = true;
                    break;
                }
            }
        }
    }
    const propagation_ms = structuralPhaseMillis(propagation_start);

    if (trace_structural_phases and closure.len == 1 and incoming != null) {
        for (continuation.items) |block_id| {
            const local_index = analysis.blockIndex(block_id) orelse continue;
            if (needed[local_index]) traceStructural("structural_extension_needed block={}\n", .{block_id.index()});
        }
    }

    var needs_extension = false;
    for (continuation.items) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return closure;
        if (needed[local_index]) {
            needs_extension = true;
            break;
        }
    }
    if (!needs_extension) return closure;
    if (trace_structural_phases and continuation.items.len >= 128) {
        traceStructural("structural_phase continuation function={} stop={} closure={} continuation={} index_ms={} discovery_ms={} context_ms={} propagation_ms={} needed={}\\n", .{
            function_id.index(),
            stop.index(),
            closure.len,
            continuation.items.len,
            index_ms,
            discovery_ms,
            context_scan_ms,
            propagation_ms,
            std.mem.countScalar(bool, needed, true),
        });
    }
    traceStructural("structural_extension stop={d} closure_len={} continuation_len={}\n", .{
        stop.index(),
        closure.len,
        continuation.items.len,
    });
    var expanded: std.ArrayList(ir.BlockId) = .empty;
    errdefer expanded.deinit(allocator);
    try expanded.appendSlice(allocator, closure);
    for (continuation.items) |block_id| {
        const local_index = analysis.blockIndex(block_id) orelse return closure;
        if (needed[local_index]) try expanded.append(allocator, block_id);
    }
    if (trace_structural_phases and closure.len == 1 and incoming != null) {
        const forwarding_index = analysis.blockIndex(ir.BlockId.fromIndex(4057));
        traceStructural("structural_continuation_post_propagation stop={} has_4057={} has_4036={} count={} needed_4057={}\n", .{
            stop.index(),
            containsBlock(continuation.items, ir.BlockId.fromIndex(4057)),
            containsBlock(continuation.items, ir.BlockId.fromIndex(4036)),
            continuation.items.len,
            if (forwarding_index) |index| needed[index] else false,
        });
    }
    var owned = try expanded.toOwnedSlice(allocator);
    allocator.free(closure);
    if (incoming) |incoming_references| {
        if (incoming_references.len != 0) {
            owned = try trimContextIndependentSharedSuffixAlloc(
                allocator,
                program,
                analysis,
                stop,
                owned,
                incoming_references,
            );
        }
    }
    if (owned.len != 0 and cloneStepForTargetCached(program, owned[0], &lineage_index) != null) {
        owned = try trimShadowedUnreachableCloneBlocksAlloc(
            allocator,
            program,
            analysis,
            owned[0],
            owned,
            &lineage_index,
        );
    }

    // Contextual discovery can admit a parameterized producer after the first
    // delayed-use scan.  Re-scan the resulting closure for values that are
    // now clone-local before publishing it; otherwise a shared suffix may
    // retain a terminator or operation that consumes the new clone value.
    // The closure-only mode does not recurse here, so this remains one
    // bounded ownership pass per contextual discovery.
    if (mode == .contextual) {
        return extendClosureForExternalUsesAlloc(
            allocator,
            program,
            analysis,
            stop,
            owned,
            incoming,
        );
    }
    return owned;
}

const Boundary = struct {
    entry: ir.BlockId,
    incoming: []ir.CfgEdgeRef,

    fn deinit(self: *Boundary, allocator: std.mem.Allocator) void {
        allocator.free(self.incoming);
        self.* = undefined;
    }
};

fn collectBoundaryAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    context: []const ir.BlockId,
    common: []const ir.BlockId,
) std.mem.Allocator.Error!?Boundary {
    var entry: ?ir.BlockId = null;
    var incoming: std.ArrayList(ir.CfgEdgeRef) = .empty;
    defer incoming.deinit(allocator);
    for (context) |source| {
        if (containsBlock(common, source) or source.index() >= program.blocks.len) continue;
        switch (program.blocks[source.index()].terminator) {
            .jump => |edge| if (!try appendBoundaryEntry(allocator, &incoming, &entry, source, .jump, edge.target, common)) return null,
            .branch => |branch| {
                if (!try appendBoundaryEntry(
                    allocator,
                    &incoming,
                    &entry,
                    source,
                    .branch_then,
                    branch.then_edge.target,
                    common,
                )) return null;
                if (!try appendBoundaryEntry(
                    allocator,
                    &incoming,
                    &entry,
                    source,
                    .branch_else,
                    branch.else_edge.target,
                    common,
                )) return null;
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        }
    }
    const selected = entry orelse return null;
    if (incoming.items.len == 0) return null;
    return .{ .entry = selected, .incoming = try incoming.toOwnedSlice(allocator) };
}

fn appendBoundaryEntry(
    allocator: std.mem.Allocator,
    incoming: *std.ArrayList(ir.CfgEdgeRef),
    entry: *?ir.BlockId,
    source: ir.BlockId,
    kind: ir.CfgEdgeKind,
    target: ir.BlockId,
    common: []const ir.BlockId,
) std.mem.Allocator.Error!bool {
    if (!containsBlock(common, target)) return true;
    if (entry.*) |existing| {
        if (existing != target) return false;
    } else {
        entry.* = target;
    }
    try incoming.append(allocator, .{ .source = source, .kind = kind, .target = target });
    return true;
}

fn containsBlock(blocks: []const ir.BlockId, target: ir.BlockId) bool {
    for (blocks) |block_id| if (block_id == target) return true;
    return false;
}

pub fn prepareClosure(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
) bool {
    return prepareClosureImpl(allocator, program, analysis, closure, incoming, null, false);
}

/// Prepare a clone closure using replay indexes owned by the caller.  Large
/// normalization transactions already authenticate one immutable function
/// snapshot; rebuilding those indexes for each collision is unnecessary.
pub fn prepareClosureWithReplayContext(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    replay_context: *ReplayProjectionContext,
) bool {
    return prepareClosureImpl(allocator, program, analysis, closure, incoming, replay_context, false);
}

/// Prepare a complete authenticated SCC from the actual cloned entry target.
/// The selected incoming source may remain in the SCC as an internal cycle
/// member, but it is not the entry at which the new clone is reached.
pub fn prepareClosureWithReplayContextFromTargets(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    replay_context: *ReplayProjectionContext,
) bool {
    return prepareClosureImpl(allocator, program, analysis, closure, incoming, replay_context, true);
}

fn tracePrepareClosureReject(reason: []const u8, closure_len: usize, incoming_len: usize) void {
    if (trace_structural_phases) {
        traceStructural("prepare_closure_reject reason={s} closure={} incoming={}\n", .{
            reason,
            closure_len,
            incoming_len,
        });
    }
}

fn prepareClosureImpl(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    replay_context: ?*ReplayProjectionContext,
    root_at_targets: bool,
) bool {
    if (closure.len == 0) return false;
    const external_result = if (replay_context) |context|
        collectExternalCloneMappingsAllocWithReplayState(
            allocator,
            program,
            analysis,
            closure,
            incoming,
            &context.lineage_index,
            &context.replay_index,
            &context.replay_cache,
        ) catch {
            tracePrepareClosureReject("external_mapping_error", closure.len, incoming.len);
            return false;
        }
    else
        collectExternalCloneMappingsAlloc(allocator, program, analysis, closure, incoming) catch {
            tracePrepareClosureReject("external_mapping_error", closure.len, incoming.len);
            return false;
        };
    var external = external_result orelse {
        tracePrepareClosureReject("external_mapping_missing", closure.len, incoming.len);
        return false;
    };
    defer external.deinit();
    if (!closureLocalUsesHaveProjectedBoundary(program, analysis, closure, incoming)) {
        tracePrepareClosureReject("projected_boundary", closure.len, incoming.len);
        return false;
    }
    for (closure) |block_id| {
        if (block_id.index() >= program.blocks.len) return false;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id or !node_split.parametersAreCanonical(program.values, block)) {
            tracePrepareClosureReject("noncanonical_block", closure.len, incoming.len);
            return false;
        }
    }
    const available = if (root_at_targets)
        clone_availability.cloneClosureUsesAreAvailableFromTargets(
            allocator,
            program,
            analysis,
            closure,
            incoming,
            external.values,
            external.clone_values,
            external.packs,
            external.clone_packs,
        ) catch {
            tracePrepareClosureReject("availability_error", closure.len, incoming.len);
            return false;
        }
    else
        clone_availability.cloneClosureUsesAreAvailable(
            allocator,
            program,
            analysis,
            closure,
            incoming,
            external.values,
            external.clone_values,
            external.packs,
            external.clone_packs,
        ) catch {
            tracePrepareClosureReject("availability_error", closure.len, incoming.len);
            return false;
        };
    if (!available) {
        tracePrepareClosureReject("availability", closure.len, incoming.len);
        return false;
    }

    // Irreducible regions can contain a value producer that does not dominate
    // every consumer in the clone closure.  Dominance sorting therefore puts a
    // valid producer after a consumer whose edge carries its value.  Build the
    // clone order from actual instruction/terminator availability instead:
    // each block is admitted only after all values and packs it uses can be
    // remapped from the external context or an already admitted block.
    const ordered = allocator.alloc(ir.BlockId, closure.len) catch return false;
    defer allocator.free(ordered);
    const processed = allocator.alloc(bool, closure.len) catch return false;
    defer allocator.free(processed);
    @memset(processed, false);

    const mapped_values = allocator.alloc(bool, program.values.len) catch return false;
    defer allocator.free(mapped_values);
    const mapped_packs = allocator.alloc(bool, program.value_packs.len) catch return false;
    defer allocator.free(mapped_packs);
    @memset(mapped_values, false);
    @memset(mapped_packs, false);
    for (external.values) |value_id| {
        if (value_id.index() >= mapped_values.len) return false;
        mapped_values[value_id.index()] = true;
    }
    for (external.packs) |pack_id| {
        if (pack_id.index() >= mapped_packs.len) return false;
        mapped_packs[pack_id.index()] = true;
    }
    var candidate_values: std.ArrayList(ir.ValueId) = .empty;
    defer candidate_values.deinit(allocator);
    var candidate_packs: std.ArrayList(ir.ValuePackId) = .empty;
    defer candidate_packs.deinit(allocator);
    var processed_count: usize = 0;
    while (processed_count < closure.len) {
        var selected_index: ?usize = null;
        var selected_order: usize = std.math.maxInt(usize);
        for (closure, 0..) |block_id, closure_index| {
            if (processed[closure_index]) continue;
            const block = program.blocks[block_id.index()];
            if (!node_split.instructionStructureIsCloneableWithMappedFlags(
                program,
                block,
                mapped_values,
                mapped_packs,
            )) continue;

            candidate_values.clearRetainingCapacity();
            candidate_packs.clearRetainingCapacity();
            var valid = true;
            for (block.parameters) |parameter_id| {
                if (parameter_id.index() >= mapped_values.len) {
                    valid = false;
                    break;
                }
                if (!mapped_values[parameter_id.index()]) {
                    mapped_values[parameter_id.index()] = true;
                    candidate_values.append(allocator, parameter_id) catch return false;
                }
            }
            for (block.instructions) |instruction_id| {
                if (!valid) break;
                if (instruction_id.index() >= program.instructions.len) {
                    valid = false;
                    break;
                }
                const instruction = program.instructions[instruction_id.index()];
                if (instruction.id != instruction_id or instruction.block != block.id) {
                    valid = false;
                    break;
                }
                for (instruction.results) |result_id| {
                    if (result_id.index() >= mapped_values.len) {
                        valid = false;
                        break;
                    }
                    if (!mapped_values[result_id.index()]) {
                        mapped_values[result_id.index()] = true;
                        candidate_values.append(allocator, result_id) catch return false;
                    }
                }
                if (instruction.pack_result) |pack_id| {
                    if (pack_id.index() >= mapped_packs.len) {
                        valid = false;
                        break;
                    }
                    if (!mapped_packs[pack_id.index()]) {
                        mapped_packs[pack_id.index()] = true;
                        candidate_packs.append(allocator, pack_id) catch return false;
                    }
                }
            }
            if (!valid or !node_split.terminatorIsCloneableWithMappedFlags(program, block.terminator, mapped_values)) {
                for (candidate_values.items) |value_id| mapped_values[value_id.index()] = false;
                for (candidate_packs.items) |pack_id| mapped_packs[pack_id.index()] = false;
                continue;
            }
            for (candidate_values.items) |value_id| mapped_values[value_id.index()] = false;
            for (candidate_packs.items) |pack_id| mapped_packs[pack_id.index()] = false;
            const order = analysis.blockIndex(block_id) orelse return false;
            if (selected_index == null or order < selected_order) {
                selected_index = closure_index;
                selected_order = order;
            }
        }
        const closure_index = selected_index orelse {
            tracePrepareClosureReject("clone_order", closure.len, incoming.len);
            return false;
        };
        const block_id = closure[closure_index];
        const block = program.blocks[block_id.index()];
        candidate_values.clearRetainingCapacity();
        candidate_packs.clearRetainingCapacity();
        var valid = true;
        for (block.parameters) |parameter_id| {
            if (parameter_id.index() >= mapped_values.len) {
                valid = false;
                break;
            }
            if (!mapped_values[parameter_id.index()]) {
                mapped_values[parameter_id.index()] = true;
                candidate_values.append(allocator, parameter_id) catch return false;
            }
        }
        for (block.instructions) |instruction_id| {
            if (!valid) break;
            if (instruction_id.index() >= program.instructions.len) {
                valid = false;
                break;
            }
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or instruction.block != block.id) {
                valid = false;
                break;
            }
            for (instruction.results) |result_id| {
                if (result_id.index() >= mapped_values.len) {
                    valid = false;
                    break;
                }
                if (!mapped_values[result_id.index()]) {
                    mapped_values[result_id.index()] = true;
                    candidate_values.append(allocator, result_id) catch return false;
                }
            }
            if (instruction.pack_result) |pack_id| {
                if (pack_id.index() >= mapped_packs.len) {
                    valid = false;
                    break;
                }
                if (!mapped_packs[pack_id.index()]) {
                    mapped_packs[pack_id.index()] = true;
                    candidate_packs.append(allocator, pack_id) catch return false;
                }
            }
        }
        if (!valid or !node_split.terminatorIsCloneableWithMappedFlags(program, block.terminator, mapped_values)) {
            for (candidate_values.items) |value_id| mapped_values[value_id.index()] = false;
            for (candidate_packs.items) |pack_id| mapped_packs[pack_id.index()] = false;
            tracePrepareClosureReject("clone_order_invalid", closure.len, incoming.len);
            return false;
        }
        processed[closure_index] = true;
        ordered[processed_count] = block_id;
        processed_count += 1;
    }
    @memcpy(closure, ordered);
    return true;
}

fn forwardDistance(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    start: ir.BlockId,
    target: ir.BlockId,
    blocked: ?ir.BlockId,
    allowed: ?[]const bool,
) std.mem.Allocator.Error!?u32 {
    const target_index = analysis.blockIndex(target) orelse return null;
    const distances = try forwardDistancesAlloc(allocator, analysis, start, blocked, allowed) orelse return null;
    defer allocator.free(distances);
    const distance = distances[target_index];
    return if (distance == std.math.maxInt(u32)) null else distance;
}

fn distanceAt(analysis: *const cfg.Analysis, distances: []const u32, target: ir.BlockId) ?u32 {
    const target_index = analysis.blockIndex(target) orelse return null;
    if (target_index >= distances.len) return null;
    const distance = distances[target_index];
    return if (distance == std.math.maxInt(u32)) null else distance;
}

fn forwardDistancesAlloc(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    start: ir.BlockId,
    blocked: ?ir.BlockId,
    allowed: ?[]const bool,
) std.mem.Allocator.Error!?[]u32 {
    const block_count = analysis.function.blocks.len;
    if (allowed) |membership| if (membership.len != block_count) return null;
    const start_index = analysis.blockIndex(start) orelse return null;
    const blocked_index = if (blocked) |blocked_id| analysis.blockIndex(blocked_id) orelse return null else null;
    if (!analysis.isReachable(start) or blocked_index == start_index) return null;
    if (allowed) |membership| if (!membership[start_index]) return null;

    const distances = try allocator.alloc(u32, block_count);
    errdefer allocator.free(distances);
    @memset(distances, std.math.maxInt(u32));
    const pending = try allocator.alloc(ir.BlockId, block_count);
    defer allocator.free(pending);
    distances[start_index] = 0;
    pending[0] = start;
    var cursor: usize = 0;
    var pending_len: usize = 1;
    while (cursor < pending_len) : (cursor += 1) {
        const current = pending[cursor];
        const current_index = analysis.blockIndex(current) orelse return null;
        for (0..analysis.successorCount(current)) |successor_index| {
            const successor = analysis.successorAt(current, successor_index) orelse return null;
            const local_index = analysis.blockIndex(successor) orelse return null;
            if (blocked_index == local_index) continue;
            if (allowed) |membership| if (!membership[local_index]) continue;
            if (distances[local_index] != std.math.maxInt(u32)) continue;
            distances[local_index] = distances[current_index] + 1;
            pending[pending_len] = successor;
            pending_len += 1;
        }
    }
    return distances;
}

test "one-parameter clone member authenticates its live edge tuple" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const source_successor = ir.BlockId.fromIndex(2);
    const incoming_source = ir.BlockId.fromIndex(3);
    const clone = ir.BlockId.fromIndex(4);
    const clone_successor = ir.BlockId.fromIndex(5);
    const selector = ir.ValueId.fromIndex(0);
    const seed = ir.ValueId.fromIndex(1);
    const alternate = ir.ValueId.fromIndex(2);
    const source_parameter = ir.ValueId.fromIndex(3);
    const clone_parameter = ir.ValueId.fromIndex(4);
    const source_result = ir.ValueId.fromIndex(5);
    const clone_result = ir.ValueId.fromIndex(6);
    const source_instruction = ir.InstructionId.fromIndex(0);
    const clone_instruction = ir.InstructionId.fromIndex(1);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const source_parameters = [_]ir.ValueId{source_parameter};
    const clone_parameters = [_]ir.ValueId{clone_parameter};
    const expected = [_]ir.ValueId{seed};

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = source, .arguments = expected[0..] },
            .else_edge = .{ .target = incoming_source },
        } } },
        .{ .id = source, .function = function_id, .parameters = source_parameters[0..], .instructions = &.{source_instruction}, .terminator = .{ .jump = .{ .target = source_successor } } },
        .{ .id = source_successor, .function = function_id, .terminator = .{ .return_values = &.{} } },
        .{ .id = incoming_source, .function = function_id, .terminator = .{ .jump = .{
            .target = clone,
            .arguments = expected[0..],
        } } },
        .{ .id = clone, .function = function_id, .parameters = clone_parameters[0..], .instructions = &.{clone_instruction}, .terminator = .{ .jump = .{ .target = clone_successor } } },
        .{ .id = clone_successor, .function = function_id, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ selector, seed, alternate },
        .blocks = &.{ entry, source, source_successor, incoming_source, clone, clone_successor },
        .entry_block = entry,
    }};
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = seed, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = alternate, .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = source_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = source, .index = 0 } } },
        .{ .id = clone_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 0 } } },
        .{ .id = source_result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = source_instruction, .index = 0 } } },
        .{ .id = clone_result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = clone_instruction, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = source_instruction, .block = source, .operation = .{ .environment_get = .{
            .target = .{ .ambient = {} },
            .name = "shared",
        } }, .results = &.{source_result}, .effects = ir.EffectSummary.semantic_environment_read },
        .{ .id = clone_instruction, .block = clone, .operation = .{ .environment_get = .{
            .target = .{ .ambient = {} },
            .name = "shared",
        } }, .results = &.{clone_result}, .effects = ir.EffectSummary.semantic_environment_read },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = incoming_source,
            .kind = .jump,
            .from = .{ .target = source, .arguments = expected[0..] },
            .to = .{ .target = clone, .arguments = expected[0..] },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = clone,
            .kind = .jump,
            .from = .{ .target = source_successor },
            .to = .{ .target = clone_successor },
            .rule = .node_split,
            .node_split_group = group,
        },
    };
    var program: ir.Program = .{
        .program_id = "one-parameter-clone-member",
        .entry_function = function_id,
        .functions = &.{functions[0]},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .edge_rewrites = &rewrites,
    };
    const incoming = ir.CfgEdgeRef{ .source = incoming_source, .kind = .jump, .target = clone };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, functions[0]);
    defer analysis.deinit();
    var replay = try ReplayProjectionContext.initForFunction(std.testing.allocator, &program, function_id);
    defer replay.deinit();
    try std.testing.expect(try replay.hasAuthenticatedOneParameterContinuationForEdge(
        &analysis,
        incoming,
        expected[0..],
    ));

    // A source-side successor can become unreachable after an earlier
    // authenticated split while the live clone-side successor remains the
    // continuation being validated.
    var dead_source_blocks = blocks;
    dead_source_blocks[entry.index()].terminator = .{ .jump = .{ .target = incoming_source } };
    var dead_source_program = program;
    dead_source_program.blocks = &dead_source_blocks;
    var dead_source_analysis = try cfg.Analysis.init(
        std.testing.allocator,
        &dead_source_program,
        functions[0],
    );
    defer dead_source_analysis.deinit();
    try std.testing.expect(!dead_source_analysis.isReachable(source_successor));
    var dead_source_replay = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &dead_source_program,
        function_id,
    );
    defer dead_source_replay.deinit();
    try std.testing.expect(try dead_source_replay.hasAuthenticatedOneParameterContinuationForEdge(
        &dead_source_analysis,
        incoming,
        expected[0..],
    ));

    var tampered_blocks = blocks;
    tampered_blocks[incoming_source.index()].terminator = .{ .jump = .{
        .target = clone,
        .arguments = &.{alternate},
    } };
    var tampered_program = program;
    tampered_program.blocks = &tampered_blocks;
    var tampered_analysis = try cfg.Analysis.init(std.testing.allocator, &tampered_program, functions[0]);
    defer tampered_analysis.deinit();
    var tampered_replay = try ReplayProjectionContext.initForFunction(
        std.testing.allocator,
        &tampered_program,
        function_id,
    );
    defer tampered_replay.deinit();
    try std.testing.expect(!try tampered_replay.hasAuthenticatedOneParameterContinuationForEdge(
        &tampered_analysis,
        incoming,
        expected[0..],
    ));
}

test "blocked sibling ingress does not hide authenticated external consumer" {
    const function_id = ir.FunctionId.fromIndex(0);
    const root = ir.BlockId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(1);
    const blocked_parent = ir.BlockId.fromIndex(2);
    const blocked_ingress = ir.BlockId.fromIndex(3);
    const consumer_source = ir.BlockId.fromIndex(4);
    const consumer = ir.BlockId.fromIndex(5);
    const original_entry = ir.BlockId.fromIndex(6);
    const original_blocked = ir.BlockId.fromIndex(7);
    const original_consumer_source = ir.BlockId.fromIndex(8);
    const original_consumer = ir.BlockId.fromIndex(9);
    const selector = ir.ValueId.fromIndex(0);
    const produced = ir.ValueId.fromIndex(1);
    const copy_instruction = ir.InstructionId.fromIndex(0);
    const group = ir.NodeSplitGroupId.fromIndex(0);

    const blocks = [_]ir.Block{
        .{ .id = root, .function = function_id, .terminator = .{ .jump = .{ .target = entry } } },
        .{ .id = entry, .function = function_id, .instructions = &.{copy_instruction}, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = blocked_parent },
            .else_edge = .{ .target = consumer_source },
        } } },
        .{ .id = blocked_parent, .function = function_id, .terminator = .{ .jump = .{ .target = blocked_ingress } } },
        .{ .id = blocked_ingress, .function = function_id, .terminator = .{ .jump = .{ .target = entry } } },
        .{ .id = consumer_source, .function = function_id, .terminator = .{ .jump = .{ .target = consumer } } },
        .{ .id = consumer, .function = function_id, .terminator = .{ .return_values = &.{produced} } },
        .{ .id = original_entry, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original_blocked, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original_consumer_source, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original_consumer, .function = function_id, .terminator = .{ .unreachable_block = {} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ root, entry, blocked_parent, blocked_ingress, consumer_source, consumer, original_entry, original_blocked, original_consumer_source, original_consumer },
        .entry_block = root,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = produced, .function = function_id, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = copy_instruction, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = copy_instruction,
        .block = entry,
        .operation = .{ .copy = selector },
        .results = &.{produced},
        .effects = .pure,
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{ .id = ir.EdgeRewriteId.fromIndex(0), .source = entry, .kind = .jump, .from = .{ .target = original_entry }, .to = .{ .target = entry }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(1), .source = blocked_ingress, .kind = .jump, .from = .{ .target = original_blocked }, .to = .{ .target = blocked_ingress }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(2), .source = consumer_source, .kind = .jump, .from = .{ .target = original_consumer_source }, .to = .{ .target = consumer_source }, .rule = .node_split, .node_split_group = group },
        .{ .id = ir.EdgeRewriteId.fromIndex(3), .source = consumer, .kind = .jump, .from = .{ .target = original_consumer }, .to = .{ .target = consumer }, .rule = .node_split, .node_split_group = group },
    };
    const program = ir.Program{
        .program_id = "blocked-sibling-external-consumer",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .edge_rewrites = &rewrites,
    };

    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    var lineage_index = try CloneLineageIndex.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer lineage_index.deinit();
    var replay_index = try node_split.ReplayIndex.initForFunction(
        std.testing.allocator,
        &program,
        function_id,
    );
    defer replay_index.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{
        .source = root,
        .kind = .jump,
        .target = entry,
    }};
    const initial = try std.testing.allocator.dupe(ir.BlockId, &.{entry});
    const expanded = try extendAuthenticatedGroupBoundaryContextAlloc(
        std.testing.allocator,
        &program,
        &analysis,
        initial,
        &incoming,
        &lineage_index,
        &replay_index,
    );
    defer std.testing.allocator.free(expanded);
    try std.testing.expectEqual(@as(usize, 3), expanded.len);
    try std.testing.expect(containsBlock(expanded, entry));
    try std.testing.expect(containsBlock(expanded, consumer_source));
    try std.testing.expect(containsBlock(expanded, consumer));
    try std.testing.expect(!containsBlock(expanded, blocked_ingress));
    try std.testing.expect(closureLocalUsesHaveProjectedBoundary(
        &program,
        &analysis,
        expanded,
        &incoming,
    ));
}
