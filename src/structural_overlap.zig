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

const IterationTransitionResult = struct {
    instruction: ir.Instruction,
    block: ir.BlockId,
    index: usize,
};

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

const ContextualMapping = struct {
    value: ?ir.ValueId = null,
    pack: ?ir.ValuePackId = null,
    ambiguous: bool = false,
};

const ContinuationValueContext = enum {
    available,
    contextual,
    unavailable,
};
