const std = @import("std");
const ir = @import("ir.zig");
const node_split_instruction = @import("node_split_instruction.zig");
const runtime_uses = @import("runtime_uses.zig");
const edge_path = @import("edge_path.zig");

pub const CloneError = error{InvalidNodeSplitSource} || std.mem.Allocator.Error;

pub const CloneResult = struct {
    block: ir.Block,
    cloned_values: usize,
    cloned_packs: usize,
    cloned_instructions: usize,
};

pub fn cloneBlockInArena(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    instructions: *std.ArrayList(ir.Instruction),
    values: *std.ArrayList(ir.Value),
    packs: *std.ArrayList(ir.ValuePack),
    source: ir.Block,
    clone_id: ir.BlockId,
) CloneError!CloneResult {
    return cloneBlockWithMappingsInArena(
        allocator,
        program,
        instructions,
        values,
        packs,
        source,
        clone_id,
        &.{},
        &.{},
        &.{},
        &.{},
    );
}

pub fn cloneBlockWithMappingsInArena(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    instructions: *std.ArrayList(ir.Instruction),
    values: *std.ArrayList(ir.Value),
    packs: *std.ArrayList(ir.ValuePack),
    source: ir.Block,
    clone_id: ir.BlockId,
    external_source_values: []const ir.ValueId,
    external_clone_values: []const ir.ValueId,
    external_source_packs: []const ir.ValuePackId,
    external_clone_packs: []const ir.ValuePackId,
) CloneError!CloneResult {
    if (source.id == clone_id or
        external_source_values.len != external_clone_values.len or
        external_source_packs.len != external_clone_packs.len or
        !parametersAreCanonical(program.values, source) or
        !node_split_instruction.sequenceIsCloneableWithMappings(
            program,
            source,
            external_source_values,
            external_source_packs,
        )) return error.InvalidNodeSplitSource;

    const local_value_capacity = mappedValueCapacity(program, source) orelse return error.InvalidNodeSplitSource;
    const mapped_capacity = std.math.add(usize, external_source_values.len, local_value_capacity) catch
        return error.InvalidNodeSplitSource;
    const source_values = try allocator.alloc(ir.ValueId, mapped_capacity);
    defer allocator.free(source_values);
    const clone_values = try allocator.alloc(ir.ValueId, mapped_capacity);
    defer allocator.free(clone_values);
    @memcpy(source_values[0..external_source_values.len], external_source_values);
    @memcpy(clone_values[0..external_clone_values.len], external_clone_values);
    const local_pack_capacity = mappedPackCapacity(program, source) orelse return error.InvalidNodeSplitSource;
    const mapped_pack_capacity = std.math.add(usize, external_source_packs.len, local_pack_capacity) catch
        return error.InvalidNodeSplitSource;
    const source_packs = try allocator.alloc(ir.ValuePackId, mapped_pack_capacity);
    defer allocator.free(source_packs);
    const clone_packs = try allocator.alloc(ir.ValuePackId, mapped_pack_capacity);
    defer allocator.free(clone_packs);
    @memcpy(source_packs[0..external_source_packs.len], external_source_packs);
    @memcpy(clone_packs[0..external_clone_packs.len], external_clone_packs);
    const clone_instruction_ids = try allocator.alloc(ir.InstructionId, source.instructions.len);
    try values.ensureUnusedCapacity(allocator, local_value_capacity);
    try packs.ensureUnusedCapacity(allocator, local_pack_capacity);
    try instructions.ensureUnusedCapacity(allocator, source.instructions.len);

    const clone_parameters = try allocator.alloc(ir.ValueId, source.parameters.len);
    var mapped_count: usize = external_source_values.len;
    var mapped_pack_count: usize = external_source_packs.len;
    for (source.parameters, 0..) |parameter_id, parameter_index| {
        var value = values.items[parameter_id.index()];
        value.id = ir.ValueId.fromIndex(values.items.len);
        value.origin = .{ .block_parameter = .{ .block = clone_id, .index = @intCast(parameter_index) } };
        clone_parameters[parameter_index] = value.id;
        source_values[mapped_count] = parameter_id;
        clone_values[mapped_count] = value.id;
        mapped_count += 1;
        try values.append(allocator, value);
    }

    // Capacity growth above can relocate these three backing arrays. Keep the
    // Program view passed to remapping synchronized with the mutable lists;
    // remapOperation consults both the explicit value slice and Program-owned
    // value, pack, and instruction slices when deciding whether references
    // outside the cloned closure are safe to retain.
    var remap_program = program.*;
    for (source.instructions, 0..) |source_instruction_id, instruction_index| {
        remap_program.values = values.items;
        remap_program.value_packs = packs.items;
        remap_program.instructions = instructions.items;
        const source_instruction = instructions.items[source_instruction_id.index()];
        const clone_instruction_id = ir.InstructionId.fromIndex(instructions.items.len);
        const operation = (try node_split_instruction.remapOperation(
            allocator,
            &remap_program,
            values.items,
            source.function,
            source_instruction.operation,
            source_values[0..mapped_count],
            clone_values[0..mapped_count],
            source_packs[0..mapped_pack_count],
            clone_packs[0..mapped_pack_count],
        )) orelse return error.InvalidNodeSplitSource;
        const clone_results = try allocator.alloc(ir.ValueId, source_instruction.results.len);
        var cloned_instruction = source_instruction;
        cloned_instruction.id = clone_instruction_id;
        cloned_instruction.block = clone_id;
        cloned_instruction.operation = operation;
        cloned_instruction.results = clone_results;
        clone_instruction_ids[instruction_index] = clone_instruction_id;

        for (source_instruction.results, 0..) |source_result_id, result_index| {
            var result_value = values.items[source_result_id.index()];
            result_value.id = ir.ValueId.fromIndex(values.items.len);
            result_value.origin = .{ .instruction_result = .{
                .instruction = clone_instruction_id,
                .index = @intCast(result_index),
            } };
            clone_results[result_index] = result_value.id;
            source_values[mapped_count] = source_result_id;
            clone_values[mapped_count] = result_value.id;
            mapped_count += 1;
            try values.append(allocator, result_value);
        }
        if (source_instruction.pack_result) |source_pack_id| {
            if (source_pack_id.index() >= packs.items.len) return error.InvalidNodeSplitSource;
            var pack = packs.items[source_pack_id.index()];
            if (pack.id != source_pack_id or pack.function != source.function) return error.InvalidNodeSplitSource;
            const producer = switch (pack.origin) {
                .instruction_result => |instruction_id| instruction_id,
                .varargs => return error.InvalidNodeSplitSource,
            };
            if (producer != source_instruction_id) return error.InvalidNodeSplitSource;
            pack.id = ir.ValuePackId.fromIndex(packs.items.len);
            pack.origin = .{ .instruction_result = clone_instruction_id };
            cloned_instruction.pack_result = pack.id;
            source_packs[mapped_pack_count] = source_pack_id;
            clone_packs[mapped_pack_count] = pack.id;
            mapped_pack_count += 1;
            try packs.append(allocator, pack);
        }
        try instructions.append(allocator, cloned_instruction);
    }

    var clone = source;
    clone.id = clone_id;
    clone.parameters = clone_parameters;
    clone.instructions = clone_instruction_ids;
    clone.terminator = try remapTerminatorAlloc(
        allocator,
        source.terminator,
        source.id,
        clone_id,
        source_values[0..mapped_count],
        clone_values[0..mapped_count],
    );
    return .{
        .block = clone,
        .cloned_values = mapped_count - external_source_values.len,
        .cloned_packs = mapped_pack_count - external_source_packs.len,
        .cloned_instructions = clone_instruction_ids.len,
    };
}

pub fn parametersAreCanonical(values: []const ir.Value, source: ir.Block) bool {
    for (source.parameters, 0..) |parameter_id, parameter_index| {
        if (parameter_id.index() >= values.len) return false;
        const value = values[parameter_id.index()];
        if (value.id != parameter_id or value.function != source.function) return false;
        const origin = switch (value.origin) {
            .block_parameter => |origin| origin,
            else => return false,
        };
        if (origin.block != source.id or origin.index != parameter_index) return false;
    }
    return true;
}

pub fn blockUsesMappedValues(
    program: *const ir.Program,
    block: ir.Block,
    mapped_values: []const ir.ValueId,
    mapped_packs: []const ir.ValuePackId,
) bool {
    const instructions_with_mappings = instructionStructureIsCloneableWithMappings(
        program,
        block,
        mapped_values,
        mapped_packs,
    );
    const instructions_without_mappings = instructionStructureIsCloneableWithMappings(
        program,
        block,
        &.{},
        &.{},
    );
    if (instructions_with_mappings and !instructions_without_mappings) return true;

    const terminator_with_mappings = terminatorIsCloneableWithMappings(program, block.terminator, mapped_values);
    const terminator_without_mappings = terminatorIsCloneableWithMappings(program, block.terminator, &.{});
    return terminator_with_mappings and !terminator_without_mappings;
}

pub fn terminatorIsCloneableWithMappings(
    program: *const ir.Program,
    terminator: ir.Terminator,
    mapped_values: []const ir.ValueId,
) bool {
    const valueIsCloneable = struct {
        fn check(program_value: *const ir.Program, value_id: ir.ValueId, mappings: []const ir.ValueId) bool {
            if (value_id.index() >= program_value.values.len) return false;
            for (mappings) |mapped| if (mapped == value_id) return true;
            return switch (program_value.values[value_id.index()].origin) {
                .parameter, .capture => true,
                .block_parameter, .instruction_result => false,
            };
        }

        fn checkMany(program_value: *const ir.Program, values: []const ir.ValueId, mappings: []const ir.ValueId) bool {
            for (values) |value_id| if (!check(program_value, value_id, mappings)) return false;
            return true;
        }
    };

    return switch (terminator) {
        .jump => |edge| valueIsCloneable.checkMany(program, edge.arguments, mapped_values),
        .branch => |branch| valueIsCloneable.check(program, branch.condition, mapped_values) and
            valueIsCloneable.checkMany(program, branch.then_edge.arguments, mapped_values) and
            valueIsCloneable.checkMany(program, branch.else_edge.arguments, mapped_values),
        .return_values => |values| valueIsCloneable.checkMany(program, values, mapped_values),
        .return_pack => true,
        .return_expanded => |expanded| valueIsCloneable.checkMany(program, expanded.values, mapped_values),
        .throw_error => |throw_error| valueIsCloneable.check(program, throw_error.value, mapped_values) and
            (throw_error.dynamic_level == null or valueIsCloneable.check(program, throw_error.dynamic_level.?, mapped_values)),
        .unreachable_block => true,
    };
}

pub fn terminatorIsCloneableWithMappedFlags(
    program: *const ir.Program,
    terminator: ir.Terminator,
    mapped_values: []const bool,
) bool {
    const valueIsCloneable = struct {
        fn check(program_value: *const ir.Program, value_id: ir.ValueId, mappings: []const bool) bool {
            if (value_id.index() >= program_value.values.len or value_id.index() >= mappings.len) return false;
            if (mappings[value_id.index()]) return true;
            return switch (program_value.values[value_id.index()].origin) {
                .parameter, .capture => true,
                .block_parameter, .instruction_result => false,
            };
        }

        fn checkMany(program_value: *const ir.Program, values: []const ir.ValueId, mappings: []const bool) bool {
            for (values) |value_id| if (!check(program_value, value_id, mappings)) return false;
            return true;
        }
    };

    return switch (terminator) {
        .jump => |edge| valueIsCloneable.checkMany(program, edge.arguments, mapped_values),
        .branch => |branch| valueIsCloneable.check(program, branch.condition, mapped_values) and
            valueIsCloneable.checkMany(program, branch.then_edge.arguments, mapped_values) and
            valueIsCloneable.checkMany(program, branch.else_edge.arguments, mapped_values),
        .return_values => |values| valueIsCloneable.checkMany(program, values, mapped_values),
        .return_pack => true,
        .return_expanded => |expanded| valueIsCloneable.checkMany(program, expanded.values, mapped_values),
        .throw_error => |throw_error| valueIsCloneable.check(program, throw_error.value, mapped_values) and
            (throw_error.dynamic_level == null or valueIsCloneable.check(program, throw_error.dynamic_level.?, mapped_values)),
        .unreachable_block => true,
    };
}

pub fn instructionsAreCloneable(program: *const ir.Program, source: ir.Block) bool {
    return instructionStructureIsCloneable(program, source);
}

pub fn instructionStructureIsCloneable(program: *const ir.Program, source: ir.Block) bool {
    return node_split_instruction.sequenceIsCloneable(program, source);
}

pub fn instructionStructureIsCloneableWithMappings(
    program: *const ir.Program,
    source: ir.Block,
    mapped_values: []const ir.ValueId,
    mapped_packs: []const ir.ValuePackId,
) bool {
    return node_split_instruction.sequenceIsCloneableWithMappings(program, source, mapped_values, mapped_packs);
}

pub fn instructionStructureIsCloneableWithMappedFlags(
    program: *const ir.Program,
    source: ir.Block,
    mapped_values: []const bool,
    mapped_packs: []const bool,
) bool {
    return node_split_instruction.sequenceIsCloneableWithMappedFlags(program, source, mapped_values, mapped_packs);
}

/// Replay an ungrouped or implicitly grouped split using precomputed rewrite
/// metadata.  This preserves replayAlloc's group-selection semantics while
/// avoiding a full history scan for every candidate rewrite.
pub fn replayAllocWithIndex(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    incoming: ir.Edge,
    clone_id: ir.BlockId,
    index: *const ReplayIndex,
) std.mem.Allocator.Error!?ir.Edge {
    var selected_group: ?ir.NodeSplitGroupId = null;
    var found_mapping = false;
    for (index.nodeSplitRewriteIndices()) |rewrite_index| {
        const rewrite = program.edge_rewrites[rewrite_index];
        if (rewrite.from.target != incoming.target or rewrite.to.target != clone_id) continue;
        if (found_mapping and rewrite.node_split_group != selected_group) return null;
        selected_group = rewrite.node_split_group;
        found_mapping = true;
    }
    return replayAllocWithGroup(allocator, program, incoming, clone_id, selected_group, index);
}

fn replayAllocWithGroup(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    incoming: ir.Edge,
    clone_id: ir.BlockId,
    group: ?ir.NodeSplitGroupId,
    replay_index: ?*const ReplayIndex,
) std.mem.Allocator.Error!?ir.Edge {
    if (incoming.target.index() >= program.blocks.len or clone_id.index() >= program.blocks.len) return null;
    const source = program.blocks[incoming.target.index()];
    const clone = program.blocks[clone_id.index()];
    var mappings = try replayMappingsAlloc(allocator, program, source.id, clone.id, group, replay_index) orelse return null;
    defer mappings.deinit();
    if (source.id != incoming.target or clone.id != clone_id or source.id == clone.id or
        source.function != clone.function or incoming.arguments.len != source.parameters.len or
        !std.mem.eql(ir.EvidenceId, source.evidence, clone.evidence) or
        !sameOptionalString(source.name_hint, clone.name_hint))
    {
        return null;
    }
    if (!try sameMappedBlockAlloc(allocator, program, source, clone, mappings)) return null;

    if (incoming.arguments.len == 0) return .{ .target = clone_id };
    return .{ .target = clone_id, .arguments = try allocator.dupe(ir.ValueId, incoming.arguments) };
}

pub const ReplayMappings = struct {
    allocator: std.mem.Allocator,
    source_values: []ir.ValueId,
    clone_values: []ir.ValueId,
    source_packs: []ir.ValuePackId,
    clone_packs: []ir.ValuePackId,
    history_start: ?usize,

    pub fn deinit(self: *ReplayMappings) void {
        self.allocator.free(self.source_values);
        self.allocator.free(self.clone_values);
        self.allocator.free(self.source_packs);
        self.allocator.free(self.clone_packs);
        self.* = undefined;
    }
};

const ReplayGroupRange = struct {
    group: ir.NodeSplitGroupId,
    start: usize,
    end: usize,
};

const ReplayCandidateRange = struct {
    start: usize,
    end: usize,
};

const ReplayGroupBlockKey = struct {
    group: ?ir.NodeSplitGroupId,
    block: ir.BlockId,
};

const ReplayGroupBlockRange = struct {
    key: ReplayGroupBlockKey,
    start: usize,
    end: usize,
};

/// Immutable rewrite metadata shared by external clone-mapping transactions.
/// The legacy replay API still builds this state locally; callers that inspect
/// several candidate clones can amortize the rewrite-history scan.
pub const ReplayIndex = struct {
    allocator: std.mem.Allocator,
    clone_sources: []?ir.BlockId,
    clone_depths: []?usize,
    node_split_indices: []usize,
    candidate_clone_targets: []ir.BlockId,
    candidate_ranges: []ReplayCandidateRange,
    candidate_descendants: []ir.BlockId,
    authenticated_clone_blocks: []bool,
    group_ranges: []ReplayGroupRange,
    group_rewrite_indices: []usize,
    group_lookup: std.AutoHashMapUnmanaged(ir.NodeSplitGroupId, usize),
    group_block_ranges: []ReplayGroupBlockRange,
    group_block_rewrite_indices: []usize,
    group_block_lookup: std.AutoHashMapUnmanaged(ReplayGroupBlockKey, usize),
    valid: bool,
    function_id: ?ir.FunctionId = null,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program) std.mem.Allocator.Error!ReplayIndex {
        return initWithFunction(allocator, program, null);
    }

    /// Build replay metadata for one function's authenticated rewrite history.
    /// Clone block ids are globally allocated, but their provenance is owned by
    /// the function containing the source and clone blocks.  Keeping unrelated
    /// function history out of a projection avoids treating a foreign clone as
    /// evidence while preserving the complete history for the selected owner.
    pub fn initForFunction(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        function_id: ir.FunctionId,
    ) std.mem.Allocator.Error!ReplayIndex {
        return initWithFunction(allocator, program, function_id);
    }

    fn initWithFunction(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        function_id: ?ir.FunctionId,
    ) std.mem.Allocator.Error!ReplayIndex {
        const clone_sources = try allocator.alloc(?ir.BlockId, program.blocks.len);
        errdefer allocator.free(clone_sources);
        @memset(clone_sources, null);
        const clone_depths = try allocator.alloc(?usize, program.blocks.len);
        errdefer allocator.free(clone_depths);
        @memset(clone_depths, null);
        const authenticated_clone_blocks = try allocator.alloc(bool, program.blocks.len);
        errdefer allocator.free(authenticated_clone_blocks);
        @memset(authenticated_clone_blocks, false);

        var node_split_indices: std.ArrayList(usize) = .empty;
        defer node_split_indices.deinit(allocator);
        var candidate_clone_targets: std.ArrayList(ir.BlockId) = .empty;
        defer candidate_clone_targets.deinit(allocator);
        var candidate_seen: std.AutoHashMapUnmanaged(ir.BlockId, void) = .empty;
        defer candidate_seen.deinit(allocator);
        var group_ranges: std.ArrayList(ReplayGroupRange) = .empty;
        defer group_ranges.deinit(allocator);
        var group_lookup: std.AutoHashMapUnmanaged(ir.NodeSplitGroupId, usize) = .empty;
        errdefer group_lookup.deinit(allocator);
        var group_block_ranges: std.ArrayList(ReplayGroupBlockRange) = .empty;
        defer group_block_ranges.deinit(allocator);
        var group_block_lookup: std.AutoHashMapUnmanaged(ReplayGroupBlockKey, usize) = .empty;
        errdefer group_block_lookup.deinit(allocator);
        var valid = true;

        for (program.edge_rewrites, 0..) |rewrite, rewrite_index| {
            if (rewrite.rule != .node_split) continue;
            if (function_id) |selected_function| {
                if (!rewriteBelongsToFunction(program, rewrite, selected_function)) continue;
            }
            try node_split_indices.append(allocator, rewrite_index);
            if (rewrite.node_split_group != null and rewrite.to.target.index() < program.blocks.len) {
                authenticated_clone_blocks[rewrite.to.target.index()] = true;
            }
            if (rewrite.to.target.index() < program.blocks.len) {
                const candidate_entry = try candidate_seen.getOrPut(allocator, rewrite.to.target);
                if (!candidate_entry.found_existing) try candidate_clone_targets.append(allocator, rewrite.to.target);
            }
            if (rewrite.node_split_group) |group| {
                const group_entry = try group_lookup.getOrPut(allocator, group);
                if (!group_entry.found_existing) {
                    group_entry.value_ptr.* = group_ranges.items.len;
                    try group_ranges.append(allocator, .{ .group = group, .start = 0, .end = 0 });
                }
                const group_index = group_entry.value_ptr.*;
                group_ranges.items[group_index].end = std.math.add(
                    usize,
                    group_ranges.items[group_index].end,
                    1,
                ) catch return error.OutOfMemory;
            }
            for ([_]ReplayGroupBlockKey{
                .{ .group = rewrite.node_split_group, .block = rewrite.from.target },
                .{ .group = rewrite.node_split_group, .block = rewrite.to.target },
            }) |key| {
                const entry = try group_block_lookup.getOrPut(allocator, key);
                if (!entry.found_existing) {
                    entry.value_ptr.* = group_block_ranges.items.len;
                    try group_block_ranges.append(allocator, .{ .key = key, .start = 0, .end = 0 });
                }
                const range_index = entry.value_ptr.*;
                group_block_ranges.items[range_index].end = std.math.add(
                    usize,
                    group_block_ranges.items[range_index].end,
                    1,
                ) catch return error.OutOfMemory;
            }

            // Preserve replayMappingsAlloc's history policy: malformed
            // references are skipped, while conflicting valid clone parents
            // make the complete replay index unusable.
            if (rewrite.to.target == rewrite.from.target or
                rewrite.to.target.index() >= program.blocks.len or
                rewrite.from.target.index() >= program.blocks.len)
            {
                continue;
            }
            if (clone_sources[rewrite.to.target.index()]) |existing| {
                if (existing != rewrite.from.target) valid = false;
            } else {
                clone_sources[rewrite.to.target.index()] = rewrite.from.target;
            }
        }

        if (!try populateNodeSplitDepths(allocator, clone_sources, clone_depths)) valid = false;

        var group_offset: usize = 0;
        for (group_ranges.items) |*range| {
            const count = range.end;
            range.start = group_offset;
            range.end = std.math.add(usize, group_offset, count) catch return error.OutOfMemory;
            group_offset = range.end;
        }
        const group_rewrite_indices = try allocator.alloc(usize, group_offset);
        errdefer allocator.free(group_rewrite_indices);
        var group_positions = try allocator.alloc(usize, group_ranges.items.len);
        defer allocator.free(group_positions);
        for (group_ranges.items, 0..) |range, group_index| group_positions[group_index] = range.start;
        for (node_split_indices.items) |rewrite_index| {
            const group = program.edge_rewrites[rewrite_index].node_split_group orelse continue;
            const group_index = group_lookup.get(group).?;
            const position = group_positions[group_index];
            group_rewrite_indices[position] = rewrite_index;
            group_positions[group_index] = position + 1;
        }

        var group_block_offset: usize = 0;
        for (group_block_ranges.items) |*range| {
            const count = range.end;
            range.start = group_block_offset;
            range.end = std.math.add(usize, group_block_offset, count) catch return error.OutOfMemory;
            group_block_offset = range.end;
        }
        const group_block_rewrite_indices = try allocator.alloc(usize, group_block_offset);
        errdefer allocator.free(group_block_rewrite_indices);
        var group_block_positions = try allocator.alloc(usize, group_block_ranges.items.len);
        defer allocator.free(group_block_positions);
        for (group_block_ranges.items, 0..) |range, range_index| group_block_positions[range_index] = range.start;
        for (node_split_indices.items) |rewrite_index| {
            const rewrite = program.edge_rewrites[rewrite_index];
            for ([_]ReplayGroupBlockKey{
                .{ .group = rewrite.node_split_group, .block = rewrite.from.target },
                .{ .group = rewrite.node_split_group, .block = rewrite.to.target },
            }) |key| {
                const range_index = group_block_lookup.get(key).?;
                const position = group_block_positions[range_index];
                group_block_rewrite_indices[position] = rewrite_index;
                group_block_positions[range_index] = position + 1;
            }
        }

        // Index each clone target under every ancestor in its node-split
        // lineage. External mapping normally needs one producer's descendants;
        // scanning every rewrite target for every value turns large closures
        // into a quadratic search.
        var descendant_counts = try allocator.alloc(usize, program.blocks.len);
        defer allocator.free(descendant_counts);
        @memset(descendant_counts, 0);
        for (candidate_clone_targets.items) |candidate| {
            var current = candidate;
            var depth: usize = 0;
            while (true) {
                if (current.index() >= clone_sources.len) break;
                descendant_counts[current.index()] = std.math.add(
                    usize,
                    descendant_counts[current.index()],
                    1,
                ) catch return error.OutOfMemory;
                const parent = clone_sources[current.index()] orelse break;
                if (parent == current or depth >= clone_sources.len) {
                    valid = false;
                    break;
                }
                current = parent;
                depth += 1;
            }
        }

        const candidate_ranges = try allocator.alloc(ReplayCandidateRange, program.blocks.len);
        errdefer allocator.free(candidate_ranges);
        var descendant_total: usize = 0;
        for (descendant_counts, 0..) |count, block_index| {
            const start = descendant_total;
            descendant_total = std.math.add(usize, descendant_total, count) catch return error.OutOfMemory;
            candidate_ranges[block_index] = .{ .start = start, .end = descendant_total };
        }
        const candidate_descendants = try allocator.alloc(ir.BlockId, descendant_total);
        errdefer allocator.free(candidate_descendants);
        var descendant_positions = try allocator.alloc(usize, candidate_ranges.len);
        defer allocator.free(descendant_positions);
        for (candidate_ranges, 0..) |range, block_index| descendant_positions[block_index] = range.start;
        if (valid) {
            for (candidate_clone_targets.items) |candidate| {
                var current = candidate;
                var depth: usize = 0;
                while (true) {
                    if (current.index() >= clone_sources.len) break;
                    const position = descendant_positions[current.index()];
                    candidate_descendants[position] = candidate;
                    descendant_positions[current.index()] = position + 1;
                    const parent = clone_sources[current.index()] orelse break;
                    if (parent == current or depth >= clone_sources.len) break;
                    current = parent;
                    depth += 1;
                }
            }
        }

        const owned_node_split_indices = try node_split_indices.toOwnedSlice(allocator);
        errdefer allocator.free(owned_node_split_indices);
        const owned_candidate_clone_targets = try candidate_clone_targets.toOwnedSlice(allocator);
        errdefer allocator.free(owned_candidate_clone_targets);
        const owned_group_ranges = try group_ranges.toOwnedSlice(allocator);
        const owned_group_block_ranges = try group_block_ranges.toOwnedSlice(allocator);
        return .{
            .allocator = allocator,
            .clone_sources = clone_sources,
            .clone_depths = clone_depths,
            .node_split_indices = owned_node_split_indices,
            .candidate_clone_targets = owned_candidate_clone_targets,
            .candidate_ranges = candidate_ranges,
            .candidate_descendants = candidate_descendants,
            .authenticated_clone_blocks = authenticated_clone_blocks,
            .group_ranges = owned_group_ranges,
            .group_rewrite_indices = group_rewrite_indices,
            .group_lookup = group_lookup,
            .group_block_ranges = owned_group_block_ranges,
            .group_block_rewrite_indices = group_block_rewrite_indices,
            .group_block_lookup = group_block_lookup,
            .valid = valid,
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

    pub fn deinit(self: *ReplayIndex) void {
        self.allocator.free(self.clone_sources);
        self.allocator.free(self.clone_depths);
        self.allocator.free(self.node_split_indices);
        self.allocator.free(self.candidate_clone_targets);
        self.allocator.free(self.candidate_ranges);
        self.allocator.free(self.candidate_descendants);
        self.allocator.free(self.authenticated_clone_blocks);
        self.allocator.free(self.group_ranges);
        self.allocator.free(self.group_rewrite_indices);
        self.group_lookup.deinit(self.allocator);
        self.allocator.free(self.group_block_ranges);
        self.allocator.free(self.group_block_rewrite_indices);
        self.group_block_lookup.deinit(self.allocator);
        self.* = undefined;
    }

    fn groupRewriteIndices(self: *const ReplayIndex, group: ir.NodeSplitGroupId) []const usize {
        const range_index = self.group_lookup.get(group) orelse return &.{};
        const range = self.group_ranges[range_index];
        return self.group_rewrite_indices[range.start..range.end];
    }

    fn nodeSplitDepth(self: *const ReplayIndex, block: ir.BlockId) ?usize {
        if (block.index() >= self.clone_depths.len) return null;
        return self.clone_depths[block.index()];
    }

    fn adjacentRewriteIndices(
        self: *const ReplayIndex,
        group: ?ir.NodeSplitGroupId,
        block: ir.BlockId,
    ) []const usize {
        const range_index = self.group_block_lookup.get(.{ .group = group, .block = block }) orelse return &.{};
        const range = self.group_block_ranges[range_index];
        return self.group_block_rewrite_indices[range.start..range.end];
    }

    pub fn candidateCloneTargets(self: *const ReplayIndex) []const ir.BlockId {
        return self.candidate_clone_targets;
    }

    /// Return the rewrite records for one authenticated node-split group.
    /// The returned values are indexes into `program.edge_rewrites`; callers
    /// that already hold a function-scoped replay index can avoid rescanning
    /// unrelated rewrite history for every contextual mapping query.
    pub fn nodeSplitRewriteIndicesForGroup(
        self: *const ReplayIndex,
        group: ir.NodeSplitGroupId,
    ) []const usize {
        return self.groupRewriteIndices(group);
    }

    /// Return all function-scoped node-split rewrite indexes.  Consumers that
    /// need an exact edge lookup can avoid rescanning unrelated rewrite rules.
    pub fn nodeSplitRewriteIndices(self: *const ReplayIndex) []const usize {
        return self.node_split_indices;
    }

    pub fn candidateCloneTargetsForSource(
        self: *const ReplayIndex,
        program: *const ir.Program,
        source: ir.BlockId,
    ) []const ir.BlockId {
        if (source.index() >= program.blocks.len or program.blocks[source.index()].id != source) return &.{};
        if (self.function_id) |selected| {
            if (program.blocks[source.index()].function != selected) return &.{};
        }
        if (!self.valid or source.index() >= self.candidate_ranges.len) return &.{};
        const range = self.candidate_ranges[source.index()];
        return self.candidate_descendants[range.start..range.end];
    }

    /// Return whether a block is the authenticated target of any node-split
    /// rewrite in this function-scoped history.  Carrier paths can cross
    /// nested split groups; the exact entry group still authenticates the
    /// selected projection, while every traversed carrier block must have its
    /// own node-split evidence.
    pub fn isAuthenticatedCloneBlock(
        self: *const ReplayIndex,
        program: *const ir.Program,
        block: ir.BlockId,
    ) bool {
        if (!self.valid or block.index() >= program.blocks.len or
            block.index() >= self.authenticated_clone_blocks.len or
            program.blocks[block.index()].id != block)
        {
            return false;
        }
        if (self.function_id) |selected| {
            if (program.blocks[block.index()].function != selected) return false;
        }
        return self.authenticated_clone_blocks[block.index()];
    }

    fn ownsMapping(
        self: *const ReplayIndex,
        program: *const ir.Program,
        source: ir.BlockId,
        clone: ir.BlockId,
        group: ir.NodeSplitGroupId,
    ) bool {
        if (source.index() >= program.blocks.len or clone.index() >= program.blocks.len) return false;
        const source_block = program.blocks[source.index()];
        const clone_block = program.blocks[clone.index()];
        if (source_block.id != source or clone_block.id != clone or
            source_block.function != clone_block.function)
        {
            return false;
        }
        if (self.function_id) |selected| {
            if (source_block.function != selected) return false;
        }
        for (self.groupRewriteIndices(group)) |rewrite_index| {
            const rewrite = program.edge_rewrites[rewrite_index];
            if (rewrite.from.target == source and rewrite.to.target == clone) return true;
        }
        return false;
    }

    pub fn groupOwnsBlock(
        self: *const ReplayIndex,
        program: *const ir.Program,
        group: ir.NodeSplitGroupId,
        block: ir.BlockId,
    ) bool {
        if (!self.valid) return false;
        if (block.index() >= program.blocks.len or program.blocks[block.index()].id != block) return false;
        if (self.function_id) |selected| {
            if (program.blocks[block.index()].function != selected) return false;
        }
        for (self.groupRewriteIndices(group)) |rewrite_index| {
            const rewrite = program.edge_rewrites[rewrite_index];
            if (rewrite.to.target != block or rewrite.from.target.index() >= program.blocks.len) continue;
            if (program.blocks[rewrite.from.target.index()].function == program.blocks[block.index()].function) return true;
        }
        return false;
    }
};

test "function-scoped replay index excludes foreign rewrite history" {
    const first_function = ir.FunctionId.fromIndex(0);
    const second_function = ir.FunctionId.fromIndex(1);
    const first_source = ir.BlockId.fromIndex(0);
    const first_original = ir.BlockId.fromIndex(1);
    const first_clone = ir.BlockId.fromIndex(2);
    const second_source = ir.BlockId.fromIndex(3);
    const second_original = ir.BlockId.fromIndex(4);
    const second_clone = ir.BlockId.fromIndex(5);

    const blocks = [_]ir.Block{
        .{ .id = first_source, .function = first_function, .terminator = .{ .unreachable_block = {} } },
        .{ .id = first_original, .function = first_function, .terminator = .{ .unreachable_block = {} } },
        .{ .id = first_clone, .function = first_function, .terminator = .{ .unreachable_block = {} } },
        .{ .id = second_source, .function = second_function, .terminator = .{ .unreachable_block = {} } },
        .{ .id = second_original, .function = second_function, .terminator = .{ .unreachable_block = {} } },
        .{ .id = second_clone, .function = second_function, .terminator = .{ .unreachable_block = {} } },
    };
    const functions = [_]ir.Function{
        .{ .id = first_function, .blocks = &.{ first_source, first_original, first_clone }, .entry_block = first_source },
        .{ .id = second_function, .blocks = &.{ second_source, second_original, second_clone }, .entry_block = second_source },
    };
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = ir.EdgeRewriteId.fromIndex(0),
            .source = first_source,
            .kind = .jump,
            .from = .{ .target = first_original },
            .to = .{ .target = first_clone },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(0),
        },
        .{
            .id = ir.EdgeRewriteId.fromIndex(1),
            .source = second_source,
            .kind = .jump,
            .from = .{ .target = second_original },
            .to = .{ .target = second_clone },
            .rule = .node_split,
            .node_split_group = ir.NodeSplitGroupId.fromIndex(1),
        },
    };
    const program = ir.Program{
        .program_id = "function-scoped-replay-index",
        .entry_function = first_function,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .edge_rewrites = &rewrites,
    };

    var index = try ReplayIndex.initForFunction(std.testing.allocator, &program, first_function);
    defer index.deinit();
    try std.testing.expect(index.valid);
    try std.testing.expectEqual(@as(usize, 1), index.node_split_indices.len);
    const first_group_rewrites = index.nodeSplitRewriteIndicesForGroup(ir.NodeSplitGroupId.fromIndex(0));
    try std.testing.expectEqual(@as(usize, 1), first_group_rewrites.len);
    try std.testing.expectEqual(@as(usize, 0), first_group_rewrites[0]);
    try std.testing.expectEqual(@as(usize, 0), index.nodeSplitRewriteIndicesForGroup(ir.NodeSplitGroupId.fromIndex(1)).len);
    try std.testing.expectEqual(@as(usize, 1), index.candidateCloneTargetsForSource(&program, first_original).len);
    try std.testing.expectEqual(first_clone, index.candidateCloneTargetsForSource(&program, first_original)[0]);
    try std.testing.expectEqual(@as(usize, 0), index.candidateCloneTargetsForSource(&program, second_original).len);
    try std.testing.expect(index.clone_sources[second_clone.index()] == null);
}

fn replayMappingsAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    current_source: ir.BlockId,
    current_clone: ir.BlockId,
    group: ?ir.NodeSplitGroupId,
    replay_index: ?*const ReplayIndex,
) std.mem.Allocator.Error!?ReplayMappings {
    if (current_source.index() >= program.blocks.len or current_clone.index() >= program.blocks.len) return null;
    const source_block = program.blocks[current_source.index()];
    const clone_block = program.blocks[current_clone.index()];
    if (source_block.id != current_source or clone_block.id != current_clone or
        source_block.function != clone_block.function)
    {
        return null;
    }
    if (replay_index) |index| {
        if (index.function_id) |function_id| {
            if (source_block.function != function_id) return null;
        }
    }
    var owned_clone_sources: ?[]?ir.BlockId = null;
    const clone_sources: []?ir.BlockId = if (replay_index) |index| blk: {
        if (!index.valid) return null;
        break :blk index.clone_sources;
    } else blk: {
        const allocated = try allocator.alloc(?ir.BlockId, program.blocks.len);
        owned_clone_sources = allocated;
        @memset(allocated, null);
        for (program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.to.target.index() >= program.blocks.len or
                rewrite.from.target.index() >= program.blocks.len or rewrite.to.target == rewrite.from.target) continue;
            if (allocated[rewrite.to.target.index()]) |existing| {
                if (existing != rewrite.from.target) return null;
            } else {
                allocated[rewrite.to.target.index()] = rewrite.from.target;
            }
        }
        break :blk allocated;
    };
    defer if (owned_clone_sources) |allocated| allocator.free(allocated);
    if (group) |requested_group| {
        if (replay_index) |index| {
            if (!index.ownsMapping(program, current_source, current_clone, requested_group)) return null;
        } else {
            var owns_mapping = false;
            for (program.edge_rewrites) |rewrite| {
                if (rewrite.rule == .node_split and rewrite.node_split_group == requested_group and
                    rewrite.from.target == current_source and rewrite.to.target == current_clone)
                {
                    owns_mapping = true;
                    break;
                }
            }
            if (!owns_mapping) return null;
        }
    }
    if (current_clone.index() >= clone_sources.len) return null;
    if (clone_sources[current_clone.index()]) |recorded| {
        if (recorded != current_source) return null;
    } else {
        if (replay_index != null) return null;
        clone_sources[current_clone.index()] = current_source;
    }
    const source_depth = replayNodeSplitDepth(replay_index, clone_sources, current_source) orelse return null;
    const clone_depth = replayNodeSplitDepth(replay_index, clone_sources, current_clone) orelse return null;
    if (clone_depth != std.math.add(usize, source_depth, 1) catch return null) return null;

    const active = try allocator.alloc(bool, program.blocks.len);
    defer allocator.free(active);
    @memset(active, false);
    var group_owned: ?[]bool = null;
    if (replay_index == null) {
        const allocated = try allocator.alloc(bool, program.blocks.len);
        group_owned = allocated;
        @memset(allocated, false);
        if (group) |requested_group| {
            for (program.edge_rewrites) |rewrite| {
                if (rewrite.rule == .node_split and rewrite.node_split_group == requested_group and
                    rewrite.to.target.index() < allocated.len)
                {
                    allocated[rewrite.to.target.index()] = true;
                }
            }
        }
    }
    defer if (group_owned) |allocated| allocator.free(allocated);
    var pending: std.ArrayList(ir.BlockId) = .empty;
    defer pending.deinit(allocator);
    try pending.append(allocator, current_clone);
    if (replay_index) |index| {
        while (pending.pop()) |clone_id| {
            if (clone_id.index() >= active.len or active[clone_id.index()]) continue;
            active[clone_id.index()] = true;
            const rewrite_indices = index.adjacentRewriteIndices(group, clone_id);
            for (rewrite_indices) |rewrite_index| {
                const rewrite = program.edge_rewrites[rewrite_index];
                if (group == null and rewrite.node_split_group != null) continue;
                if (rewrite.from.target.index() >= program.blocks.len or rewrite.to.target.index() >= program.blocks.len or
                    program.blocks[rewrite.from.target.index()].function != source_block.function or
                    program.blocks[rewrite.to.target.index()].function != source_block.function)
                {
                    continue;
                }
                const mapped_source_depth = replayNodeSplitDepth(replay_index, clone_sources, rewrite.from.target) orelse return null;
                const mapped_clone_depth = replayNodeSplitDepth(replay_index, clone_sources, rewrite.to.target) orelse return null;
                if (mapped_source_depth != source_depth or mapped_clone_depth != clone_depth) continue;
                const source_is_owned = if (group) |requested_group|
                    index.groupOwnsBlock(program, requested_group, rewrite.source)
                else
                    true;
                if (source_is_owned and rewrite.source == clone_id and rewrite.to.target.index() < clone_sources.len and
                    clone_sources[rewrite.to.target.index()] != null)
                {
                    try pending.append(allocator, rewrite.to.target);
                }
                if (source_is_owned and rewrite.to.target == clone_id and rewrite.source.index() < clone_sources.len and
                    clone_sources[rewrite.source.index()] != null)
                {
                    try pending.append(allocator, rewrite.source);
                }
            }
        }
    } else while (pending.pop()) |clone_id| {
        if (clone_id.index() >= active.len or active[clone_id.index()]) continue;
        active[clone_id.index()] = true;
        for (program.edge_rewrites) |rewrite| {
            if (rewrite.rule != .node_split or rewrite.node_split_group != group) continue;
            const mapped_source_depth = replayNodeSplitDepth(replay_index, clone_sources, rewrite.from.target) orelse return null;
            const mapped_clone_depth = replayNodeSplitDepth(replay_index, clone_sources, rewrite.to.target) orelse return null;
            if (mapped_source_depth != source_depth or mapped_clone_depth != clone_depth) continue;
            const source_is_owned = group == null or
                (rewrite.source.index() < group_owned.?.len and group_owned.?[rewrite.source.index()]);
            if (source_is_owned and rewrite.source == clone_id and rewrite.to.target.index() < clone_sources.len and
                clone_sources[rewrite.to.target.index()] != null)
            {
                try pending.append(allocator, rewrite.to.target);
            }
            if (source_is_owned and rewrite.to.target == clone_id and rewrite.source.index() < clone_sources.len and
                clone_sources[rewrite.source.index()] != null)
            {
                try pending.append(allocator, rewrite.source);
            }
        }
    }

    var source_values: std.ArrayList(ir.ValueId) = .empty;
    defer source_values.deinit(allocator);
    var clone_values: std.ArrayList(ir.ValueId) = .empty;
    defer clone_values.deinit(allocator);
    var source_packs: std.ArrayList(ir.ValuePackId) = .empty;
    defer source_packs.deinit(allocator);
    var clone_packs: std.ArrayList(ir.ValuePackId) = .empty;
    defer clone_packs.deinit(allocator);
    for (active, 0..) |is_active, clone_index| {
        if (!is_active or clone_index == current_clone.index()) continue;
        const source_id = clone_sources[clone_index] orelse return null;
        if (!try appendReplayBlockMappings(
            allocator,
            program,
            source_id,
            ir.BlockId.fromIndex(clone_index),
            &source_values,
            &clone_values,
            &source_packs,
            &clone_packs,
        )) return null;
    }
    // Seed the current block's canonical parameter/result identities before
    // inferring mappings from uses. Otherwise a tampered clone can mention a
    // source value directly and manufacture an identity mapping that masks
    // the required source-to-clone projection.
    if (!try appendReplayBlockMappings(
        allocator,
        program,
        current_source,
        current_clone,
        &source_values,
        &clone_values,
        &source_packs,
        &clone_packs,
    )) return null;
    if (!try appendReplayUseMappingsFrom(
        allocator,
        program,
        current_source,
        current_clone,
        &source_values,
        &clone_values,
        &source_packs,
        &clone_packs,
        if (group) |requested_group| requested_group.index() else 0,
    )) return null;
    const owned_source_values = try source_values.toOwnedSlice(allocator);
    errdefer allocator.free(owned_source_values);
    const owned_clone_values = try clone_values.toOwnedSlice(allocator);
    errdefer allocator.free(owned_clone_values);
    const owned_source_packs = try source_packs.toOwnedSlice(allocator);
    errdefer allocator.free(owned_source_packs);
    const owned_clone_packs = try clone_packs.toOwnedSlice(allocator);
    errdefer allocator.free(owned_clone_packs);
    return .{
        .allocator = allocator,
        .source_values = owned_source_values,
        .clone_values = owned_clone_values,
        .source_packs = owned_source_packs,
        .clone_packs = owned_clone_packs,
        .history_start = if (group) |requested_group| requested_group.index() else null,
    };
}

const UseCollector = struct {
    allocator: std.mem.Allocator,
    values: *std.ArrayList(ir.ValueId),
    packs: *std.ArrayList(ir.ValuePackId),
    out_of_memory: *bool,

    pub fn value(self: *UseCollector, value_id: ir.ValueId) void {
        self.values.append(self.allocator, value_id) catch {
            self.out_of_memory.* = true;
        };
    }

    pub fn pack(self: *UseCollector, pack_id: ir.ValuePackId) void {
        self.packs.append(self.allocator, pack_id) catch {
            self.out_of_memory.* = true;
        };
    }

    pub fn place(_: *UseCollector, _: ir.PlaceId) void {}
};

fn appendReplayUseMappingsFrom(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source_id: ir.BlockId,
    clone_id: ir.BlockId,
    source_values: *std.ArrayList(ir.ValueId),
    clone_values: *std.ArrayList(ir.ValueId),
    source_packs: *std.ArrayList(ir.ValuePackId),
    clone_packs: *std.ArrayList(ir.ValuePackId),
    history_start: usize,
) std.mem.Allocator.Error!bool {
    if (source_id.index() >= program.blocks.len or clone_id.index() >= program.blocks.len) return false;
    const source = program.blocks[source_id.index()];
    const clone = program.blocks[clone_id.index()];
    if (source.id != source_id or clone.id != clone_id or source.instructions.len != clone.instructions.len) return false;

    var source_used_values: std.ArrayList(ir.ValueId) = .empty;
    defer source_used_values.deinit(allocator);
    var clone_used_values: std.ArrayList(ir.ValueId) = .empty;
    defer clone_used_values.deinit(allocator);
    var source_used_packs: std.ArrayList(ir.ValuePackId) = .empty;
    defer source_used_packs.deinit(allocator);
    var clone_used_packs: std.ArrayList(ir.ValuePackId) = .empty;
    defer clone_used_packs.deinit(allocator);
    var out_of_memory = false;

    for (source.instructions, clone.instructions) |source_instruction_id, clone_instruction_id| {
        if (source_instruction_id.index() >= program.instructions.len or clone_instruction_id.index() >= program.instructions.len) return false;
        const source_instruction = program.instructions[source_instruction_id.index()];
        const clone_instruction = program.instructions[clone_instruction_id.index()];
        if (source_instruction.id != source_instruction_id or clone_instruction.id != clone_instruction_id) return false;
        source_used_values.clearRetainingCapacity();
        clone_used_values.clearRetainingCapacity();
        source_used_packs.clearRetainingCapacity();
        clone_used_packs.clearRetainingCapacity();
        var source_collector = UseCollector{
            .allocator = allocator,
            .values = &source_used_values,
            .packs = &source_used_packs,
            .out_of_memory = &out_of_memory,
        };
        var clone_collector = UseCollector{
            .allocator = allocator,
            .values = &clone_used_values,
            .packs = &clone_used_packs,
            .out_of_memory = &out_of_memory,
        };
        runtime_uses.visitOperationUses(source_instruction.operation, &source_collector);
        runtime_uses.visitOperationUses(clone_instruction.operation, &clone_collector);
        if (out_of_memory) return error.OutOfMemory;
        if (source_used_values.items.len != clone_used_values.items.len or
            source_used_packs.items.len != clone_used_packs.items.len)
            return false;
        for (source_used_values.items, clone_used_values.items) |source_value, clone_value| {
            if (!replayValuePairCompatible(program, source_value, clone_value) or
                !try appendReplayValueMapping(allocator, source_values, clone_values, source_value, clone_value)) return false;
        }
        for (source_used_packs.items, clone_used_packs.items) |source_pack, clone_pack| {
            if (!replayPackPairCompatible(program, source_pack, clone_pack) or
                !try appendReplayPackMapping(allocator, source_packs, clone_packs, source_pack, clone_pack)) return false;
        }
    }

    source_used_values.clearRetainingCapacity();
    clone_used_values.clearRetainingCapacity();
    source_used_packs.clearRetainingCapacity();
    clone_used_packs.clearRetainingCapacity();
    var source_collector = UseCollector{
        .allocator = allocator,
        .values = &source_used_values,
        .packs = &source_used_packs,
        .out_of_memory = &out_of_memory,
    };
    var clone_collector = UseCollector{
        .allocator = allocator,
        .values = &clone_used_values,
        .packs = &clone_used_packs,
        .out_of_memory = &out_of_memory,
    };
    const terminators = reverseStructuralTerminatorPair(
        program,
        source.id,
        source.terminator,
        clone.id,
        clone.terminator,
        history_start,
    );
    runtime_uses.visitTerminatorUses(terminators.source, &source_collector);
    runtime_uses.visitTerminatorUses(terminators.clone, &clone_collector);
    if (out_of_memory) return error.OutOfMemory;
    if (source_used_values.items.len != clone_used_values.items.len or
        source_used_packs.items.len != clone_used_packs.items.len)
        return false;
    for (source_used_values.items, clone_used_values.items) |source_value, clone_value| {
        if (!replayValuePairCompatible(program, source_value, clone_value) or
            !try appendReplayTerminatorValueMapping(
                allocator,
                program,
                source.id,
                clone.id,
                source_values,
                clone_values,
                source_value,
                clone_value,
            )) return false;
    }
    for (source_used_packs.items, clone_used_packs.items) |source_pack, clone_pack| {
        if (!replayPackPairCompatible(program, source_pack, clone_pack) or
            !try appendReplayPackMapping(allocator, source_packs, clone_packs, source_pack, clone_pack)) return false;
    }
    return true;
}

fn replayValuePairCompatible(program: *const ir.Program, source_id: ir.ValueId, clone_id: ir.ValueId) bool {
    if (source_id == clone_id) return true;
    if (source_id.index() >= program.values.len or clone_id.index() >= program.values.len) return false;
    const source = program.values[source_id.index()];
    const clone = program.values[clone_id.index()];
    return source.id == source_id and clone.id == clone_id and source.function == clone.function and
        sameType(source.type, clone.type) and sameOptionalString(source.name_hint, clone.name_hint);
}

fn replayPackPairCompatible(program: *const ir.Program, source_id: ir.ValuePackId, clone_id: ir.ValuePackId) bool {
    if (source_id == clone_id) return true;
    if (source_id.index() >= program.value_packs.len or clone_id.index() >= program.value_packs.len) return false;
    const source = program.value_packs[source_id.index()];
    const clone = program.value_packs[clone_id.index()];
    return source.id == source_id and clone.id == clone_id and source.function == clone.function and
        samePackShape(source.shape, clone.shape) and std.mem.eql(ir.EvidenceId, source.evidence, clone.evidence);
}

fn populateNodeSplitDepths(
    allocator: std.mem.Allocator,
    clone_sources: []const ?ir.BlockId,
    depths: []?usize,
) std.mem.Allocator.Error!bool {
    const states = try allocator.alloc(u8, clone_sources.len);
    defer allocator.free(states);
    @memset(states, 0);

    var path: std.ArrayList(usize) = .empty;
    defer path.deinit(allocator);
    var valid = true;

    for (0..clone_sources.len) |start| {
        if (states[start] != 0) continue;
        path.clearRetainingCapacity();

        var current = ir.BlockId.fromIndex(start);
        var resolved_depth: usize = 0;
        var resolved_from_parent = false;
        var invalid = false;
        while (true) {
            if (current.index() >= clone_sources.len) {
                invalid = true;
                break;
            }
            switch (states[current.index()]) {
                2 => {
                    resolved_depth = depths[current.index()] orelse {
                        invalid = true;
                        break;
                    };
                    resolved_from_parent = true;
                    break;
                },
                1 => {
                    invalid = true;
                    break;
                },
                else => {
                    states[current.index()] = 1;
                    try path.append(allocator, current.index());
                    if (clone_sources[current.index()]) |parent| {
                        current = parent;
                    } else {
                        resolved_depth = 0;
                        resolved_from_parent = false;
                        break;
                    }
                },
            }
        }

        if (invalid) {
            valid = false;
            for (path.items) |index| {
                states[index] = 2;
                depths[index] = null;
            }
            continue;
        }

        var depth = resolved_depth;
        if (resolved_from_parent) depth = std.math.add(usize, depth, 1) catch return false;
        var reverse = path.items.len;
        while (reverse != 0) {
            reverse -= 1;
            const index = path.items[reverse];
            depths[index] = depth;
            states[index] = 2;
            if (reverse != 0) depth = std.math.add(usize, depth, 1) catch return false;
        }
    }
    return valid;
}

fn replayNodeSplitDepth(
    replay_index: ?*const ReplayIndex,
    clone_sources: []const ?ir.BlockId,
    block: ir.BlockId,
) ?usize {
    if (replay_index) |index| return index.nodeSplitDepth(block);
    return nodeSplitDepth(clone_sources, block);
}

fn nodeSplitDepth(clone_sources: []const ?ir.BlockId, block: ir.BlockId) ?usize {
    var current = block;
    var depth: usize = 0;
    while (current.index() < clone_sources.len) {
        const parent = clone_sources[current.index()] orelse return depth;
        depth = std.math.add(usize, depth, 1) catch return null;
        if (depth > clone_sources.len) return null;
        current = parent;
    }
    return null;
}

fn appendReplayBlockMappings(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source_id: ir.BlockId,
    clone_id: ir.BlockId,
    source_values: *std.ArrayList(ir.ValueId),
    clone_values: *std.ArrayList(ir.ValueId),
    source_packs: *std.ArrayList(ir.ValuePackId),
    clone_packs: *std.ArrayList(ir.ValuePackId),
) std.mem.Allocator.Error!bool {
    if (source_id.index() >= program.blocks.len or clone_id.index() >= program.blocks.len) return false;
    const source = program.blocks[source_id.index()];
    const clone = program.blocks[clone_id.index()];
    if (source.id != source_id or clone.id != clone_id or source.function != clone.function or
        source.parameters.len != clone.parameters.len or source.instructions.len != clone.instructions.len) return false;
    for (source.parameters, clone.parameters) |source_value, clone_value| {
        if (!try appendReplayValueMapping(allocator, source_values, clone_values, source_value, clone_value)) return false;
    }
    for (source.instructions, clone.instructions) |source_instruction_id, clone_instruction_id| {
        if (source_instruction_id.index() >= program.instructions.len or clone_instruction_id.index() >= program.instructions.len) return false;
        const source_instruction = program.instructions[source_instruction_id.index()];
        const clone_instruction = program.instructions[clone_instruction_id.index()];
        if (source_instruction.id != source_instruction_id or clone_instruction.id != clone_instruction_id or
            source_instruction.block != source.id or clone_instruction.block != clone.id or
            source_instruction.results.len != clone_instruction.results.len or
            (source_instruction.pack_result == null) != (clone_instruction.pack_result == null)) return false;
        for (source_instruction.results, clone_instruction.results) |source_value, clone_value| {
            if (!try appendReplayValueMapping(allocator, source_values, clone_values, source_value, clone_value)) return false;
        }
        if (source_instruction.pack_result) |source_pack| {
            if (!try appendReplayPackMapping(
                allocator,
                source_packs,
                clone_packs,
                source_pack,
                clone_instruction.pack_result.?,
            )) return false;
        }
    }
    return true;
}

fn appendReplayValueMapping(
    allocator: std.mem.Allocator,
    sources: *std.ArrayList(ir.ValueId),
    clones: *std.ArrayList(ir.ValueId),
    source: ir.ValueId,
    clone: ir.ValueId,
) std.mem.Allocator.Error!bool {
    for (sources.items, clones.items) |existing_source, existing_clone| {
        if (existing_source == source) return existing_clone == clone;
        if (source == clone and existing_clone == clone) return true;
        if (existing_clone == clone) return false;
    }
    try sources.append(allocator, source);
    try clones.append(allocator, clone);
    return true;
}

// A cloned terminator may project multiple external block parameters onto one
// value when the selected incoming edge has already authenticated that alias.
// Keep instruction results, local block parameters, and all pack mappings
// injective; only the external edge tuple gets this narrower relation.
fn appendReplayTerminatorValueMapping(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source_block: ir.BlockId,
    clone_block: ir.BlockId,
    sources: *std.ArrayList(ir.ValueId),
    clones: *std.ArrayList(ir.ValueId),
    source: ir.ValueId,
    clone: ir.ValueId,
) std.mem.Allocator.Error!bool {
    for (sources.items, clones.items) |existing_source, existing_clone| {
        if (existing_source == source) return existing_clone == clone;
        if (source == clone and existing_clone == clone) return true;
        if (existing_clone != clone) continue;
        if (!replayValuePairCompatible(program, existing_source, source) or
            !replayExternalAliasSourcePair(program, source_block, existing_source, source) or
            !replayExternalValue(program, clone_block, existing_clone)) return false;
    }
    try sources.append(allocator, source);
    try clones.append(allocator, clone);
    return true;
}

fn replayExternalAliasSourcePair(
    program: *const ir.Program,
    block_id: ir.BlockId,
    left_id: ir.ValueId,
    right_id: ir.ValueId,
) bool {
    if (left_id.index() >= program.values.len or right_id.index() >= program.values.len) return false;
    const left = program.values[left_id.index()];
    const right = program.values[right_id.index()];
    if (left.id != left_id or right.id != right_id) return false;
    const left_origin = switch (left.origin) {
        .block_parameter => |origin| origin,
        .parameter, .capture, .instruction_result => return false,
    };
    const right_origin = switch (right.origin) {
        .block_parameter => |origin| origin,
        .parameter, .capture, .instruction_result => return false,
    };
    return left_origin.block != block_id and left_origin.block == right_origin.block;
}

fn replayExternalValue(
    program: *const ir.Program,
    block_id: ir.BlockId,
    value_id: ir.ValueId,
) bool {
    if (value_id.index() >= program.values.len) return false;
    const value = program.values[value_id.index()];
    if (value.id != value_id) return false;
    return switch (value.origin) {
        .parameter, .capture => true,
        .block_parameter => |origin| origin.block != block_id,
        .instruction_result => |origin| blk: {
            if (origin.instruction.index() >= program.instructions.len) break :blk false;
            break :blk program.instructions[origin.instruction.index()].block != block_id;
        },
    };
}

fn appendReplayPackMapping(
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

fn sameMappedBlockAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    source: ir.Block,
    clone: ir.Block,
    external: ReplayMappings,
) std.mem.Allocator.Error!bool {
    if (source.parameters.len != clone.parameters.len or
        source.instructions.len != clone.instructions.len or
        !parametersAreCanonical(program.values, source) or
        !parametersAreCanonical(program.values, clone) or
        !node_split_instruction.sequenceIsCloneableWithMappings(
            program,
            source,
            external.source_values,
            external.source_packs,
        ) or
        !node_split_instruction.sequenceIsCloneableWithMappings(
            program,
            clone,
            external.clone_values,
            external.clone_packs,
        )) return false;

    if (external.source_values.len != external.clone_values.len or external.source_packs.len != external.clone_packs.len) return false;
    const local_value_capacity = mappedValueCapacity(program, source) orelse return false;
    const mapped_capacity = std.math.add(usize, external.source_values.len, local_value_capacity) catch return false;
    const source_values = try allocator.alloc(ir.ValueId, mapped_capacity);
    defer allocator.free(source_values);
    const clone_values = try allocator.alloc(ir.ValueId, mapped_capacity);
    defer allocator.free(clone_values);
    @memcpy(source_values[0..external.source_values.len], external.source_values);
    @memcpy(clone_values[0..external.clone_values.len], external.clone_values);
    const local_pack_capacity = mappedPackCapacity(program, source) orelse return false;
    const mapped_pack_capacity = std.math.add(usize, external.source_packs.len, local_pack_capacity) catch return false;
    const source_packs = try allocator.alloc(ir.ValuePackId, mapped_pack_capacity);
    defer allocator.free(source_packs);
    const clone_packs = try allocator.alloc(ir.ValuePackId, mapped_pack_capacity);
    defer allocator.free(clone_packs);
    @memcpy(source_packs[0..external.source_packs.len], external.source_packs);
    @memcpy(clone_packs[0..external.clone_packs.len], external.clone_packs);
    var mapped_count: usize = external.source_values.len;
    var mapped_pack_count: usize = external.source_packs.len;

    for (source.parameters, clone.parameters, 0..) |source_id, clone_id, parameter_index| {
        if (source_id == clone_id) return false;
        const source_value = program.values[source_id.index()];
        const clone_value = program.values[clone_id.index()];
        if (!sameType(source_value.type, clone_value.type) or
            !sameOptionalString(source_value.name_hint, clone_value.name_hint)) return false;
        const source_origin = source_value.origin.block_parameter;
        const clone_origin = clone_value.origin.block_parameter;
        if (source_origin.block != source.id or source_origin.index != parameter_index or
            clone_origin.block != clone.id or clone_origin.index != parameter_index) return false;
        source_values[mapped_count] = source_id;
        clone_values[mapped_count] = clone_id;
        mapped_count += 1;
    }

    for (source.instructions, clone.instructions, 0..) |source_id, clone_id, instruction_index| {
        if (source_id == clone_id) return false;
        for (source.instructions) |candidate| if (candidate == clone_id) return false;
        for (clone.instructions[0..instruction_index]) |prior| if (prior == clone_id) return false;
        const source_instruction = program.instructions[source_id.index()];
        const clone_instruction = program.instructions[clone_id.index()];
        if (source_instruction.results.len != clone_instruction.results.len or
            !node_split_instruction.sameEffects(source_instruction.effects, clone_instruction.effects) or
            !std.mem.eql(ir.EvidenceId, source_instruction.evidence, clone_instruction.evidence)) return false;
        const mapped_operation = (try node_split_instruction.remapOperation(
            allocator,
            program,
            program.values,
            source.function,
            source_instruction.operation,
            source_values[0..mapped_count],
            clone_values[0..mapped_count],
            source_packs[0..mapped_pack_count],
            clone_packs[0..mapped_pack_count],
        )) orelse return false;
        defer node_split_instruction.deinitRemappedOperation(allocator, mapped_operation);
        if (!node_split_instruction.sameOperation(mapped_operation, clone_instruction.operation)) return false;

        for (source_instruction.results, clone_instruction.results) |source_result_id, clone_result_id| {
            if (source_result_id == clone_result_id) return false;
            for (source_values[0..mapped_count]) |candidate| if (candidate == clone_result_id) return false;
            for (clone_values[0..mapped_count]) |candidate| if (candidate == source_result_id) return false;
            const source_result = program.values[source_result_id.index()];
            const clone_result = program.values[clone_result_id.index()];
            if (!sameType(source_result.type, clone_result.type) or
                !sameOptionalString(source_result.name_hint, clone_result.name_hint)) return false;
            source_values[mapped_count] = source_result_id;
            clone_values[mapped_count] = clone_result_id;
            mapped_count += 1;
        }
        if (!sameMappedPackResult(
            program,
            source.function,
            source_id,
            clone_id,
            source_instruction.pack_result,
            clone_instruction.pack_result,
            source_packs[0..mapped_pack_count],
            clone_packs[0..mapped_pack_count],
        )) return false;
        if (source_instruction.pack_result) |source_pack_id| {
            source_packs[mapped_pack_count] = source_pack_id;
            clone_packs[mapped_pack_count] = clone_instruction.pack_result.?;
            mapped_pack_count += 1;
        }
    }

    const history_start = external.history_start orelse 0;
    if (history_start > program.edge_rewrites.len) return false;
    const terminators = reverseStructuralTerminatorPair(
        program,
        source.id,
        source.terminator,
        clone.id,
        clone.terminator,
        history_start,
    );
    return sameMappedTerminator(
        terminators.source,
        terminators.clone,
        source.id,
        clone.id,
        source_values[0..mapped_count],
        clone_values[0..mapped_count],
    );
}

const StructuralTerminatorPair = struct {
    source: ir.Terminator,
    clone: ir.Terminator,
};

fn reverseStructuralTerminatorPair(
    program: *const ir.Program,
    source_block: ir.BlockId,
    source_terminator: ir.Terminator,
    clone_block: ir.BlockId,
    clone_terminator: ir.Terminator,
    history_start: usize,
) StructuralTerminatorPair {
    // A consumed branch is proof metadata for the post-branch jump unless the
    // other side is itself a branch or carries the same authenticated
    // witness. Restoring it on only one side makes an exact clone of the
    // selected arm look structurally different.
    const source_consumed_branch = if (source_terminator == .jump)
        edge_path.consumedBranchForReplay(program, source_block)
    else
        null;
    const clone_consumed_branch = if (clone_terminator == .jump)
        edge_path.consumedBranchForReplay(program, clone_block)
    else
        null;
    const source_branch_compatible = source_terminator == .branch or source_consumed_branch != null;
    const clone_branch_compatible = clone_terminator == .branch or clone_consumed_branch != null;
    const restore_consumed_branch = source_branch_compatible and clone_branch_compatible;
    return .{
        .source = reverseStructuralTerminatorFromWithMode(
            program,
            source_block,
            source_terminator,
            history_start,
            restore_consumed_branch,
        ),
        .clone = reverseStructuralTerminatorFromWithMode(
            program,
            clone_block,
            clone_terminator,
            history_start,
            restore_consumed_branch,
        ),
    };
}

fn reverseStructuralTerminatorFromWithMode(
    program: *const ir.Program,
    block: ir.BlockId,
    terminator: ir.Terminator,
    history_start: usize,
    restore_consumed_branch: bool,
) ir.Terminator {
    var result = terminator;
    if (restore_consumed_branch and result == .jump) {
        if (edge_path.consumedBranchForReplay(program, block)) |branch| {
            const live = result.jump;
            if (sameEdge(live, branch.then_edge) or sameEdge(live, branch.else_edge)) {
                result = .{ .branch = branch };
            }
        }
    }
    var index = program.edge_rewrites.len;
    while (index > history_start) {
        index -= 1;
        const rewrite = program.edge_rewrites[index];
        if (rewrite.source != block or
            (rewrite.rule != .node_split and rewrite.rule != .forwarding_jump and rewrite.rule != .clone_fold)) continue;
        _ = replaceTerminatorEdge(&result, rewrite.kind, rewrite.to, rewrite.from);
    }
    return result;
}

fn replaceTerminatorEdge(terminator: *ir.Terminator, kind: ir.CfgEdgeKind, expected: ir.Edge, replacement: ir.Edge) bool {
    switch (terminator.*) {
        .jump => |edge| {
            if (kind != .jump or !sameEdge(edge, expected)) return false;
            terminator.* = .{ .jump = replacement };
        },
        .branch => |branch| {
            var changed = branch;
            switch (kind) {
                .branch_then => {
                    if (!sameEdge(branch.then_edge, expected)) return false;
                    changed.then_edge = replacement;
                },
                .branch_else => {
                    if (!sameEdge(branch.else_edge, expected)) return false;
                    changed.else_edge = replacement;
                },
                .jump => return false,
            }
            terminator.* = .{ .branch = changed };
        },
        else => return false,
    }
    return true;
}

fn sameEdge(left: ir.Edge, right: ir.Edge) bool {
    return left.target == right.target and std.mem.eql(ir.ValueId, left.arguments, right.arguments);
}

fn remapTerminatorAlloc(
    allocator: std.mem.Allocator,
    terminator: ir.Terminator,
    source_block: ir.BlockId,
    clone_block: ir.BlockId,
    source_parameters: []const ir.ValueId,
    clone_parameters: []const ir.ValueId,
) std.mem.Allocator.Error!ir.Terminator {
    return switch (terminator) {
        .jump => |edge| .{ .jump = try remapEdgeAlloc(allocator, edge, source_block, clone_block, source_parameters, clone_parameters) },
        .branch => |branch| .{ .branch = .{
            .condition = remapValue(branch.condition, source_parameters, clone_parameters),
            .then_edge = try remapEdgeAlloc(allocator, branch.then_edge, source_block, clone_block, source_parameters, clone_parameters),
            .else_edge = try remapEdgeAlloc(allocator, branch.else_edge, source_block, clone_block, source_parameters, clone_parameters),
        } },
        .return_values => |items| .{ .return_values = try remapValuesAlloc(allocator, items, source_parameters, clone_parameters) },
        .return_pack => |pack| .{ .return_pack = pack },
        .return_expanded => |expanded| .{ .return_expanded = .{
            .values = try remapValuesAlloc(allocator, expanded.values, source_parameters, clone_parameters),
            .pack = expanded.pack,
        } },
        .throw_error => |throw_error| .{ .throw_error = .{
            .value = remapValue(throw_error.value, source_parameters, clone_parameters),
            .level = throw_error.level,
            .dynamic_level = if (throw_error.dynamic_level) |level|
                remapValue(level, source_parameters, clone_parameters)
            else
                null,
        } },
        .unreachable_block => .{ .unreachable_block = {} },
    };
}

fn remapEdgeAlloc(
    allocator: std.mem.Allocator,
    edge: ir.Edge,
    source_block: ir.BlockId,
    clone_block: ir.BlockId,
    source_parameters: []const ir.ValueId,
    clone_parameters: []const ir.ValueId,
) std.mem.Allocator.Error!ir.Edge {
    return .{
        .target = remapBlockTarget(edge.target, source_block, clone_block),
        .arguments = try remapValuesAlloc(allocator, edge.arguments, source_parameters, clone_parameters),
    };
}

fn remapBlockTarget(target: ir.BlockId, source_block: ir.BlockId, clone_block: ir.BlockId) ir.BlockId {
    return if (target == source_block) clone_block else target;
}

fn remapValuesAlloc(
    allocator: std.mem.Allocator,
    items: []const ir.ValueId,
    source_parameters: []const ir.ValueId,
    clone_parameters: []const ir.ValueId,
) std.mem.Allocator.Error![]const ir.ValueId {
    if (items.len == 0) return &.{};
    const mapped = try allocator.alloc(ir.ValueId, items.len);
    for (items, 0..) |item, index| mapped[index] = remapValue(item, source_parameters, clone_parameters);
    return mapped;
}

fn remapValue(value: ir.ValueId, source_parameters: []const ir.ValueId, clone_parameters: []const ir.ValueId) ir.ValueId {
    for (source_parameters, clone_parameters) |source, clone| if (value == source) return clone;
    return value;
}

fn mappedValueCapacity(program: *const ir.Program, block: ir.Block) ?usize {
    var capacity = block.parameters.len;
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return null;
        capacity = std.math.add(usize, capacity, program.instructions[instruction_id.index()].results.len) catch return null;
    }
    return capacity;
}

fn mappedPackCapacity(program: *const ir.Program, block: ir.Block) ?usize {
    var capacity: usize = 0;
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return null;
        if (program.instructions[instruction_id.index()].pack_result != null) {
            capacity = std.math.add(usize, capacity, 1) catch return null;
        }
    }
    return capacity;
}

fn sameMappedPackResult(
    program: *const ir.Program,
    function: ir.FunctionId,
    source_instruction: ir.InstructionId,
    clone_instruction: ir.InstructionId,
    source_maybe: ?ir.ValuePackId,
    clone_maybe: ?ir.ValuePackId,
    prior_source: []const ir.ValuePackId,
    prior_clone: []const ir.ValuePackId,
) bool {
    const source_id = source_maybe orelse return clone_maybe == null;
    const clone_id = clone_maybe orelse return false;
    if (source_id == clone_id or source_id.index() >= program.value_packs.len or clone_id.index() >= program.value_packs.len) return false;
    for (prior_source) |candidate| if (candidate == clone_id) return false;
    for (prior_clone) |candidate| if (candidate == source_id) return false;
    const source = program.value_packs[source_id.index()];
    const clone = program.value_packs[clone_id.index()];
    if (source.id != source_id or clone.id != clone_id or source.function != function or clone.function != function or
        !samePackShape(source.shape, clone.shape) or
        !std.mem.eql(ir.EvidenceId, source.evidence, clone.evidence)) return false;
    const source_producer = switch (source.origin) {
        .instruction_result => |instruction_id| instruction_id,
        .varargs => return false,
    };
    const clone_producer = switch (clone.origin) {
        .instruction_result => |instruction_id| instruction_id,
        .varargs => return false,
    };
    return source_producer == source_instruction and clone_producer == clone_instruction;
}

fn samePackShape(left: ir.PackShape, right: ir.PackShape) bool {
    if (left.tail != right.tail or left.prefix.len != right.prefix.len) return false;
    for (left.prefix, right.prefix) |left_type, right_type| if (!sameType(left_type, right_type)) return false;
    return true;
}

fn sameMappedTerminator(
    source: ir.Terminator,
    clone: ir.Terminator,
    source_block: ir.BlockId,
    clone_block: ir.BlockId,
    source_parameters: []const ir.ValueId,
    clone_parameters: []const ir.ValueId,
) bool {
    if (std.meta.activeTag(source) != std.meta.activeTag(clone)) return false;
    return switch (source) {
        .jump => |edge| sameMappedEdge(edge, clone.jump, source_block, clone_block, source_parameters, clone_parameters),
        .branch => |branch| remapValue(branch.condition, source_parameters, clone_parameters) == clone.branch.condition and
            sameMappedEdge(branch.then_edge, clone.branch.then_edge, source_block, clone_block, source_parameters, clone_parameters) and
            sameMappedEdge(branch.else_edge, clone.branch.else_edge, source_block, clone_block, source_parameters, clone_parameters),
        .return_values => |items| sameMappedValues(items, clone.return_values, source_parameters, clone_parameters),
        .return_pack => |pack| pack == clone.return_pack,
        .return_expanded => |expanded| expanded.pack == clone.return_expanded.pack and
            sameMappedValues(expanded.values, clone.return_expanded.values, source_parameters, clone_parameters),
        .throw_error => |throw_error| throw_error.level == clone.throw_error.level and
            remapValue(throw_error.value, source_parameters, clone_parameters) == clone.throw_error.value and
            sameMappedOptionalValue(throw_error.dynamic_level, clone.throw_error.dynamic_level, source_parameters, clone_parameters),
        .unreachable_block => true,
    };
}

fn sameMappedEdge(
    source: ir.Edge,
    clone: ir.Edge,
    source_block: ir.BlockId,
    clone_block: ir.BlockId,
    source_parameters: []const ir.ValueId,
    clone_parameters: []const ir.ValueId,
) bool {
    return remapBlockTarget(source.target, source_block, clone_block) == clone.target and
        sameMappedValues(source.arguments, clone.arguments, source_parameters, clone_parameters);
}

fn sameMappedValues(
    source: []const ir.ValueId,
    clone: []const ir.ValueId,
    source_parameters: []const ir.ValueId,
    clone_parameters: []const ir.ValueId,
) bool {
    if (source.len != clone.len) return false;
    for (source, clone) |source_value, clone_value| {
        if (remapValue(source_value, source_parameters, clone_parameters) != clone_value) return false;
    }
    return true;
}

fn sameMappedOptionalValue(
    source: ?ir.ValueId,
    clone: ?ir.ValueId,
    source_parameters: []const ir.ValueId,
    clone_parameters: []const ir.ValueId,
) bool {
    if (source == null or clone == null) return source == null and clone == null;
    return remapValue(source.?, source_parameters, clone_parameters) == clone.?;
}

fn sameOptionalString(left: ?[]const u8, right: ?[]const u8) bool {
    if (left == null or right == null) return left == null and right == null;
    return std.mem.eql(u8, left.?, right.?);
}

fn sameType(left: ir.ValueType, right: ir.ValueType) bool {
    return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed;
}
