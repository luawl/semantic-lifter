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
