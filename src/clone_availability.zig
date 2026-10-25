const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const cfg_edge = @import("cfg_edge.zig");
const runtime_uses = @import("runtime_uses.zig");
const build_options = @import("build_options");

const trace_clone_availability = build_options.trace_normalize_phases;

const ExternalMappings = struct {
    source_values: []const ir.ValueId,
    clone_values: []const ir.ValueId,
    source_packs: []const ir.ValuePackId,
    clone_packs: []const ir.ValuePackId,
};

const RootedDominance = struct {
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    block_ids: []const ir.BlockId,
    closure_indices: []?usize,
    roots: []bool,
    reachable: []bool,
    words_per_row: usize,
    rows: []usize,

    fn init(
        allocator: std.mem.Allocator,
        analysis: *const cfg.Analysis,
        block_ids: []const ir.BlockId,
        roots: []const ir.BlockId,
    ) std.mem.Allocator.Error!?RootedDominance {
        if (block_ids.len == 0 or roots.len == 0) return null;

        const closure_indices = try allocator.alloc(?usize, analysis.function.blocks.len);
        const root_bits = try allocator.alloc(bool, block_ids.len);
        const reachable = try allocator.alloc(bool, block_ids.len);
        const queue = try allocator.alloc(usize, block_ids.len);
        var committed = false;
        defer if (!committed) {
            allocator.free(queue);
            allocator.free(reachable);
            allocator.free(root_bits);
            allocator.free(closure_indices);
        };
        @memset(closure_indices, null);
        @memset(root_bits, false);
        @memset(reachable, false);

        for (block_ids, 0..) |block_id, block_index| {
            const local_index = analysis.blockIndex(block_id) orelse return null;
            if (block_id.index() >= analysis.program.blocks.len or
                analysis.program.blocks[block_id.index()].id != block_id or
                analysis.program.blocks[block_id.index()].function != analysis.function.id or
                closure_indices[local_index] != null)
            {
                return null;
            }
            closure_indices[local_index] = block_index;
        }

        for (roots) |root| {
            const closure_index = closureIndexFor(closure_indices, analysis, root) orelse return null;
            if (!analysis.isReachable(root)) return null;
            root_bits[closure_index] = true;
        }

        var queue_len: usize = 0;
        for (root_bits, 0..) |is_root, index| if (is_root) {
            reachable[index] = true;
            queue[queue_len] = index;
            queue_len += 1;
        };
        var queue_index: usize = 0;
        while (queue_index < queue_len) : (queue_index += 1) {
            const current = block_ids[queue[queue_index]];
            for (0..analysis.successorCount(current)) |successor_index| {
                const successor = analysis.successorAt(current, successor_index) orelse return null;
                const closure_index = closureIndexFor(closure_indices, analysis, successor) orelse continue;
                if (reachable[closure_index]) continue;
                reachable[closure_index] = true;
                queue[queue_len] = closure_index;
                queue_len += 1;
            }
        }
        allocator.free(queue);

        const word_bits = @bitSizeOf(usize);
        const words_per_row = (block_ids.len + word_bits - 1) / word_bits;
        const row_count = std.math.mul(usize, block_ids.len, words_per_row) catch return null;
        const rows = try allocator.alloc(usize, row_count);
        @memset(rows, 0);

        var result: RootedDominance = .{
            .allocator = allocator,
            .analysis = analysis,
            .block_ids = block_ids,
            .closure_indices = closure_indices,
            .roots = root_bits,
            .reachable = reachable,
            .words_per_row = words_per_row,
            .rows = rows,
        };
        errdefer result.deinit();

        for (0..block_ids.len) |block_index| {
            if (!reachable[block_index]) continue;
            if (root_bits[block_index]) {
                setBit(result.row(block_index), block_index);
            } else {
                for (reachable, 0..) |is_reachable, candidate| if (is_reachable) {
                    setBit(result.row(block_index), candidate);
                };
            }
        }

        const scratch = try allocator.alloc(usize, words_per_row);
        defer allocator.free(scratch);
        var changed = true;
        while (changed) {
            changed = false;
            for (0..block_ids.len) |block_index| {
                if (!reachable[block_index] or root_bits[block_index]) continue;
                @memset(scratch, 0);
                var has_predecessor = false;
                var predecessor_index: usize = 0;
                while (analysis.predecessorAt(block_ids[block_index], predecessor_index)) |predecessor| : (predecessor_index += 1) {
                    const predecessor_closure_index = result.closureIndex(predecessor) orelse continue;
                    if (!reachable[predecessor_closure_index]) continue;
                    if (!has_predecessor) {
                        @memcpy(scratch, result.row(predecessor_closure_index));
                        has_predecessor = true;
                    } else {
                        for (scratch, result.row(predecessor_closure_index)) |*left, right| left.* &= right;
                    }
                }
                if (!has_predecessor) return null;
                setBit(scratch, block_index);
                const current_row = result.row(block_index);
                if (!std.mem.eql(usize, current_row, scratch)) {
                    @memcpy(current_row, scratch);
                    changed = true;
                }
            }
        }

        committed = true;
        return result;
    }

    fn deinit(self: *RootedDominance) void {
        self.allocator.free(self.rows);
        self.allocator.free(self.reachable);
        self.allocator.free(self.roots);
        self.allocator.free(self.closure_indices);
        self.* = undefined;
    }

    fn closureIndex(self: *const RootedDominance, block_id: ir.BlockId) ?usize {
        return closureIndexFor(self.closure_indices, self.analysis, block_id);
    }

    fn row(self: *RootedDominance, block_index: usize) []usize {
        return self.rows[block_index * self.words_per_row ..][0..self.words_per_row];
    }

    fn dominates(self: *const RootedDominance, producer: ir.BlockId, use: ir.BlockId) bool {
        const producer_index = self.closureIndex(producer) orelse return false;
        const use_index = self.closureIndex(use) orelse return false;
        if (!self.reachable[producer_index] or !self.reachable[use_index]) return false;
        return bitIsSet(self.rows[use_index * self.words_per_row ..][0..self.words_per_row], producer_index);
    }

    fn reachableBlock(self: *const RootedDominance, block_id: ir.BlockId) bool {
        const block_index = self.closureIndex(block_id) orelse return false;
        return self.reachable[block_index];
    }
};

fn closureIndexFor(
    closure_indices: []const ?usize,
    analysis: *const cfg.Analysis,
    block_id: ir.BlockId,
) ?usize {
    const local_index = analysis.blockIndex(block_id) orelse return null;
    if (local_index >= closure_indices.len) return null;
    return closure_indices[local_index];
}

fn setBit(row: []usize, bit_index: usize) void {
    const word_bits = @bitSizeOf(usize);
    row[bit_index / word_bits] |= @as(usize, 1) << @intCast(bit_index % word_bits);
}

fn bitIsSet(row: []const usize, bit_index: usize) bool {
    const word_bits = @bitSizeOf(usize);
    return (row[bit_index / word_bits] & (@as(usize, 1) << @intCast(bit_index % word_bits))) != 0;
}

const UseVisitor = struct {
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    dominance: *const RootedDominance,
    instruction_positions: []const ?usize,
    external_mappings: ExternalMappings,
    use_block: ir.BlockId,
    use_position: usize,
    valid: bool = true,
    failure_value: ?ir.ValueId = null,
    failure_pack: ?ir.ValuePackId = null,
    failure_place: ?ir.PlaceId = null,
    failure_producer: ?ir.BlockId = null,
    failure_producer_reachable: bool = false,
    failure_use_reachable: bool = false,
    failure_dominates: bool = false,

    pub fn value(self: *UseVisitor, value_id: ir.ValueId) void {
        if (!self.valueAvailable(value_id)) {
            self.valid = false;
            if (self.failure_value == null) self.failure_value = value_id;
        }
    }

    pub fn pack(self: *UseVisitor, pack_id: ir.ValuePackId) void {
        if (!self.packAvailable(pack_id)) {
            self.valid = false;
            if (self.failure_pack == null) self.failure_pack = pack_id;
        }
    }

    pub fn place(self: *UseVisitor, place_id: ir.PlaceId) void {
        if (!self.placeAvailable(place_id)) {
            self.valid = false;
            if (self.failure_place == null) self.failure_place = place_id;
        }
    }

    fn valueAvailable(self: *const UseVisitor, value_id: ir.ValueId) bool {
        if (value_id.index() >= self.program.values.len) return false;
        const value_data = self.program.values[value_id.index()];
        if (value_data.id != value_id or value_data.function != self.analysis.function.id) return false;
        switch (value_data.origin) {
            .parameter, .capture => return true,
            .block_parameter => |origin| {
                if (origin.block.index() >= self.program.blocks.len) return false;
                const definition_block = self.program.blocks[origin.block.index()];
                const parameter_index: usize = @intCast(origin.index);
                if (definition_block.id != origin.block or
                    definition_block.function != self.analysis.function.id or
                    parameter_index >= definition_block.parameters.len or
                    definition_block.parameters[parameter_index] != value_id)
                {
                    return false;
                }
                if (self.dominance.closureIndex(origin.block) == null) {
                    return self.hasExternalValueMapping(value_id);
                }
                const available = self.blockAvailable(origin.block);
                return available;
            },
            .instruction_result => |origin| {
                if (origin.instruction.index() >= self.program.instructions.len) return false;
                const definition = self.program.instructions[origin.instruction.index()];
                const result_index: usize = @intCast(origin.index);
                if (definition.id != origin.instruction or
                    definition.block.index() >= self.program.blocks.len or
                    result_index >= definition.results.len or
                    definition.results[result_index] != value_id)
                {
                    return false;
                }
                if (self.dominance.closureIndex(definition.block) == null) {
                    return self.hasExternalValueMapping(value_id);
                }
                if (definition.block == self.use_block) {
                    return instructionPrecedesUse(
                        self.instruction_positions,
                        origin.instruction,
                        self.use_position,
                    );
                }
                const available = self.blockAvailable(definition.block);
                return available;
            },
        }
    }

    fn packAvailable(self: *const UseVisitor, pack_id: ir.ValuePackId) bool {
        if (pack_id.index() >= self.program.value_packs.len) return false;
        const pack_data = self.program.value_packs[pack_id.index()];
        if (pack_data.id != pack_id or pack_data.function != self.analysis.function.id) return false;
        switch (pack_data.origin) {
            .varargs => return true,
            .instruction_result => |instruction_id| {
                if (instruction_id.index() >= self.program.instructions.len) return false;
                const definition = self.program.instructions[instruction_id.index()];
                if (definition.id != instruction_id or definition.pack_result != pack_id or
                    definition.block.index() >= self.program.blocks.len)
                {
                    return false;
                }
                if (self.dominance.closureIndex(definition.block) == null) {
                    return self.hasExternalPackMapping(pack_id);
                }
                if (definition.block == self.use_block) {
                    return instructionPrecedesUse(self.instruction_positions, instruction_id, self.use_position);
                }
                return self.blockAvailable(definition.block);
            },
        }
    }

    fn hasExternalValueMapping(self: *const UseVisitor, value_id: ir.ValueId) bool {
        for (self.external_mappings.source_values) |source| {
            if (source == value_id) return true;
        }
        return false;
    }

    fn hasExternalPackMapping(self: *const UseVisitor, pack_id: ir.ValuePackId) bool {
        for (self.external_mappings.source_packs) |source| {
            if (source == pack_id) return true;
        }
        return false;
    }

    fn placeAvailable(self: *const UseVisitor, place_id: ir.PlaceId) bool {
        if (place_id.index() >= self.program.places.len) return false;
        const place_data = self.program.places[place_id.index()];
        if (place_data.id != place_id or place_data.function != self.analysis.function.id) return false;
        switch (place_data.origin) {
            .local, .capture => return true,
            .instruction => |instruction_id| {
                if (instruction_id.index() >= self.program.instructions.len) return false;
                const definition = self.program.instructions[instruction_id.index()];
                if (definition.id != instruction_id or definition.block.index() >= self.program.blocks.len) return false;
                if (self.dominance.closureIndex(definition.block) == null) return true;
                if (definition.block == self.use_block) {
                    return instructionPrecedesUse(self.instruction_positions, instruction_id, self.use_position);
                }
                return self.blockAvailable(definition.block);
            },
        }
    }

    fn blockAvailable(self: *const UseVisitor, producer: ir.BlockId) bool {
        const producer_reachable = self.dominance.reachableBlock(producer);
        const use_reachable = self.dominance.reachableBlock(self.use_block);
        const dominates = producer_reachable and use_reachable and
            self.dominance.dominates(producer, self.use_block);
        if (!producer_reachable or !use_reachable or !dominates) {
            const mutable = @constCast(self);
            mutable.failure_producer = producer;
            mutable.failure_producer_reachable = producer_reachable;
            mutable.failure_use_reachable = use_reachable;
            mutable.failure_dominates = dominates;
        }
        return dominates;
    }
};

fn instructionPrecedesUse(
    instruction_positions: []const ?usize,
    instruction_id: ir.InstructionId,
    use_position: usize,
) bool {
    if (instruction_id.index() >= instruction_positions.len) return false;
    const definition_position = instruction_positions[instruction_id.index()] orelse return false;
    return definition_position < use_position;
}

fn usesAreAvailableFromRoots(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    block_ids: []const ir.BlockId,
    roots: []const ir.BlockId,
    require_all_blocks_reachable: bool,
    external_mappings: ExternalMappings,
) std.mem.Allocator.Error!bool {
    var dominance = (try RootedDominance.init(allocator, analysis, block_ids, roots)) orelse return false;
    defer dominance.deinit();

    if (require_all_blocks_reachable) {
        for (block_ids) |block_id| {
            if (!dominance.reachableBlock(block_id)) {
                if (trace_clone_availability and block_ids.len >= 100) {
                    var has_4057 = false;
                    for (block_ids) |member| {
                        if (member.index() == 4057) has_4057 = true;
                    }
                    std.debug.print("clone_availability_unreachable block={} roots={any} closure={} blocks={any}\n", .{
                        block_id.index(),
                        roots,
                        block_ids.len,
                        block_ids,
                    });
                    std.debug.print("clone_availability_membership block_4057={}\n", .{has_4057});
                }
                return false;
            }
        }
    }

    if (external_mappings.source_values.len != external_mappings.clone_values.len or
        external_mappings.source_packs.len != external_mappings.clone_packs.len)
    {
        return false;
    }
    for (external_mappings.source_values, external_mappings.clone_values) |source, clone| {
        if (!valuePairIsCanonical(program, analysis.function.id, source, clone)) return false;
    }
    for (external_mappings.source_packs, external_mappings.clone_packs) |source, clone| {
        if (!packPairIsCanonical(program, analysis.function.id, source, clone)) return false;
    }

    const instruction_positions = try allocator.alloc(?usize, program.instructions.len);
    defer allocator.free(instruction_positions);
    @memset(instruction_positions, null);
    for (block_ids) |block_id| {
        if (block_id.index() >= program.blocks.len) return false;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id or block.function != analysis.function.id) return false;
        for (block.instructions, 0..) |instruction_id, position| {
            if (instruction_id.index() >= program.instructions.len or
                instruction_positions[instruction_id.index()] != null)
            {
                return false;
            }
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or instruction.block != block_id) return false;
            instruction_positions[instruction_id.index()] = position;
        }
    }

    for (block_ids) |block_id| {
        if (!dominance.reachableBlock(block_id)) continue;
        const block = program.blocks[block_id.index()];
        for (block.instructions, 0..) |instruction_id, position| {
            const instruction = program.instructions[instruction_id.index()];
            var visitor = UseVisitor{
                .program = program,
                .analysis = analysis,
                .dominance = &dominance,
                .instruction_positions = instruction_positions,
                .external_mappings = external_mappings,
                .use_block = block_id,
                .use_position = position,
            };
            runtime_uses.visitOperationUses(instruction.operation, &visitor);
            if (!visitor.valid) {
                if (trace_clone_availability and block_ids.len >= 100) {
                    const global_dominates = if (visitor.failure_producer) |producer|
                        visitor.analysis.dominates(producer, block_id)
                    else
                        false;
                    const rooted_producer_index = if (visitor.failure_producer) |producer|
                        dominance.closureIndex(producer)
                    else
                        null;
                    const rooted_use_index = dominance.closureIndex(block_id);
                    const rooted_producer = if (rooted_producer_index) |index|
                        dominance.roots[index]
                    else
                        false;
                    const rooted_use = if (rooted_use_index) |index|
                        dominance.roots[index]
                    else
                        false;
                    std.debug.print("clone_availability_reject block={} instruction={} value={?d} pack={?d} place={?d} producer={?d} producer_reachable={} use_reachable={} dominates={}\n", .{
                        block_id.index(),
                        instruction_id.index(),
                        visitor.failure_value,
                        visitor.failure_pack,
                        visitor.failure_place,
                        visitor.failure_producer,
                        visitor.failure_producer_reachable,
                        visitor.failure_use_reachable,
                        visitor.failure_dominates,
                    });
                    std.debug.print("clone_availability_root_state producer_index={?d} use_index={?d} producer_root={} use_root={} closure_len={} roots={any}\n", .{
                        rooted_producer_index,
                        rooted_use_index,
                        rooted_producer,
                        rooted_use,
                        block_ids.len,
                        block_ids,
                    });
                    std.debug.print("clone_availability_global_dominates block={} producer={?d} result={} function_blocks={}\n", .{
                        block_id.index(),
                        visitor.failure_producer,
                        global_dominates,
                        visitor.analysis.function.blocks.len,
                    });
                }
                return false;
            }
        }
        var visitor = UseVisitor{
            .program = program,
            .analysis = analysis,
            .dominance = &dominance,
            .instruction_positions = instruction_positions,
            .external_mappings = external_mappings,
            .use_block = block_id,
            .use_position = block.instructions.len,
        };
        runtime_uses.visitTerminatorUses(block.terminator, &visitor);
        if (!visitor.valid) {
            if (trace_clone_availability and block_ids.len >= 100) {
                const global_dominates = if (visitor.failure_producer) |producer|
                    visitor.analysis.dominates(producer, block_id)
                else
                    false;
                const rooted_producer_index = if (visitor.failure_producer) |producer|
                    dominance.closureIndex(producer)
                else
                    null;
                const rooted_use_index = dominance.closureIndex(block_id);
                const rooted_producer = if (rooted_producer_index) |index|
                    dominance.roots[index]
                else
                    false;
                const rooted_use = if (rooted_use_index) |index|
                    dominance.roots[index]
                else
                    false;
                std.debug.print("clone_availability_reject block={} terminator value={?d} pack={?d} place={?d} producer={?d} producer_reachable={} use_reachable={} dominates={}\n", .{
                    block_id.index(),
                    visitor.failure_value,
                    visitor.failure_pack,
                    visitor.failure_place,
                    visitor.failure_producer,
                    visitor.failure_producer_reachable,
                    visitor.failure_use_reachable,
                    visitor.failure_dominates,
                });
                std.debug.print("clone_availability_root_state producer_index={?d} use_index={?d} producer_root={} use_root={} closure_len={} roots={any}\n", .{
                    rooted_producer_index,
                    rooted_use_index,
                    rooted_producer,
                    rooted_use,
                    block_ids.len,
                    block_ids,
                });
                std.debug.print("clone_availability_global_dominates block={} producer={?d} result={} function_blocks={}\n", .{
                    block_id.index(),
                    visitor.failure_producer,
                    global_dominates,
                    visitor.analysis.function.blocks.len,
                });
            }
            return false;
        }
    }
    return true;
}

pub fn cloneClosureUsesAreAvailable(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    external_source_values: []const ir.ValueId,
    external_clone_values: []const ir.ValueId,
    external_source_packs: []const ir.ValuePackId,
    external_clone_packs: []const ir.ValuePackId,
) std.mem.Allocator.Error!bool {
    return cloneClosureUsesAreAvailableWithRootPolicy(
        allocator,
        program,
        analysis,
        closure,
        incoming,
        external_source_values,
        external_clone_values,
        external_source_packs,
        external_clone_packs,
        .source_if_internal,
    );
}

// A complete authenticated SCC is entered at the incoming edge target.  Its
// selected source may also be a member of the SCC, but it is not the cloned
// entry.  Rooting at that source admits paths that bypass the target's
// block-parameter state.  Ordinary continuation splits retain the historical
// source-root behavior through cloneClosureUsesAreAvailable above.
pub fn cloneClosureUsesAreAvailableFromTargets(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    external_source_values: []const ir.ValueId,
    external_clone_values: []const ir.ValueId,
    external_source_packs: []const ir.ValuePackId,
    external_clone_packs: []const ir.ValuePackId,
) std.mem.Allocator.Error!bool {
    return cloneClosureUsesAreAvailableWithRootPolicy(
        allocator,
        program,
        analysis,
        closure,
        incoming,
        external_source_values,
        external_clone_values,
        external_source_packs,
        external_clone_packs,
        .target,
    );
}

const RootPolicy = enum {
    source_if_internal,
    target,
};

fn cloneClosureUsesAreAvailableWithRootPolicy(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    closure: []const ir.BlockId,
    incoming: []const ir.CfgEdgeRef,
    external_source_values: []const ir.ValueId,
    external_clone_values: []const ir.ValueId,
    external_source_packs: []const ir.ValuePackId,
    external_clone_packs: []const ir.ValuePackId,
    root_policy: RootPolicy,
) std.mem.Allocator.Error!bool {
    if (closure.len == 0 or incoming.len == 0) return false;
    const roots = try allocator.alloc(ir.BlockId, incoming.len);
    defer allocator.free(roots);
    for (incoming, 0..) |reference, index| {
        if (!incomingEdgeIsCanonical(program, analysis, reference)) return false;
        roots[index] = reference.target;
        if (root_policy == .source_if_internal) {
            // A continuation edge may start inside the proposed closure.  In
            // that shape the source is the closure entry; rooting only at the
            // target makes the source block parameters appear unreachable.
            for (closure) |block_id| {
                if (block_id == reference.source) {
                    roots[index] = reference.source;
                    break;
                }
            }
        }
    }
    return usesAreAvailableFromRoots(allocator, program, analysis, closure, roots, true, .{
        .source_values = external_source_values,
        .clone_values = external_clone_values,
        .source_packs = external_source_packs,
        .clone_packs = external_clone_packs,
    });
}

pub fn functionUsesAreAvailable(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
) std.mem.Allocator.Error!bool {
    return usesAreAvailableFromRoots(
        allocator,
        program,
        analysis,
        analysis.function.blocks,
        &.{analysis.function.entry_block},
        false,
        .{
            .source_values = &.{},
            .clone_values = &.{},
            .source_packs = &.{},
            .clone_packs = &.{},
        },
    );
}

/// The owner-side and clone-side identities a clone fold renames, position by position. A pair whose two sides are
/// equal renames nothing.
pub const RenamedPairs = struct {
    source_values: []const ir.ValueId = &.{},
    clone_values: []const ir.ValueId = &.{},
    source_packs: []const ir.ValuePackId = &.{},
    clone_packs: []const ir.ValuePackId = &.{},
};

const FoldUseCollector = struct {
    allocator: std.mem.Allocator,
    values: *std.ArrayList(ir.ValueId),
    packs: *std.ArrayList(ir.ValuePackId),
    out_of_memory: *bool,

    pub fn value(self: *FoldUseCollector, value_id: ir.ValueId) void {
        self.values.append(self.allocator, value_id) catch {
            self.out_of_memory.* = true;
        };
    }

    pub fn pack(self: *FoldUseCollector, pack_id: ir.ValuePackId) void {
        self.packs.append(self.allocator, pack_id) catch {
            self.out_of_memory.* = true;
        };
    }

    pub fn place(_: *FoldUseCollector, _: ir.PlaceId) void {}
};

// Both sides of every pair whose two sides differ: the identities a fold renames.
fn putRenamedSides(allocator: std.mem.Allocator, set: anytype, sources: anytype, clones: anytype) std.mem.Allocator.Error!void {
    for (sources, clones) |source, clone| {
        if (source == clone) continue;
        try set.put(allocator, source, {});
        try set.put(allocator, clone, {});
    }
}

fn foldValueDefinitionBlock(program: *const ir.Program, value_id: ir.ValueId) ?ir.BlockId {
    if (value_id.index() >= program.values.len) return null;
    return switch (program.values[value_id.index()].origin) {
        .parameter, .capture => null,
        .block_parameter => |origin| origin.block,
        .instruction_result => |origin| if (origin.instruction.index() < program.instructions.len)
            program.instructions[origin.instruction.index()].block
        else
            null,
    };
}

fn foldPackDefinitionBlock(program: *const ir.Program, pack_id: ir.ValuePackId) ?ir.BlockId {
    if (pack_id.index() >= program.value_packs.len) return null;
    return switch (program.value_packs[pack_id.index()].origin) {
        .varargs => null,
        .instruction_result => |instruction_id| if (instruction_id.index() < program.instructions.len)
            program.instructions[instruction_id.index()].block
        else
            null,
    };
}

/// A clone fold redirects an edge from a node-split clone to the clone's owner block. The replay mapping that
/// authenticates the fold pairs each owner-side identity with its clone-side identity (the clone is the owner's
/// image under that renaming). After the redirect the owner side runs where the clone side ran, so it reads the
/// owner-side identity of every renamed value where the clone read the clone-side one; the two hold the same runtime
/// value only if neither identity of a renamed pair is live on entry to the owner. A use is live when the owner
/// reaches its block without passing the value's defining block; a value the owner defines is not. `analysis` is
/// the function's graph after the redirect.
pub fn foldRenamedValuesAreDead(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    owner: ir.BlockId,
    renamed: RenamedPairs,
) std.mem.Allocator.Error!bool {
    if (renamed.source_values.len != renamed.clone_values.len or renamed.source_packs.len != renamed.clone_packs.len) return false;
    var renamed_values: std.AutoHashMapUnmanaged(ir.ValueId, void) = .empty;
    defer renamed_values.deinit(allocator);
    try putRenamedSides(allocator, &renamed_values, renamed.source_values, renamed.clone_values);
    var renamed_packs: std.AutoHashMapUnmanaged(ir.ValuePackId, void) = .empty;
    defer renamed_packs.deinit(allocator);
    try putRenamedSides(allocator, &renamed_packs, renamed.source_packs, renamed.clone_packs);
    var used_values: std.ArrayList(ir.ValueId) = .empty;
    defer used_values.deinit(allocator);
    var used_packs: std.ArrayList(ir.ValuePackId) = .empty;
    defer used_packs.deinit(allocator);
    var out_of_memory = false;
    for (analysis.function.blocks) |use_block| {
        if (use_block.index() >= program.blocks.len or !analysis.isReachable(use_block)) continue;
        used_values.clearRetainingCapacity();
        used_packs.clearRetainingCapacity();
        var collector = FoldUseCollector{
            .allocator = allocator,
            .values = &used_values,
            .packs = &used_packs,
            .out_of_memory = &out_of_memory,
        };
        const block = program.blocks[use_block.index()];
        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) return false;
            runtime_uses.visitOperationUses(program.instructions[instruction_id.index()].operation, &collector);
        }
        runtime_uses.visitTerminatorUses(block.terminator, &collector);
        if (out_of_memory) return error.OutOfMemory;
        for (used_values.items) |value_id| {
            if (!renamed_values.contains(value_id)) continue;
            const definition = foldValueDefinitionBlock(program, value_id) orelse continue;
            // canReachAvoiding is false when the owner or the use block is the definition block: a value the
            // owner defines, or one read only after its own block redefines it, is not live on entry.
            if (try analysis.canReachAvoiding(owner, use_block, definition)) {
                if (trace_clone_availability) std.debug.print("clone_fold_renamed_live owner={} value={} definition={} use={}\n", .{
                    owner.index(),
                    value_id.index(),
                    definition.index(),
                    use_block.index(),
                });
                return false;
            }
        }
        for (used_packs.items) |pack_id| {
            if (!renamed_packs.contains(pack_id)) continue;
            const definition = foldPackDefinitionBlock(program, pack_id) orelse continue;
            if (try analysis.canReachAvoiding(owner, use_block, definition)) return false;
        }
    }
    return true;
}

fn valuePairIsCanonical(
    program: *const ir.Program,
    function_id: ir.FunctionId,
    source: ir.ValueId,
    clone: ir.ValueId,
) bool {
    if (source.index() >= program.values.len or clone.index() >= program.values.len) return false;
    const source_data = program.values[source.index()];
    const clone_data = program.values[clone.index()];
    return source_data.id == source and clone_data.id == clone and
        source_data.function == function_id and clone_data.function == function_id;
}

fn packPairIsCanonical(
    program: *const ir.Program,
    function_id: ir.FunctionId,
    source: ir.ValuePackId,
    clone: ir.ValuePackId,
) bool {
    if (source.index() >= program.value_packs.len or clone.index() >= program.value_packs.len) return false;
    const source_data = program.value_packs[source.index()];
    const clone_data = program.value_packs[clone.index()];
    return source_data.id == source and clone_data.id == clone and
        source_data.function == function_id and clone_data.function == function_id;
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

test "complete internal SCC availability roots at the cloned target" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const source = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const consumer = ir.BlockId.fromIndex(3);
    const selector = ir.ValueId.fromIndex(0);
    const produced = ir.ValueId.fromIndex(1);
    const definition = ir.InstructionId.fromIndex(0);

    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = source, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = target },
            .else_edge = .{ .target = consumer },
        } } },
        .{ .id = target, .function = function_id, .instructions = &.{definition}, .terminator = .{ .jump = .{ .target = source } } },
        .{ .id = consumer, .function = function_id, .terminator = .{ .return_values = &.{produced} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{selector},
        .blocks = &.{ entry, source, target, consumer },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = produced, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = definition, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = definition,
        .block = target,
        .operation = .{ .constant = .{ .number = 7 } },
        .results = &.{produced},
        .effects = .pure,
    }};
    const program = ir.Program{
        .program_id = "complete-scc-target-root-availability",
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
        .target = target,
    }};
    const closure = [_]ir.BlockId{ target, source, consumer };

    try std.testing.expect(!(try cloneClosureUsesAreAvailable(
        std.testing.allocator,
        &program,
        &analysis,
        &closure,
        &incoming,
        &.{},
        &.{},
        &.{},
        &.{},
    )));
    try std.testing.expect(try cloneClosureUsesAreAvailableFromTargets(
        std.testing.allocator,
        &program,
        &analysis,
        &closure,
        &incoming,
        &.{},
        &.{},
        &.{},
        &.{},
    ));
}

test "clone closure availability requires an authenticated external mapping" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const producer = ir.BlockId.fromIndex(1);
    const target = ir.BlockId.fromIndex(2);
    const use = ir.BlockId.fromIndex(3);
    const selector = ir.ValueId.fromIndex(0);
    const produced = ir.ValueId.fromIndex(1);
    const boundary = ir.ValueId.fromIndex(2);
    const definition = ir.InstructionId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = selector,
            .then_edge = .{ .target = producer },
            .else_edge = .{ .target = target },
        } } },
        .{ .id = producer, .function = function_id, .instructions = &.{definition}, .terminator = .{ .jump = .{ .target = use } } },
        .{ .id = target, .function = function_id, .terminator = .{ .jump = .{ .target = use } } },
        .{ .id = use, .function = function_id, .terminator = .{ .return_values = &.{produced} } },
    };
    const function = ir.Function{
        .id = function_id,
        .parameters = &.{ selector, boundary },
        .blocks = &.{ entry, producer, target, use },
        .entry_block = entry,
    };
    const values = [_]ir.Value{
        .{ .id = selector, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = produced, .function = function_id, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = definition, .index = 0 } } },
        .{ .id = boundary, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = definition,
        .block = producer,
        .operation = .{ .constant = .{ .number = 1 } },
        .results = &.{produced},
        .effects = .pure,
    }};
    const program = ir.Program{
        .program_id = "clone-availability-root",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var analysis = try cfg.Analysis.init(std.testing.allocator, &program, function);
    defer analysis.deinit();
    const incoming = [_]ir.CfgEdgeRef{.{ .source = entry, .kind = .branch_else, .target = target }};
    const closure = [_]ir.BlockId{ target, use };
    try std.testing.expect(!(try cloneClosureUsesAreAvailable(
        std.testing.allocator,
        &program,
        &analysis,
        &closure,
        &incoming,
        &.{},
        &.{},
        &.{},
        &.{},
    )));
    try std.testing.expect(try cloneClosureUsesAreAvailable(
        std.testing.allocator,
        &program,
        &analysis,
        &closure,
        &incoming,
        &.{produced},
        &.{boundary},
        &.{},
        &.{},
    ));
    const disconnected = [_]ir.BlockId{ target, producer, use };
    try std.testing.expect(!(try cloneClosureUsesAreAvailable(
        std.testing.allocator,
        &program,
        &analysis,
        &disconnected,
        &incoming,
        &.{produced},
        &.{boundary},
        &.{},
        &.{},
    )));
}
