const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const structure = @import("structure.zig");
const iteration_protocol = @import("iteration_protocol.zig");
const natural_loop = @import("natural_loop.zig");
const irreducible_region = @import("irreducible_region.zig");
const runtime_uses = @import("runtime_uses.zig");
const runtime_value_rewrite = @import("runtime_value_rewrite.zig");

const LoopId = usize;
const invalid_loop = std.math.maxInt(LoopId);
const invalid_region = std.math.maxInt(usize);

const LoopInfo = struct {
    parent: LoopId,
    header: ir.BlockId,
    depth: usize,
    matched_iteration: bool,
};

pub const Transfer = struct {
    value: ir.ValueId,
    loop: LoopId,
};

pub const Alias = struct {
    value: ir.ValueId,
    replacement: ir.ValueId,
    loop: LoopId,
};

/// Selects the innermost structured loop crossed by each reachable runtime
/// value use. Native-loop protocol bindings remain blockers, while standalone
/// semantic-normalized numeric transitions use their explicit statement form.
pub const Plan = struct {
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function: ir.Function,
    loops: []LoopInfo,
    block_loops: []LoopId,
    transfers: []Transfer,
    aliases: []Alias,
    unsupported_values: []ir.ValueId,

    pub fn init(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        function: ir.Function,
        analysis: *const cfg.Analysis,
        structured: *const structure.Plan,
    ) !Plan {
        var fact_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        defer fact_arena.deinit();
        const no_aliases: []const ir.ValueId = &.{};
        const no_excluded_instructions: []const bool = &.{};
        var uses = try runtime_uses.Counts.initFunction(
            fact_arena.allocator(),
            program,
            analysis,
            no_aliases,
            no_excluded_instructions,
        );
        defer uses.deinit();
        return initWithRuntimeUses(allocator, program, function, analysis, structured, &uses);
    }

    pub fn initWithRuntimeUses(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        function: ir.Function,
        analysis: *const cfg.Analysis,
        structured: *const structure.Plan,
        uses: *const runtime_uses.Counts,
    ) !Plan {
        const block_loops = try allocator.alloc(LoopId, program.blocks.len);
        errdefer allocator.free(block_loops);
        @memset(block_loops, invalid_loop);

        var loops: std.ArrayList(LoopInfo) = .empty;
        defer loops.deinit(allocator);
        try indexRegion(allocator, &loops, block_loops, structured.root, invalid_loop);
        const owned_loops = try loops.toOwnedSlice(allocator);
        errdefer allocator.free(owned_loops);

        var aliases: std.ArrayList(Alias) = .empty;
        defer aliases.deinit(allocator);
        try collectIterationAliases(
            allocator,
            program,
            analysis,
            structured.root,
            owned_loops,
            block_loops,
            &aliases,
            uses,
        );
        const owned_aliases = try aliases.toOwnedSlice(allocator);
        errdefer allocator.free(owned_aliases);

        const selected = try allocator.alloc(LoopId, program.values.len);
        defer allocator.free(selected);
        @memset(selected, invalid_loop);
        const unsupported = try allocator.alloc(bool, program.values.len);
        defer allocator.free(unsupported);
        @memset(unsupported, false);

        var builder: Builder = .{
            .program = program,
            .function = function,
            .loops = owned_loops,
            .block_loops = block_loops,
            .selected = selected,
            .unsupported = unsupported,
        };
        for (function.blocks) |block_id| {
            if (block_id.index() >= program.blocks.len or !analysis.isReachable(block_id)) continue;
            const block = program.blocks[block_id.index()];
            const visitor = UseVisitor{ .builder = &builder, .block = block_id };
            for (block.instructions) |instruction_id| {
                if (instruction_id.index() >= program.instructions.len) continue;
                runtime_uses.visitOperationUses(program.instructions[instruction_id.index()].operation, visitor);
            }
            runtime_uses.visitTerminatorUses(block.terminator, visitor);
        }

        var transfers: std.ArrayList(Transfer) = .empty;
        defer transfers.deinit(allocator);
        var unsupported_values: std.ArrayList(ir.ValueId) = .empty;
        defer unsupported_values.deinit(allocator);
        for (program.values) |value| {
            if (value.function != function.id or value.id.index() >= selected.len) continue;
            if (selected[value.id.index()] != invalid_loop) {
                try transfers.append(allocator, .{ .value = value.id, .loop = selected[value.id.index()] });
            }
            if (unsupported[value.id.index()]) try unsupported_values.append(allocator, value.id);
        }

        const owned_transfers = try transfers.toOwnedSlice(allocator);
        errdefer allocator.free(owned_transfers);
        const owned_unsupported_values = try unsupported_values.toOwnedSlice(allocator);
        errdefer allocator.free(owned_unsupported_values);

        return .{
            .allocator = allocator,
            .program = program,
            .function = function,
            .loops = owned_loops,
            .block_loops = block_loops,
            .transfers = owned_transfers,
            .aliases = owned_aliases,
            .unsupported_values = owned_unsupported_values,
        };
    }

    pub fn deinit(self: *Plan) void {
        self.allocator.free(self.unsupported_values);
        self.allocator.free(self.aliases);
        self.allocator.free(self.transfers);
        self.allocator.free(self.block_loops);
        self.allocator.free(self.loops);
        self.* = undefined;
    }

    pub fn isOutside(self: *const Plan, transfer: Transfer, block_id: ir.BlockId) bool {
        return !self.blockInsideLoop(block_id, transfer.loop);
    }

    pub fn aliasIsOutside(self: *const Plan, alias: Alias, block_id: ir.BlockId) bool {
        return !self.blockInsideLoop(block_id, alias.loop);
    }

    fn blockInsideLoop(self: *const Plan, block_id: ir.BlockId, target: LoopId) bool {
        if (block_id.index() >= self.block_loops.len or target >= self.loops.len) return false;
        var current = self.block_loops[block_id.index()];
        while (current != invalid_loop) {
            if (current == target) return true;
            if (current >= self.loops.len) return false;
            current = self.loops[current].parent;
        }
        return false;
    }
};

fn collectIterationAliases(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    region: *const structure.Region,
    loops: []LoopInfo,
    block_loops: []const LoopId,
    aliases: *std.ArrayList(Alias),
    uses: *const runtime_uses.Counts,
) std.mem.Allocator.Error!void {
    for (region.nodes) |node| switch (node) {
        .block, .loop_control, .loop_terminal => {},
        .branch => |branch| {
            try collectIterationAliases(allocator, program, analysis, branch.then_region, loops, block_loops, aliases, uses);
            try collectIterationAliases(allocator, program, analysis, branch.else_region, loops, block_loops, aliases, uses);
        },
        .loop => |loop| {
            const loop_id = findLoopByHeader(loops, loop.header);
            if (loop_id) |id| {
                const matched = try iteration_protocol.matchLoopWithContext(program, analysis, uses, loop);
                if (matched != null) loops[id].matched_iteration = true;
                if (matched) |match| switch (match) {
                    .numeric => |numeric| {
                        if (numeric.transition.results.len == 4 and numeric.initial_arguments.len == 4) {
                            const results = numeric.transition.results[1..3];
                            const replacements = numeric.initial_arguments[1..3];
                            for (results, replacements) |value, replacement| {
                                if (!iteration_protocol.valueIsStaticNumeric(program, replacement) or
                                    !hasOutsideUse(program, analysis, loops, block_loops, id, value)) continue;
                                try aliases.append(allocator, .{ .value = value, .replacement = replacement, .loop = id });
                            }
                        }
                    },
                    .generic => {},
                };
            }
            try collectIterationAliases(allocator, program, analysis, loop.body_region, loops, block_loops, aliases, uses);
        },
        .latch_loop => |loop| try collectIterationAliases(allocator, program, analysis, loop.body_region, loops, block_loops, aliases, uses),
        .infinite_loop => |loop| {
            try collectIterationAliases(allocator, program, analysis, loop.body_region, loops, block_loops, aliases, uses);
            if (loop.shared_side_exit) |side_exit| {
                for (side_exit.entries) |entry| {
                    try collectIterationAliases(allocator, program, analysis, entry.region, loops, block_loops, aliases, uses);
                }
            }
        },
        .loop_boundary => |control| {
            try collectIterationAliases(allocator, program, analysis, control.body_region, loops, block_loops, aliases, uses);
            switch (control.boundary) {
                .side_exit => |exit| try collectIterationAliases(allocator, program, analysis, exit.region, loops, block_loops, aliases, uses),
                .side_escape => |escape| try collectIterationAliases(allocator, program, analysis, escape.region, loops, block_loops, aliases, uses),
                .exit, .escape, .terminal, .shared_exit => {},
            }
        },
    };
}

fn findLoopByHeader(loops: []const LoopInfo, header: ir.BlockId) ?LoopId {
    for (loops, 0..) |loop, index| if (loop.header == header) return index;
    return null;
}

fn hasOutsideUse(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    loops: []const LoopInfo,
    block_loops: []const LoopId,
    loop_id: LoopId,
    value: ir.ValueId,
) bool {
    for (analysis.function.blocks) |block_id| {
        if (!analysis.isReachable(block_id) or block_id.index() >= program.blocks.len or
            blockInsideLoop(loops, block_loops, block_id, loop_id)) continue;
        if (blockUsesValue(program, program.blocks[block_id.index()], value)) return true;
    }
    return false;
}

const Builder = struct {
    program: *const ir.Program,
    function: ir.Function,
    loops: []const LoopInfo,
    block_loops: []const LoopId,
    selected: []LoopId,
    unsupported: []bool,

    fn recordUse(self: *Builder, value_id: ir.ValueId, use_block: ir.BlockId) void {
        if (value_id.index() >= self.program.values.len or value_id.index() >= self.selected.len) return;
        const value = self.program.values[value_id.index()];
        if (value.function != self.function.id) return;
        const definition = definitionBlock(self.program, value) orelse return;
        if (definition.index() >= self.block_loops.len) return;

        var current = self.block_loops[definition.index()];
        while (current != invalid_loop) {
            if (current >= self.loops.len) return;
            const info = self.loops[current];
            if (info.header != definition and !blockInsideLoop(self.loops, self.block_loops, use_block, current)) {
                if (!supportsDefinition(self.program, self.loops, self.block_loops, value, definition)) {
                    self.unsupported[value_id.index()] = true;
                    return;
                }
                const previous = self.selected[value_id.index()];
                if (previous == invalid_loop or self.loops[previous].depth < info.depth) {
                    self.selected[value_id.index()] = current;
                }
                return;
            }
            current = info.parent;
        }
    }
};

const UseVisitor = struct {
    builder: *Builder,
    block: ir.BlockId,

    pub fn value(self: UseVisitor, value_id: ir.ValueId) void {
        self.builder.recordUse(value_id, self.block);
    }

    pub fn pack(_: UseVisitor, _: ir.ValuePackId) void {}
    pub fn place(_: UseVisitor, _: ir.PlaceId) void {}
};

pub const PrepareError = std.mem.Allocator.Error || error{
    UnsupportedControlFlow,
    UnsupportedTransfer,
};

fn clonePlan(allocator: std.mem.Allocator, source: Plan) !Plan {
    const loops = try allocator.dupe(LoopInfo, source.loops);
    errdefer allocator.free(loops);
    const block_loops = try allocator.dupe(LoopId, source.block_loops);
    errdefer allocator.free(block_loops);
    const transfers = try allocator.dupe(Transfer, source.transfers);
    errdefer allocator.free(transfers);
    const aliases = try allocator.dupe(Alias, source.aliases);
    errdefer allocator.free(aliases);
    const unsupported_values = try allocator.dupe(ir.ValueId, source.unsupported_values);
    errdefer allocator.free(unsupported_values);
    return .{
        .allocator = allocator,
        .program = source.program,
        .function = source.function,
        .loops = loops,
        .block_loops = block_loops,
        .transfers = transfers,
        .aliases = aliases,
        .unsupported_values = unsupported_values,
    };
}

fn emptyPlan(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function: ir.Function,
) !Plan {
    const loops = try allocator.alloc(LoopInfo, 0);
    errdefer allocator.free(loops);
    const block_loops = try allocator.alloc(LoopId, 0);
    errdefer allocator.free(block_loops);
    const transfers = try allocator.alloc(Transfer, 0);
    errdefer allocator.free(transfers);
    const aliases = try allocator.alloc(Alias, 0);
    errdefer allocator.free(aliases);
    const unsupported_values = try allocator.alloc(ir.ValueId, 0);
    errdefer allocator.free(unsupported_values);
    return .{
        .allocator = allocator,
        .program = program,
        .function = function,
        .loops = loops,
        .block_loops = block_loops,
        .transfers = transfers,
        .aliases = aliases,
        .unsupported_values = unsupported_values,
    };
}

const CycleFrame = struct {
    local_index: usize,
    next_successor: usize,
};

fn hasUnmodeledCycle(
    allocator: std.mem.Allocator,
    analysis: *const cfg.Analysis,
    candidates: []const bool,
) PrepareError!bool {
    const colors = try allocator.alloc(u8, analysis.function.blocks.len);
    defer allocator.free(colors);
    @memset(colors, 0);
    const stack = try allocator.alloc(CycleFrame, analysis.function.blocks.len);
    defer allocator.free(stack);

    for (analysis.function.blocks, 0..) |start, start_index| {
        if (!analysis.isReachable(start) or colors[start_index] != 0) continue;
        var depth: usize = 1;
        colors[start_index] = 1;
        stack[0] = .{ .local_index = start_index, .next_successor = 0 };
        while (depth != 0) {
            const frame = &stack[depth - 1];
            const source = analysis.function.blocks[frame.local_index];
            const successor_count = analysis.successorCount(source);
            if (frame.next_successor >= successor_count) {
                colors[frame.local_index] = 2;
                depth -= 1;
                continue;
            }
            const target = analysis.successorAt(source, frame.next_successor) orelse return true;
            frame.next_successor += 1;
            const target_index = analysis.blockIndex(target) orelse return true;
            switch (colors[target_index]) {
                0 => {
                    colors[target_index] = 1;
                    stack[depth] = .{ .local_index = target_index, .next_successor = 0 };
                    depth += 1;
                },
                1 => if (!candidates[target_index]) return true,
                else => {},
            }
        }
    }
    return false;
}

/// A structured shadow is only needed when a value defined inside a loop is
/// observed outside that loop. Prove the absence of that case from the CFG
/// before invoking the substantially more expensive region builder. Unknown
/// or irreducible cycles retain the full path.
fn needsStructuredPreparation(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
) PrepareError!bool {
    const candidates = try natural_loop.headerCandidatesAlloc(allocator, analysis);
    defer allocator.free(candidates);
    const unmodeled_cycle = try hasUnmodeledCycle(allocator, analysis, candidates);

    for (candidates, 0..) |is_candidate, local_index| {
        if (!is_candidate) continue;
        const header = analysis.function.blocks[local_index];
        var membership = (natural_loop.collect(allocator, analysis, header) catch |err| switch (err) {
            error.UnsupportedShape => return true,
            error.OutOfMemory => return error.OutOfMemory,
        }) orelse return true;
        defer membership.deinit();

        var found = false;
        for (analysis.function.blocks, 0..) |block_id, block_index| {
            if (found or membership.bits[block_index] or !analysis.isReachable(block_id)) continue;
            const block = program.blocks[block_id.index()];
            const visitor = EscapingDefinitionVisitor{
                .program = program,
                .analysis = analysis,
                .membership = membership.bits,
                .found = &found,
            };
            for (block.instructions) |instruction_id| {
                if (instruction_id.index() >= program.instructions.len) continue;
                runtime_uses.visitOperationUses(program.instructions[instruction_id.index()].operation, visitor);
                if (found) break;
            }
            if (!found) runtime_uses.visitTerminatorUses(block.terminator, visitor);
        }
        if (found) return true;
    }
    if (unmodeled_cycle) return try hasEscapingIrreducibleDefinition(allocator, program, analysis);
    return false;
}

const EscapingDefinitionVisitor = struct {
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    membership: []const bool,
    found: *bool,

    pub fn value(self: EscapingDefinitionVisitor, value_id: ir.ValueId) void {
        if (self.found.* or value_id.index() >= self.program.values.len) return;
        const defined_value = self.program.values[value_id.index()];
        if (defined_value.function != self.analysis.function.id) return;
        const definition = definitionBlock(self.program, defined_value) orelse return;
        const definition_index = self.analysis.blockIndex(definition) orelse return;
        if (self.membership[definition_index]) self.found.* = true;
    }

    pub fn pack(_: EscapingDefinitionVisitor, _: ir.ValuePackId) void {}
    pub fn place(_: EscapingDefinitionVisitor, _: ir.PlaceId) void {}
};

/// Natural-loop candidates cover ordinary loop boundaries. For an irreducible
/// cycle, use its authenticated SCC as the conservative boundary: if no value
/// defined in that SCC is consumed outside it, lexical transfer cannot be
/// required even when the full structured region is expensive to build.
fn hasEscapingIrreducibleDefinition(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
) PrepareError!bool {
    var regions = try irreducible_region.analyze(allocator, analysis);
    defer regions.deinit();
    if (regions.regions.len == 0) return true;

    const region_of = try allocator.alloc(usize, analysis.function.blocks.len);
    defer allocator.free(region_of);
    @memset(region_of, invalid_region);
    for (regions.regions, 0..) |region, region_index| {
        for (region.blocks) |block_id| {
            const local_index = analysis.blockIndex(block_id) orelse return true;
            if (region_of[local_index] != invalid_region) return true;
            region_of[local_index] = region_index;
        }
    }

    var found = false;
    for (analysis.function.blocks) |block_id| {
        if (found or !analysis.isReachable(block_id) or block_id.index() >= program.blocks.len) continue;
        const block = program.blocks[block_id.index()];
        const visitor = IrreducibleEscapeVisitor{
            .program = program,
            .analysis = analysis,
            .region_of = region_of,
            .use_region = region_of[analysis.blockIndex(block_id).?],
            .found = &found,
        };
        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) continue;
            runtime_uses.visitOperationUses(program.instructions[instruction_id.index()].operation, visitor);
            if (found) break;
        }
        if (!found) runtime_uses.visitTerminatorUses(block.terminator, visitor);
    }
    return found;
}

const IrreducibleEscapeVisitor = struct {
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    region_of: []const usize,
    use_region: usize,
    found: *bool,

    pub fn value(self: IrreducibleEscapeVisitor, value_id: ir.ValueId) void {
        if (self.found.* or value_id.index() >= self.program.values.len) return;
        const defined_value = self.program.values[value_id.index()];
        if (defined_value.function != self.analysis.function.id) return;
        const definition = definitionBlock(self.program, defined_value) orelse return;
        const definition_index = self.analysis.blockIndex(definition) orelse return;
        if (self.region_of[definition_index] != invalid_region and
            self.region_of[definition_index] != self.use_region)
        {
            self.found.* = true;
        }
    }

    pub fn pack(_: IrreducibleEscapeVisitor, _: ir.ValuePackId) void {}
    pub fn place(_: IrreducibleEscapeVisitor, _: ir.PlaceId) void {}
};

/// Builds an emission-only shadow program. The original per-iteration value
/// remains local to the loop; a synthetic place carries its latest value to
/// rewritten uses outside the loop without changing durable IR or proof state.
pub fn prepareInArena(allocator: std.mem.Allocator, program: *const ir.Program) PrepareError!ir.Program {
    var plans: std.ArrayList(Plan) = .empty;
    defer {
        for (plans.items) |*plan| plan.deinit();
        plans.deinit(allocator);
    }

    var transfer_count: usize = 0;
    var alias_count: usize = 0;
    for (program.functions) |function| {
        std.debug.print("lexical_transfer function={} blocks={} stage=begin\n", .{ function.id.index(), function.blocks.len });
        var function_scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        defer function_scratch.deinit();
        const scratch = function_scratch.allocator();

        var analysis = cfg.Analysis.init(scratch, program, function) catch |err| switch (err) {
            error.InvalidCfg => return error.UnsupportedControlFlow,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer analysis.deinit();
        const needs_preparation = try needsStructuredPreparation(scratch, program, &analysis);
        std.debug.print("lexical_transfer function={} needs_preparation={} stage=checked\n", .{ function.id.index(), needs_preparation });
        if (!needs_preparation) {
            var empty = try emptyPlan(allocator, program, function);
            plans.append(allocator, empty) catch |err| {
                empty.deinit();
                return err;
            };
            continue;
        }
        std.debug.print("lexical_transfer function={} stage=structure_begin\n", .{function.id.index()});
        var structured = if (structure.Plan.shouldUseArbitraryFallback(&analysis))
            structure.Plan.initArbitrary(scratch, &analysis) catch |err| switch (err) {
                error.UnsupportedShape => return error.UnsupportedControlFlow,
                error.OutOfMemory => return error.OutOfMemory,
            }
        else
            structure.Plan.init(scratch, &analysis) catch |err| switch (err) {
                error.UnsupportedShape => structure.Plan.initArbitrary(scratch, &analysis) catch |fallback_error| switch (fallback_error) {
                    error.UnsupportedShape => return error.UnsupportedControlFlow,
                    error.OutOfMemory => return error.OutOfMemory,
                },
                error.OutOfMemory => return error.OutOfMemory,
            };
        defer structured.deinit();
        std.debug.print("lexical_transfer function={} stage=structure_done\n", .{function.id.index()});
        if (structured.root.arbitrary_cfg) {
            var empty = try emptyPlan(allocator, program, function);
            plans.append(allocator, empty) catch |append_error| {
                empty.deinit();
                return append_error;
            };
            continue;
        }
        const no_aliases: []const ir.ValueId = &.{};
        const no_excluded_instructions: []const bool = &.{};
        var uses = try runtime_uses.Counts.initFunction(
            scratch,
            program,
            &analysis,
            no_aliases,
            no_excluded_instructions,
        );
        defer uses.deinit();
        var scratch_plan = try Plan.initWithRuntimeUses(scratch, program, function, &analysis, &structured, &uses);
        std.debug.print("lexical_transfer function={} transfers={} aliases={} unsupported={} stage=plan_done\n", .{
            function.id.index(),
            scratch_plan.transfers.len,
            scratch_plan.aliases.len,
            scratch_plan.unsupported_values.len,
        });
        if (scratch_plan.unsupported_values.len != 0) {
            scratch_plan.deinit();
            return error.UnsupportedTransfer;
        }
        var plan = try clonePlan(allocator, scratch_plan);
        scratch_plan.deinit();
        transfer_count = std.math.add(usize, transfer_count, plan.transfers.len) catch {
            plan.deinit();
            return error.UnsupportedTransfer;
        };
        alias_count = std.math.add(usize, alias_count, plan.aliases.len) catch {
            plan.deinit();
            return error.UnsupportedTransfer;
        };
        plans.append(allocator, plan) catch |err| {
            plan.deinit();
            return err;
        };
    }
    if (transfer_count == 0 and alias_count == 0) return program.*;

    var values: std.ArrayList(ir.Value) = .empty;
    defer values.deinit(allocator);
    try values.appendSlice(allocator, program.values);
    var places: std.ArrayList(ir.Place) = .empty;
    defer places.deinit(allocator);
    try places.appendSlice(allocator, program.places);
    var instructions: std.ArrayList(ir.Instruction) = .empty;
    defer instructions.deinit(allocator);
    try instructions.appendSlice(allocator, program.instructions);

    const blocks = try allocator.dupe(ir.Block, program.blocks);
    const functions = try allocator.dupe(ir.Function, program.functions);
    const transfer_places = try allocator.alloc(?ir.PlaceId, program.values.len);
    defer allocator.free(transfer_places);
    @memset(transfer_places, null);
    const block_start_writes = try allocator.alloc(std.ArrayList(ir.InstructionId), program.blocks.len);
    for (block_start_writes) |*list| list.* = .empty;
    defer {
        for (block_start_writes) |*list| list.deinit(allocator);
        allocator.free(block_start_writes);
    }
    const writes_after_instruction = try allocator.alloc(std.ArrayList(ir.InstructionId), program.instructions.len);
    for (writes_after_instruction) |*list| list.* = .empty;
    defer {
        for (writes_after_instruction) |*list| list.deinit(allocator);
        allocator.free(writes_after_instruction);
    }
    const function_places = try allocator.alloc(std.ArrayList(ir.PlaceId), program.functions.len);
    for (function_places) |*list| list.* = .empty;
    defer {
        for (function_places) |*list| list.deinit(allocator);
        allocator.free(function_places);
    }

    for (program.functions) |function| {
        const plan = &plans.items[function.id.index()];
        try function_places[function.id.index()].appendSlice(allocator, function.local_places);
        for (plan.transfers) |transfer| {
            const value = program.values[transfer.value.index()];
            const definition = definitionBlock(program, value) orelse return error.UnsupportedTransfer;
            const evidence = definitionEvidence(program, value) orelse return error.UnsupportedTransfer;
            const place_id = ir.PlaceId.fromIndex(places.items.len);
            const local_index = function_places[function.id.index()].items.len;
            try places.append(allocator, .{
                .id = place_id,
                .function = function.id,
                .type = value.type,
                .name_hint = value.name_hint,
                .origin = .{ .local = @intCast(local_index) },
                .evidence = evidence,
            });
            transfer_places[value.id.index()] = place_id;
            try function_places[function.id.index()].append(allocator, place_id);

            const write_id = ir.InstructionId.fromIndex(instructions.items.len);
            try instructions.append(allocator, .{
                .id = write_id,
                .block = definition,
                .operation = .{ .place_write = .{ .place = place_id, .value = value.id } },
                .results = &.{},
                .effects = .place_write,
                .evidence = evidence,
            });
            switch (value.origin) {
                .block_parameter => try block_start_writes[definition.index()].append(allocator, write_id),
                .instruction_result => |origin| try writes_after_instruction[origin.instruction.index()].append(allocator, write_id),
                else => return error.UnsupportedTransfer,
            }
        }
    }
    for (program.blocks) |source_block| {
        const plan = &plans.items[source_block.function.index()];
        var replacements: std.ArrayList(runtime_value_rewrite.Replacement) = .empty;
        defer replacements.deinit(allocator);
        var read_ids: std.ArrayList(ir.InstructionId) = .empty;
        defer read_ids.deinit(allocator);

        for (plan.aliases) |alias| {
            if (!plan.aliasIsOutside(alias, source_block.id) or !blockUsesValue(program, source_block, alias.value)) continue;
            try replacements.append(allocator, .{ .from = alias.value, .to = alias.replacement });
        }

        for (plan.transfers) |transfer| {
            if (!plan.isOutside(transfer, source_block.id) or !blockUsesValue(program, source_block, transfer.value)) continue;
            const place_id = transfer_places[transfer.value.index()] orelse return error.UnsupportedTransfer;
            const read_id = ir.InstructionId.fromIndex(instructions.items.len);
            const read_value = ir.ValueId.fromIndex(values.items.len);
            const source_value = program.values[transfer.value.index()];
            const evidence = definitionEvidence(program, source_value) orelse return error.UnsupportedTransfer;
            const result_ids = try allocator.dupe(ir.ValueId, &.{read_value});
            try instructions.append(allocator, .{
                .id = read_id,
                .block = source_block.id,
                .operation = .{ .place_read = place_id },
                .results = result_ids,
                .effects = .place_read,
                .evidence = evidence,
            });
            try values.append(allocator, .{
                .id = read_value,
                .function = source_block.function,
                .type = source_value.type,
                .name_hint = source_value.name_hint,
                .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } },
            });
            try replacements.append(allocator, .{ .from = transfer.value, .to = read_value });
            try read_ids.append(allocator, read_id);
        }

        for (source_block.instructions) |instruction_id| {
            if (instruction_id.index() >= program.instructions.len) continue;
            instructions.items[instruction_id.index()].operation = try runtime_value_rewrite.operationAlloc(
                allocator,
                program.instructions[instruction_id.index()].operation,
                replacements.items,
            );
        }
        blocks[source_block.id.index()].terminator = try runtime_value_rewrite.terminatorAlloc(
            allocator,
            source_block.terminator,
            replacements.items,
        );

        var block_instructions: std.ArrayList(ir.InstructionId) = .empty;
        defer block_instructions.deinit(allocator);
        try block_instructions.appendSlice(allocator, read_ids.items);
        try block_instructions.appendSlice(allocator, block_start_writes[source_block.id.index()].items);
        for (source_block.instructions) |instruction_id| {
            try block_instructions.append(allocator, instruction_id);
            if (instruction_id.index() < writes_after_instruction.len) {
                try block_instructions.appendSlice(allocator, writes_after_instruction[instruction_id.index()].items);
            }
        }
        blocks[source_block.id.index()].instructions = try block_instructions.toOwnedSlice(allocator);
    }

    for (program.functions) |function| {
        functions[function.id.index()].local_places = try function_places[function.id.index()].toOwnedSlice(allocator);
    }

    var prepared = program.*;
    prepared.functions = functions;
    prepared.blocks = blocks;
    prepared.instructions = try instructions.toOwnedSlice(allocator);
    prepared.values = try values.toOwnedSlice(allocator);
    prepared.places = try places.toOwnedSlice(allocator);
    return prepared;
}

fn indexRegion(
    allocator: std.mem.Allocator,
    loops: *std.ArrayList(LoopInfo),
    block_loops: []LoopId,
    region: *const structure.Region,
    current: LoopId,
) std.mem.Allocator.Error!void {
    for (region.nodes) |node| switch (node) {
        .block => |block_id| markBlock(loops.items, block_loops, block_id, current),
        .branch => |branch| {
            markBlock(loops.items, block_loops, branch.block, current);
            try indexRegion(allocator, loops, block_loops, branch.then_region, current);
            try indexRegion(allocator, loops, block_loops, branch.else_region, current);
        },
        .loop => |loop| {
            const nested = try addLoop(allocator, loops, current, loop.header);
            markBlock(loops.items, block_loops, loop.header, nested);
            try indexRegion(allocator, loops, block_loops, loop.body_region, nested);
        },
        .latch_loop => |loop| {
            const nested = try addLoop(allocator, loops, current, loop.header);
            markBlock(loops.items, block_loops, loop.header, nested);
            try indexRegion(allocator, loops, block_loops, loop.body_region, nested);
        },
        .infinite_loop => |loop| {
            const nested = try addLoop(allocator, loops, current, loop.header);
            markBlock(loops.items, block_loops, loop.header, nested);
            try indexRegion(allocator, loops, block_loops, loop.body_region, nested);
            if (loop.shared_side_exit) |side_exit| {
                for (side_exit.entries) |entry| try indexRegion(allocator, loops, block_loops, entry.region, current);
            }
        },
        .loop_control => |control| markBlock(loops.items, block_loops, control.block, current),
        .loop_boundary => |control| {
            markBlock(loops.items, block_loops, control.block, current);
            try indexRegion(allocator, loops, block_loops, control.body_region, current);
            switch (control.boundary) {
                .side_exit => |side_exit| try indexRegion(allocator, loops, block_loops, side_exit.region, current),
                .side_escape => |side_escape| try indexRegion(allocator, loops, block_loops, side_escape.region, current),
                .exit, .escape, .terminal, .shared_exit => {},
            }
        },
        .loop_terminal => |control| {
            markBlock(loops.items, block_loops, control.block, current);
            markBlock(loops.items, block_loops, control.terminal_block, current);
        },
    };
}

fn addLoop(
    allocator: std.mem.Allocator,
    loops: *std.ArrayList(LoopInfo),
    parent: LoopId,
    header: ir.BlockId,
) std.mem.Allocator.Error!LoopId {
    const id = loops.items.len;
    const depth = if (parent == invalid_loop) 1 else loops.items[parent].depth + 1;
    try loops.append(allocator, .{ .parent = parent, .header = header, .depth = depth, .matched_iteration = false });
    return id;
}

fn markBlock(loops: []const LoopInfo, block_loops: []LoopId, block_id: ir.BlockId, current: LoopId) void {
    if (block_id.index() >= block_loops.len or current == invalid_loop) return;
    const previous = block_loops[block_id.index()];
    if (previous == invalid_loop or loops[previous].depth <= loops[current].depth) block_loops[block_id.index()] = current;
}

fn blockInsideLoop(loops: []const LoopInfo, block_loops: []const LoopId, block_id: ir.BlockId, target: LoopId) bool {
    if (block_id.index() >= block_loops.len or target >= loops.len) return false;
    var current = block_loops[block_id.index()];
    while (current != invalid_loop) {
        if (current == target) return true;
        if (current >= loops.len) return false;
        current = loops[current].parent;
    }
    return false;
}

fn definitionBlock(program: *const ir.Program, value: ir.Value) ?ir.BlockId {
    return switch (value.origin) {
        .block_parameter => |origin| origin.block,
        .instruction_result => |origin| if (origin.instruction.index() < program.instructions.len)
            program.instructions[origin.instruction.index()].block
        else
            null,
        .parameter, .capture => null,
    };
}

fn definitionEvidence(program: *const ir.Program, value: ir.Value) ?[]const ir.EvidenceId {
    return switch (value.origin) {
        .block_parameter => |origin| if (origin.block.index() < program.blocks.len)
            program.blocks[origin.block.index()].evidence
        else
            null,
        .instruction_result => |origin| if (origin.instruction.index() < program.instructions.len)
            program.instructions[origin.instruction.index()].evidence
        else
            null,
        .parameter, .capture => null,
    };
}

fn supportsDefinition(
    program: *const ir.Program,
    loops: []const LoopInfo,
    block_loops: []const LoopId,
    value: ir.Value,
    definition: ir.BlockId,
) bool {
    return switch (value.origin) {
        .block_parameter => true,
        .instruction_result => |origin| if (origin.instruction.index() < program.instructions.len) switch (program.instructions[origin.instruction.index()].operation) {
            .numeric_for_next => |operation| operation.mode == .semantic_normalized and
                !definitionOwnsMatchedIterationLoop(loops, block_loops, definition),
            .generic_for_next => false,
            else => true,
        } else false,
        .parameter, .capture => false,
    };
}

fn definitionOwnsMatchedIterationLoop(loops: []const LoopInfo, block_loops: []const LoopId, definition: ir.BlockId) bool {
    if (definition.index() >= block_loops.len) return false;
    const owner = block_loops[definition.index()];
    return owner < loops.len and loops[owner].header == definition and loops[owner].matched_iteration;
}

fn blockUsesValue(program: *const ir.Program, block: ir.Block, target: ir.ValueId) bool {
    var found = false;
    const visitor = FindValueVisitor{ .target = target, .found = &found };
    for (block.instructions) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) continue;
        runtime_uses.visitOperationUses(program.instructions[instruction_id.index()].operation, visitor);
    }
    runtime_uses.visitTerminatorUses(block.terminator, visitor);
    return found;
}

const FindValueVisitor = struct {
    target: ir.ValueId,
    found: *bool,

    pub fn value(self: FindValueVisitor, value_id: ir.ValueId) void {
        if (value_id == self.target) self.found.* = true;
    }

    pub fn pack(_: FindValueVisitor, _: ir.ValuePackId) void {}
    pub fn place(_: FindValueVisitor, _: ir.PlaceId) void {}
};

test "semantic normalized transfer distinguishes unmatched iteration ownership" {
    const function_id = ir.FunctionId.fromIndex(0);
    const definition = ir.BlockId.fromIndex(4);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const value_id = ir.ValueId.fromIndex(0);
    const values = [_]ir.Value{.{
        .id = value_id,
        .function = function_id,
        .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
    }};
    const instructions = [_]ir.Instruction{.{
        .id = instruction_id,
        .block = definition,
        .operation = .{ .numeric_for_next = .{
            .control = value_id,
            .limit = value_id,
            .step = value_id,
            .initial = value_id,
            .mode = .semantic_normalized,
        } },
        .results = &.{value_id},
        .effects = .numeric_for_next,
    }};
    const program: ir.Program = .{
        .program_id = "unmatched-iteration-transfer-policy",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
    };
    var loops = [_]LoopInfo{
        .{ .parent = invalid_loop, .header = ir.BlockId.fromIndex(1), .depth = 1, .matched_iteration = false },
        .{ .parent = 0, .header = definition, .depth = 2, .matched_iteration = false },
    };
    var block_loops = [_]LoopId{ invalid_loop, invalid_loop, invalid_loop, invalid_loop, 1 };

    try std.testing.expect(supportsDefinition(&program, &loops, &block_loops, values[0], definition));
    loops[1].matched_iteration = true;
    try std.testing.expect(!supportsDefinition(&program, &loops, &block_loops, values[0], definition));
}
