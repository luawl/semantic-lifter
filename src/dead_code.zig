const std = @import("std");
const ir = @import("ir.zig");
const pack_plan = @import("pack_plan.zig");
const luau_runtime = @import("luau_runtime.zig");
const runtime_uses = @import("runtime_uses.zig");
const readable_scope = @import("readable_scope.zig");

pub const Plan = struct {
    allocator: std.mem.Allocator,
    scope: ?readable_scope.Scope = null,
    eliminated: []bool,
    aliases: []ir.ValueId,
    inlined: []bool,

    pub fn init(allocator: std.mem.Allocator, program: *const ir.Program, packs: *const pack_plan.Plan) !Plan {
        var scope = try readable_scope.Scope.init(allocator, program);
        errdefer scope.deinit();
        const eliminated = try allocator.alloc(bool, program.instructions.len);
        errdefer allocator.free(eliminated);
        @memset(eliminated, false);
        const aliases = try allocator.alloc(ir.ValueId, program.values.len);
        errdefer allocator.free(aliases);
        for (aliases, 0..) |*alias, index| alias.* = ir.ValueId.fromIndex(index);
        const inlined = try allocator.alloc(bool, program.instructions.len);
        errdefer allocator.free(inlined);
        @memset(inlined, false);

        for (program.instructions) |instruction| {
            if (!isCopyAliasCandidate(program, packs, instruction)) continue;
            const result_id = instruction.results[0];
            aliases[result_id.index()] = instruction.operation.copy;
            eliminated[instruction.id.index()] = true;
        }

        try addSinglePredecessorAliases(allocator, program, &scope, aliases);

        var uses = try runtime_uses.Counts.initScoped(allocator, program, &scope, aliases, eliminated);
        defer uses.deinit();
        var worklist: std.ArrayList(ir.InstructionId) = .empty;
        defer worklist.deinit(allocator);
        for (program.instructions) |instruction| {
            if (canEliminate(program, packs, eliminated, uses.values, uses.packs, instruction)) {
                try worklist.append(allocator, instruction.id);
            }
        }

        var cursor: usize = 0;
        while (cursor < worklist.items.len) : (cursor += 1) {
            const instruction_id = worklist.items[cursor];
            if (instruction_id.index() >= program.instructions.len or eliminated[instruction_id.index()]) continue;
            const instruction = program.instructions[instruction_id.index()];
            if (!canEliminate(program, packs, eliminated, uses.values, uses.packs, instruction)) continue;
            eliminated[instruction_id.index()] = true;
            try uses.removeOperation(program, aliases, instruction.operation, &worklist);
        }

        const inline_depths = try allocator.alloc(usize, program.instructions.len);
        defer allocator.free(inline_depths);
        @memset(inline_depths, 0);
        for (program.instructions) |instruction| {
            const depth = inlineCandidateDepth(program, packs, eliminated, uses.values, inlined, inline_depths, instruction) orelse continue;
            if (depth >= luau_runtime.max_fused_expression_operations) continue;
            inlined[instruction.id.index()] = true;
            eliminated[instruction.id.index()] = true;
            inline_depths[instruction.id.index()] = depth;
        }

        return .{ .allocator = allocator, .scope = scope, .eliminated = eliminated, .aliases = aliases, .inlined = inlined };
    }

    pub fn deinit(self: *Plan) void {
        self.allocator.free(self.inlined);
        self.allocator.free(self.aliases);
        self.allocator.free(self.eliminated);
        if (self.scope) |*scope| scope.deinit();
    }

    pub fn contains(self: *const Plan, instruction_id: ir.InstructionId) bool {
        return instruction_id.index() < self.eliminated.len and self.eliminated[instruction_id.index()];
    }

    pub fn resolveValue(self: *const Plan, value_id: ir.ValueId) ir.ValueId {
        return resolveAlias(self.aliases, value_id);
    }

    pub fn isInlined(self: *const Plan, instruction_id: ir.InstructionId) bool {
        return instruction_id.index() < self.inlined.len and self.inlined[instruction_id.index()];
    }

    pub fn isValueAlias(self: *const Plan, value_id: ir.ValueId) bool {
        return self.resolveValue(value_id) != value_id;
    }

    pub fn semanticUseCounts(self: *const Plan, allocator: std.mem.Allocator, program: *const ir.Program) !runtime_uses.Counts {
        const excluded = try allocator.alloc(bool, program.instructions.len);
        defer allocator.free(excluded);
        for (excluded, 0..) |*item, index| {
            const instruction_id = ir.InstructionId.fromIndex(index);
            item.* = self.contains(instruction_id) and !self.isInlined(instruction_id);
        }
        if (self.scope) |scope| {
            return runtime_uses.Counts.initScoped(allocator, program, &scope, self.aliases, excluded);
        }
        return runtime_uses.Counts.init(allocator, program, self.aliases, excluded);
    }

    pub fn operationUsesValue(self: *const Plan, operation: ir.Operation, target: ir.ValueId) bool {
        var found = false;
        runtime_uses.visitOperationUses(operation, FindValueVisitor{ .plan = self, .target = target, .found = &found });
        return found;
    }

    pub fn terminatorUsesValue(self: *const Plan, terminator: ir.Terminator, target: ir.ValueId) bool {
        var found = false;
        runtime_uses.visitTerminatorUses(terminator, FindValueVisitor{ .plan = self, .target = target, .found = &found });
        return found;
    }
};

const FindValueVisitor = struct {
    plan: *const Plan,
    target: ir.ValueId,
    found: *bool,

    pub fn value(self: FindValueVisitor, value_id: ir.ValueId) void {
        if (self.plan.resolveValue(value_id) == self.target) self.found.* = true;
    }

    pub fn pack(_: FindValueVisitor, _: ir.ValuePackId) void {}
    pub fn place(_: FindValueVisitor, _: ir.PlaceId) void {}
};

fn addSinglePredecessorAliases(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    aliases: []ir.ValueId,
) !void {
    const predecessor_counts = try allocator.alloc(usize, program.blocks.len);
    defer allocator.free(predecessor_counts);
    @memset(predecessor_counts, 0);
    const predecessor_blocks = try allocator.alloc(?ir.BlockId, program.blocks.len);
    defer allocator.free(predecessor_blocks);
    @memset(predecessor_blocks, null);
    const incoming_arguments = try allocator.alloc(?[]const ir.ValueId, program.blocks.len);
    defer allocator.free(incoming_arguments);
    @memset(incoming_arguments, null);

    for (program.blocks) |block| {
        if (scope.block(block.id)) recordSuccessors(predecessor_counts, predecessor_blocks, incoming_arguments, block);
    }
    for (program.blocks) |block| {
        if (!scope.block(block.id)) continue;
        if (predecessor_counts[block.id.index()] != 1) continue;
        const predecessor_id = predecessor_blocks[block.id.index()] orelse continue;
        if (predecessor_id == block.id or predecessor_id.index() >= program.blocks.len) continue;
        // A branch target may be emitted outside the branch's lexical scope,
        // especially when the edge leaves a loop. Keep its transfer explicit.
        if (program.blocks[predecessor_id.index()].terminator != .jump) continue;
        if (block.function.index() >= program.functions.len or program.functions[block.function.index()].entry_block == block.id) continue;
        const arguments = incoming_arguments[block.id.index()] orelse continue;
        if (arguments.len != block.parameters.len) continue;
        for (block.parameters, arguments) |parameter, argument| {
            if (parameter.index() < aliases.len and argument.index() < aliases.len) aliases[parameter.index()] = argument;
        }
    }
}

fn recordSuccessors(predecessor_counts: []usize, predecessor_blocks: []?ir.BlockId, incoming_arguments: []?[]const ir.ValueId, block: ir.Block) void {
    switch (block.terminator) {
        .jump => |edge| recordEdge(predecessor_counts, predecessor_blocks, incoming_arguments, block.id, edge),
        .branch => |branch| {
            recordEdge(predecessor_counts, predecessor_blocks, incoming_arguments, block.id, branch.then_edge);
            recordEdge(predecessor_counts, predecessor_blocks, incoming_arguments, block.id, branch.else_edge);
        },
        else => {},
    }
}

fn recordEdge(predecessor_counts: []usize, predecessor_blocks: []?ir.BlockId, incoming_arguments: []?[]const ir.ValueId, predecessor: ir.BlockId, edge: ir.Edge) void {
    if (edge.target.index() >= predecessor_counts.len) return;
    const index = edge.target.index();
    predecessor_counts[index] += 1;
    if (predecessor_counts[index] == 1) {
        predecessor_blocks[index] = predecessor;
        incoming_arguments[index] = edge.arguments;
    }
}

fn isCopyAliasCandidate(program: *const ir.Program, packs: *const pack_plan.Plan, instruction: ir.Instruction) bool {
    if (instruction.id.index() >= program.instructions.len or instruction.results.len != 1 or instruction.pack_result != null) return false;
    const source = switch (instruction.operation) {
        .copy => |value_id| value_id,
        else => return false,
    };
    if (source.index() >= program.values.len or instruction.results[0].index() >= program.values.len) return false;
    if (!isObservationallyInert(instruction.effects)) return false;
    return switch (packs.role(instruction.id)) {
        .ordinary => true,
        else => false,
    };
}

fn inlineCandidateDepth(
    program: *const ir.Program,
    packs: *const pack_plan.Plan,
    eliminated: []const bool,
    value_uses: []const usize,
    inlined: []const bool,
    inline_depths: []const usize,
    instruction: ir.Instruction,
) ?usize {
    if (instruction.id.index() >= eliminated.len or eliminated[instruction.id.index()]) return null;
    if (instruction.results.len != 1 or instruction.pack_result != null or !isObservationallyInert(instruction.effects)) return null;
    const result_id = instruction.results[0];
    if (result_id.index() >= value_uses.len or value_uses[result_id.index()] != 1) return null;
    const origin_matches = switch (program.values[result_id.index()].origin) {
        .instruction_result => |origin| origin.instruction == instruction.id and origin.index == 0,
        else => false,
    };
    if (!origin_matches) return null;
    switch (packs.role(instruction.id)) {
        .ordinary => {},
        else => return null,
    }
    return switch (instruction.operation) {
        .constant, .function_ref => 1,
        .unary => |unary| addExpressionLevel(inlinedValueDepth(program, inlined, inline_depths, unary.operand)),
        .binary => |binary| addExpressionLevel(@max(
            inlinedValueDepth(program, inlined, inline_depths, binary.left),
            inlinedValueDepth(program, inlined, inline_depths, binary.right),
        )),
        else => null,
    };
}

fn inlinedValueDepth(program: *const ir.Program, inlined: []const bool, inline_depths: []const usize, value_id: ir.ValueId) usize {
    if (value_id.index() >= program.values.len) return 0;
    const origin = switch (program.values[value_id.index()].origin) {
        .instruction_result => |origin| origin,
        else => return 0,
    };
    if (origin.index != 0 or origin.instruction.index() >= inlined.len or !inlined[origin.instruction.index()] or
        origin.instruction.index() >= inline_depths.len) return 0;
    return inline_depths[origin.instruction.index()];
}

fn addExpressionLevel(depth: usize) usize {
    return std.math.add(usize, depth, 1) catch std.math.maxInt(usize);
}

fn resolveAlias(aliases: []const ir.ValueId, value_id: ir.ValueId) ir.ValueId {
    if (value_id.index() >= aliases.len) return value_id;
    var current = value_id;
    var remaining = aliases.len;
    while (remaining != 0) : (remaining -= 1) {
        const next = aliases[current.index()];
        if (next == current or next.index() >= aliases.len) return current;
        current = next;
    }
    return value_id;
}

fn canEliminate(program: *const ir.Program, packs: *const pack_plan.Plan, eliminated: []const bool, value_uses: []const usize, pack_uses: []const usize, instruction: ir.Instruction) bool {
    if (instruction.id.index() >= eliminated.len or eliminated[instruction.id.index()]) return false;
    switch (packs.role(instruction.id)) {
        .ordinary => {},
        else => return false,
    }
    if (!isObservationallyInert(instruction.effects)) return false;
    for (instruction.results) |value_id| {
        if (value_id.index() >= value_uses.len or value_uses[value_id.index()] != 0) return false;
    }
    if (instruction.pack_result) |pack_id| {
        if (pack_id.index() >= pack_uses.len or pack_uses[pack_id.index()] != 0) return false;
    }
    _ = program;
    return true;
}

fn isObservationallyInert(effects: ir.EffectSummary) bool {
    return effects.precision == .exact and
        !effects.writes_memory and
        !effects.may_throw and
        !effects.may_yield and
        !effects.invokes_unknown_code;
}

test "dead-code plan removes transitive exact-pure chains only" {
    const f = ir.FunctionId.fromIndex(0);
    const b = ir.BlockId.fromIndex(0);
    const i_constant = ir.InstructionId.fromIndex(0);
    const i_copy = ir.InstructionId.fromIndex(1);
    const i_observable = ir.InstructionId.fromIndex(2);
    const v_constant = ir.ValueId.fromIndex(0);
    const v_copy = ir.ValueId.fromIndex(1);
    const v_observable = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = v_constant, .function = f, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = i_constant, .index = 0 } } },
        .{ .id = v_copy, .function = f, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = i_copy, .index = 0 } } },
        .{ .id = v_observable, .function = f, .origin = .{ .instruction_result = .{ .instruction = i_observable, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = i_constant, .block = b, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_constant}, .effects = .pure },
        .{ .id = i_copy, .block = b, .operation = .{ .copy = v_constant }, .results = &.{v_copy}, .effects = .pure },
        .{ .id = i_observable, .block = b, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "observable" } }, .results = &.{v_observable}, .effects = .semantic_environment_read },
    };
    const blocks = [_]ir.Block{.{ .id = b, .function = f, .instructions = &.{ i_constant, i_copy, i_observable }, .terminator = .{ .return_values = &.{} } }};
    const functions = [_]ir.Function{.{ .id = f, .blocks = &.{b}, .entry_block = b }};
    const program: ir.Program = .{
        .program_id = "generic-dead-code-plan",
        .entry_function = f,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer packs.deinit();
    var plan = try Plan.init(std.testing.allocator, &program, &packs);
    defer plan.deinit();
    try std.testing.expect(plan.contains(i_constant));
    try std.testing.expect(plan.contains(i_copy));
    try std.testing.expect(!plan.contains(i_observable));
    try std.testing.expectEqual(v_constant, plan.resolveValue(v_copy));
}

test "branch edge parameters retain an explicit lexical transfer" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const target = ir.BlockId.fromIndex(1);
    const other = ir.BlockId.fromIndex(2);
    const source_value = ir.ValueId.fromIndex(0);
    const condition = ir.ValueId.fromIndex(1);
    const target_parameter = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = source_value, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 1 } },
        .{ .id = target_parameter, .function = function_id, .origin = .{ .block_parameter = .{ .block = target, .index = 0 } } },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = target, .arguments = &.{source_value} },
            .else_edge = .{ .target = other },
        } } },
        .{ .id = target, .function = function_id, .parameters = &.{target_parameter}, .terminator = .{ .return_values = &.{target_parameter} } },
        .{ .id = other, .function = function_id, .terminator = .{ .return_values = &.{source_value} } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ source_value, condition },
        .blocks = &.{ entry, target, other },
        .entry_block = entry,
    }};
    const program: ir.Program = .{
        .program_id = "branch-parameter-scope",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };
    var packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer packs.deinit();
    var plan = try Plan.init(std.testing.allocator, &program, &packs);
    defer plan.deinit();
    try std.testing.expectEqual(target_parameter, plan.resolveValue(target_parameter));
}

test "unreachable predecessors do not suppress jump parameter aliases" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const target_id = ir.BlockId.fromIndex(1);
    const dead_id = ir.BlockId.fromIndex(2);
    const source_id = ir.ValueId.fromIndex(0);
    const target_parameter_id = ir.ValueId.fromIndex(1);
    const values = [_]ir.Value{
        .{ .id = source_id, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = target_parameter_id, .function = function_id, .origin = .{ .block_parameter = .{ .block = target_id, .index = 0 } } },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .jump = .{ .target = target_id, .arguments = &.{source_id} } } },
        .{ .id = target_id, .function = function_id, .parameters = &.{target_parameter_id}, .terminator = .{ .return_values = &.{target_parameter_id} } },
        .{ .id = dead_id, .function = function_id, .terminator = .{ .jump = .{ .target = target_id, .arguments = &.{source_id} } } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .parameters = &.{source_id},
        .entry_block = entry_id,
        .blocks = &.{ entry_id, target_id, dead_id },
    };
    const program: ir.Program = .{
        .program_id = "live-single-predecessor-alias",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };

    var packs = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer packs.deinit();
    var plan = try Plan.init(std.testing.allocator, &program, &packs);
    defer plan.deinit();
    try std.testing.expectEqual(source_id, plan.resolveValue(target_parameter_id));
}
