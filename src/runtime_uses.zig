const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const readable_scope = @import("readable_scope.zig");

pub const Counts = struct {
    allocator: std.mem.Allocator,
    values: []usize,
    packs: []usize,

    pub fn init(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        aliases: []const ir.ValueId,
        excluded_instructions: []const bool,
    ) !Counts {
        var scope = try readable_scope.Scope.init(allocator, program);
        defer scope.deinit();
        return initScoped(allocator, program, &scope, aliases, excluded_instructions);
    }

    pub fn initScoped(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        scope: *const readable_scope.Scope,
        aliases: []const ir.ValueId,
        excluded_instructions: []const bool,
    ) !Counts {
        return initFiltered(allocator, program, scope, aliases, excluded_instructions, null);
    }

    pub fn initScopedIncludingBlock(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        scope: *const readable_scope.Scope,
        aliases: []const ir.ValueId,
        excluded_instructions: []const bool,
        included_block: ir.BlockId,
    ) !Counts {
        return initFiltered(allocator, program, scope, aliases, excluded_instructions, included_block);
    }

    pub fn initFunction(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        analysis: *const cfg.Analysis,
        aliases: []const ir.ValueId,
        excluded_instructions: []const bool,
    ) !Counts {
        const values = try allocator.alloc(usize, program.values.len);
        errdefer allocator.free(values);
        @memset(values, 0);
        const packs = try allocator.alloc(usize, program.value_packs.len);
        errdefer allocator.free(packs);
        @memset(packs, 0);

        for (analysis.function.blocks) |block_id| {
            if (block_id.index() >= program.blocks.len or !analysis.isReachable(block_id)) continue;
            const block = program.blocks[block_id.index()];
            for (block.instructions) |instruction_id| {
                if (instruction_id.index() >= program.instructions.len) continue;
                if (instruction_id.index() >= excluded_instructions.len or !excluded_instructions[instruction_id.index()]) {
                    visitOperationUses(program.instructions[instruction_id.index()].operation, CountVisitor{
                        .aliases = aliases,
                        .values = values,
                        .packs = packs,
                    });
                }
            }
            visitTerminatorUses(block.terminator, CountVisitor{
                .aliases = aliases,
                .values = values,
                .packs = packs,
            });
        }
        return .{ .allocator = allocator, .values = values, .packs = packs };
    }

    fn initFiltered(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        scope: *const readable_scope.Scope,
        aliases: []const ir.ValueId,
        excluded_instructions: []const bool,
        included_block: ?ir.BlockId,
    ) !Counts {
        const values = try allocator.alloc(usize, program.values.len);
        errdefer allocator.free(values);
        @memset(values, 0);
        const packs = try allocator.alloc(usize, program.value_packs.len);
        errdefer allocator.free(packs);
        @memset(packs, 0);

        for (program.instructions) |instruction| {
            if (!scope.instruction(instruction.id) and
                (included_block == null or instruction.block != included_block.?)) continue;
            if (instruction.id.index() >= excluded_instructions.len or !excluded_instructions[instruction.id.index()]) {
                visitOperationUses(instruction.operation, CountVisitor{
                    .aliases = aliases,
                    .values = values,
                    .packs = packs,
                });
            }
        }
        for (program.blocks) |block| {
            if (!scope.block(block.id) and (included_block == null or block.id != included_block.?)) continue;
            visitTerminatorUses(block.terminator, CountVisitor{
                .aliases = aliases,
                .values = values,
                .packs = packs,
            });
        }
        return .{ .allocator = allocator, .values = values, .packs = packs };
    }

    pub fn deinit(self: *Counts) void {
        self.allocator.free(self.packs);
        self.allocator.free(self.values);
    }

    pub fn removeOperation(
        self: *Counts,
        program: *const ir.Program,
        aliases: []const ir.ValueId,
        operation: ir.Operation,
        worklist: *std.ArrayList(ir.InstructionId),
    ) !void {
        switch (operation) {
            .constant, .make_table, .function_ref, .place_read => {},
            .copy => |value_id| try self.removeValue(program, aliases, value_id, worklist),
            .unary => |value| try self.removeValue(program, aliases, value.operand, worklist),
            .binary => |value| {
                try self.removeValue(program, aliases, value.left, worklist);
                try self.removeValue(program, aliases, value.right, worklist);
                if (zeroSaturatingShift(value)) try self.removeValue(program, aliases, value.right, worklist);
            },
            .call => |value| {
                try self.removeValue(program, aliases, value.callee, worklist);
                try self.removeValues(program, aliases, value.arguments, worklist);
                try self.removeOptionalPack(program, value.argument_pack, worklist);
            },
            .call_repeated_table_get => |value| {
                try self.removeValue(program, aliases, value.callee, worklist);
                try self.removeValues(program, aliases, value.prefix_arguments, worklist);
                try self.removeValue(program, aliases, value.table, worklist);
                try self.removeValue(program, aliases, value.key, worklist);
                try self.removeValue(program, aliases, value.from, worklist);
                try self.removeValue(program, aliases, value.to, worklist);
                try self.removeValue(program, aliases, value.step, worklist);
            },
            .namecall => |value| {
                try self.removeValue(program, aliases, value.receiver, worklist);
                try self.removeValues(program, aliases, value.arguments, worklist);
                try self.removeOptionalPack(program, value.argument_pack, worklist);
            },
            .protected_call => |value| {
                try self.removeValue(program, aliases, value.callee, worklist);
                if (value.error_handler) |handler| try self.removeValue(program, aliases, handler, worklist);
                try self.removeValues(program, aliases, value.arguments, worklist);
                try self.removeOptionalPack(program, value.argument_pack, worklist);
            },
            .coroutine_create => |value| try self.removeValue(program, aliases, value.callee, worklist),
            .coroutine_resume => |value| {
                try self.removeValue(program, aliases, value.thread, worklist);
                try self.removeValues(program, aliases, value.arguments, worklist);
                try self.removeOptionalPack(program, value.argument_pack, worklist);
            },
            .coroutine_yield => |value| {
                try self.removeValues(program, aliases, value.arguments, worklist);
                try self.removeOptionalPack(program, value.argument_pack, worklist);
            },
            .environment_get => |value| try self.removeEnvironmentTarget(program, aliases, value.target, worklist),
            .environment_set => |value| {
                try self.removeEnvironmentTarget(program, aliases, value.target, worklist);
                try self.removeValue(program, aliases, value.value, worklist);
            },
            .table_get => |value| {
                try self.removeValue(program, aliases, value.table, worklist);
                try self.removeValue(program, aliases, value.key, worklist);
            },
            .table_set => |value| {
                try self.removeValue(program, aliases, value.table, worklist);
                try self.removeValue(program, aliases, value.key, worklist);
                try self.removeValue(program, aliases, value.value, worklist);
            },
            .table_set_pack => |value| {
                try self.removeValue(program, aliases, value.table, worklist);
                try self.removePack(program, value.pack, worklist);
            },
            .make_closure => |value| for (value.bindings) |binding| switch (binding) {
                .value => |value_id| try self.removeValue(program, aliases, value_id, worklist),
                .place => {},
            },
            .place_write => |value| try self.removeValue(program, aliases, value.value, worklist),
            .pack_values => |values| try self.removeValues(program, aliases, values, worklist),
            .adjust_pack => |pack_id| try self.removePack(program, pack_id, worklist),
            .numeric_for_next => |value| {
                try self.removeValue(program, aliases, value.control, worklist);
                try self.removeValue(program, aliases, value.limit, worklist);
                try self.removeValue(program, aliases, value.step, worklist);
                try self.removeValue(program, aliases, value.initial, worklist);
            },
            .generic_for_next => |value| {
                try self.removeValue(program, aliases, value.iterator, worklist);
                try self.removeValue(program, aliases, value.state, worklist);
                try self.removeValue(program, aliases, value.control, worklist);
                try self.removeValue(program, aliases, value.initial, worklist);
            },
            .make_table_literal => |value| {
                for (value.fields) |field| switch (field) {
                    .list => |item| try self.removeValue(program, aliases, item, worklist),
                    .keyed => |keyed| {
                        try self.removeValue(program, aliases, keyed.key, worklist);
                        try self.removeValue(program, aliases, keyed.value, worklist);
                    },
                };
                try self.removeOptionalPack(program, value.tail_pack, worklist);
            },
            .string_interpolate => |value| try self.removeValues(program, aliases, value.values, worklist),
        }
    }

    fn removeEnvironmentTarget(self: *Counts, program: *const ir.Program, aliases: []const ir.ValueId, target: ir.EnvironmentTarget, worklist: *std.ArrayList(ir.InstructionId)) !void {
        switch (target) {
            .ambient => {},
            .value => |value_id| try self.removeValue(program, aliases, value_id, worklist),
        }
    }

    fn removeValues(self: *Counts, program: *const ir.Program, aliases: []const ir.ValueId, values: []const ir.ValueId, worklist: *std.ArrayList(ir.InstructionId)) !void {
        for (values) |value_id| try self.removeValue(program, aliases, value_id, worklist);
    }

    fn removeValue(self: *Counts, program: *const ir.Program, aliases: []const ir.ValueId, value_id: ir.ValueId, worklist: *std.ArrayList(ir.InstructionId)) !void {
        const resolved = resolveAlias(aliases, value_id);
        if (resolved.index() >= self.values.len or self.values[resolved.index()] == 0) return;
        self.values[resolved.index()] -= 1;
        if (self.values[resolved.index()] != 0) return;
        switch (program.values[resolved.index()].origin) {
            .instruction_result => |result| try worklist.append(self.allocator, result.instruction),
            else => {},
        }
    }

    fn removeOptionalPack(self: *Counts, program: *const ir.Program, pack_id: ?ir.ValuePackId, worklist: *std.ArrayList(ir.InstructionId)) !void {
        if (pack_id) |id| try self.removePack(program, id, worklist);
    }

    fn removePack(self: *Counts, program: *const ir.Program, pack_id: ir.ValuePackId, worklist: *std.ArrayList(ir.InstructionId)) !void {
        if (pack_id.index() >= self.packs.len or self.packs[pack_id.index()] == 0) return;
        self.packs[pack_id.index()] -= 1;
        if (self.packs[pack_id.index()] != 0) return;
        switch (program.value_packs[pack_id.index()].origin) {
            .instruction_result => |instruction_id| try worklist.append(self.allocator, instruction_id),
            .varargs => {},
        }
    }
};

pub fn visitOperationUses(operation: ir.Operation, visitor: anytype) void {
    switch (operation) {
        .constant, .make_table, .function_ref => {},
        .copy => |value_id| visitor.value(value_id),
        .unary => |value| visitor.value(value.operand),
        .binary => |value| {
            visitor.value(value.left);
            visitor.value(value.right);
            if (zeroSaturatingShift(value)) visitor.value(value.right);
        },
        .call => |value| {
            visitor.value(value.callee);
            for (value.arguments) |argument| visitor.value(argument);
            if (value.argument_pack) |pack_id| visitor.pack(pack_id);
        },
        .call_repeated_table_get => |value| {
            visitor.value(value.callee);
            for (value.prefix_arguments) |argument| visitor.value(argument);
            visitor.value(value.table);
            visitor.value(value.key);
            visitor.value(value.from);
            visitor.value(value.to);
            visitor.value(value.step);
            if (value.counter) |place_id| visitor.place(place_id);
        },
        .namecall => |value| {
            visitor.value(value.receiver);
            for (value.arguments) |argument| visitor.value(argument);
            if (value.argument_pack) |pack_id| visitor.pack(pack_id);
        },
        .protected_call => |value| {
            visitor.value(value.callee);
            if (value.error_handler) |handler| visitor.value(handler);
            for (value.arguments) |argument| visitor.value(argument);
            if (value.argument_pack) |pack_id| visitor.pack(pack_id);
        },
        .coroutine_create => |value| visitor.value(value.callee),
        .coroutine_resume => |value| {
            visitor.value(value.thread);
            for (value.arguments) |argument| visitor.value(argument);
            if (value.argument_pack) |pack_id| visitor.pack(pack_id);
        },
        .coroutine_yield => |value| {
            for (value.arguments) |argument| visitor.value(argument);
            if (value.argument_pack) |pack_id| visitor.pack(pack_id);
        },
        .environment_get => |value| switch (value.target) {
            .ambient => {},
            .value => |value_id| visitor.value(value_id),
        },
        .environment_set => |value| {
            switch (value.target) {
                .ambient => {},
                .value => |value_id| visitor.value(value_id),
            }
            visitor.value(value.value);
        },
        .table_get => |value| {
            visitor.value(value.table);
            visitor.value(value.key);
        },
        .table_set => |value| {
            visitor.value(value.table);
            visitor.value(value.key);
            visitor.value(value.value);
        },
        .table_set_pack => |value| {
            visitor.value(value.table);
            visitor.pack(value.pack);
        },
        .make_closure => |value| for (value.bindings) |binding| switch (binding) {
            .value => |value_id| visitor.value(value_id),
            .place => |place_id| visitor.place(place_id),
        },
        .place_read => |place_id| visitor.place(place_id),
        .place_write => |value| {
            visitor.place(value.place);
            visitor.value(value.value);
        },
        .pack_values => |values| for (values) |value| visitor.value(value),
        .adjust_pack => |pack_id| visitor.pack(pack_id),
        .numeric_for_next => |value| {
            visitor.value(value.control);
            visitor.value(value.limit);
            visitor.value(value.step);
            visitor.value(value.initial);
        },
        .generic_for_next => |value| {
            visitor.value(value.iterator);
            visitor.value(value.state);
            visitor.value(value.control);
            visitor.value(value.initial);
        },
        .make_table_literal => |value| {
            for (value.fields) |field| switch (field) {
                .list => |item| visitor.value(item),
                .keyed => |keyed| {
                    visitor.value(keyed.key);
                    visitor.value(keyed.value);
                },
            };
            if (value.tail_pack) |pack_id| visitor.pack(pack_id);
        },
        .string_interpolate => |value| for (value.values) |item| visitor.value(item),
    }
}

fn zeroSaturatingShift(binary: ir.Binary) bool {
    return (binary.operator == .shift_left or binary.operator == .shift_right) and
        binary.shift_behavior == .zero_saturating;
}

pub fn visitTerminatorUses(terminator: ir.Terminator, visitor: anytype) void {
    switch (terminator) {
        .jump => |edge| for (edge.arguments) |argument| visitor.value(argument),
        .branch => |branch| {
            visitor.value(branch.condition);
            for (branch.then_edge.arguments) |argument| visitor.value(argument);
            for (branch.else_edge.arguments) |argument| visitor.value(argument);
        },
        .return_values => |values| for (values) |value_id| visitor.value(value_id),
        .return_pack => |pack_id| visitor.pack(pack_id),
        .return_expanded => |expanded| {
            for (expanded.values) |value_id| visitor.value(value_id);
            visitor.pack(expanded.pack);
        },
        .throw_error => |value| {
            visitor.value(value.value);
            if (value.dynamic_level) |level| visitor.value(level);
        },
        .unreachable_block => {},
    }
}

const CountVisitor = struct {
    aliases: []const ir.ValueId,
    values: []usize,
    packs: []usize,

    pub fn value(self: CountVisitor, value_id: ir.ValueId) void {
        const resolved = resolveAlias(self.aliases, value_id);
        if (resolved.index() < self.values.len) self.values[resolved.index()] += 1;
    }

    pub fn pack(self: CountVisitor, pack_id: ir.ValuePackId) void {
        if (pack_id.index() < self.packs.len) self.packs[pack_id.index()] += 1;
    }

    pub fn place(_: CountVisitor, _: ir.PlaceId) void {}
};

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

test "runtime counts exclude unreachable instruction and terminator uses" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const dead_id = ir.BlockId.fromIndex(1);
    const source_id = ir.ValueId.fromIndex(0);
    const dead_result_id = ir.ValueId.fromIndex(1);
    const dead_instruction_id = ir.InstructionId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = source_id, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = dead_result_id, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = dead_instruction_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{.{
        .id = dead_instruction_id,
        .block = dead_id,
        .operation = .{ .copy = source_id },
        .results = &.{dead_result_id},
        .effects = .pure,
    }};
    const blocks = [_]ir.Block{
        .{ .id = entry_id, .function = function_id, .terminator = .{ .return_values = &.{source_id} } },
        .{ .id = dead_id, .function = function_id, .instructions = &.{dead_instruction_id}, .terminator = .{ .return_values = &.{ source_id, dead_result_id } } },
    };
    const function: ir.Function = .{
        .id = function_id,
        .parameters = &.{source_id},
        .entry_block = entry_id,
        .blocks = &.{ entry_id, dead_id },
    };
    const program: ir.Program = .{
        .program_id = "runtime-live-use-counts",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    const aliases = [_]ir.ValueId{ source_id, dead_result_id };
    const excluded = [_]bool{false};

    var counts = try Counts.init(std.testing.allocator, &program, &aliases, &excluded);
    defer counts.deinit();
    try std.testing.expectEqual(@as(usize, 1), counts.values[source_id.index()]);
    try std.testing.expectEqual(@as(usize, 0), counts.values[dead_result_id.index()]);

    var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer scope.deinit();
    var witness_counts = try Counts.initScopedIncludingBlock(
        std.testing.allocator,
        &program,
        &scope,
        &aliases,
        &excluded,
        dead_id,
    );
    defer witness_counts.deinit();
    try std.testing.expectEqual(@as(usize, 3), witness_counts.values[source_id.index()]);
    try std.testing.expectEqual(@as(usize, 1), witness_counts.values[dead_result_id.index()]);
}

test "zero-saturating shifts materialize a reused displacement" {
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const aliases = [_]ir.ValueId{ left, right };
    var value_counts = [_]usize{ 0, 0 };
    var pack_counts: [0]usize = .{};
    const visitor = CountVisitor{
        .aliases = &aliases,
        .values = &value_counts,
        .packs = &pack_counts,
    };

    visitOperationUses(.{ .binary = .{
        .operator = .shift_left,
        .left = left,
        .right = right,
        .mode = .primitive,
        .shift_behavior = .zero_saturating,
    } }, visitor);
    try std.testing.expectEqual(@as(usize, 1), value_counts[left.index()]);
    try std.testing.expectEqual(@as(usize, 2), value_counts[right.index()]);

    value_counts = .{ 0, 0 };
    visitOperationUses(.{ .binary = .{
        .operator = .shift_left,
        .left = left,
        .right = right,
        .mode = .primitive,
        .shift_behavior = .luau_bit32,
    } }, visitor);
    try std.testing.expectEqual(@as(usize, 1), value_counts[left.index()]);
    try std.testing.expectEqual(@as(usize, 1), value_counts[right.index()]);
}
