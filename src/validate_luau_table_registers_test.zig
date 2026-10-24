const std = @import("std");
const ir = @import("ir.zig");
const diagnostics = @import("diagnostics.zig");
const readable_scope = @import("readable_scope.zig");
const register_validation = @import("validate_luau_registers.zig");

fn validate(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
) !void {
    return register_validation.validate(allocator, report, program, scope, .direct_locals_luau);
}

fn tableTemporaryPressureReport(comptime field_count: usize) !diagnostics.Report {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const produce_id = ir.InstructionId.fromIndex(0);
    const table_id = ir.InstructionId.fromIndex(1);
    const callee = ir.ValueId.fromIndex(0);
    const table = ir.ValueId.fromIndex(field_count + 1);
    var values: [field_count + 2]ir.Value = undefined;
    var results: [field_count]ir.ValueId = undefined;
    var fields: [field_count]ir.TableConstructorField = undefined;
    values[0] = .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } };
    for (&results, &fields, 0..) |*result, *field, index| {
        result.* = ir.ValueId.fromIndex(index + 1);
        values[index + 1] = .{
            .id = result.*,
            .function = function_id,
            .origin = .{ .instruction_result = .{ .instruction = produce_id, .index = @intCast(index) } },
        };
        field.* = .{ .list = result.* };
    }
    values[table.index()] = .{
        .id = table,
        .function = function_id,
        .type = .{ .kind = .table },
        .origin = .{ .instruction_result = .{ .instruction = table_id, .index = 0 } },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = produce_id,
            .block = block_id,
            .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .fixed = field_count } } },
            .results = &results,
            .effects = .dynamic_call,
        },
        .{
            .id = table_id,
            .block = block_id,
            .operation = .{ .make_table_literal = .{ .fields = &fields } },
            .results = &.{table},
            .effects = .pure,
        },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ produce_id, table_id },
        .terminator = .{ .return_values = &.{ table, table } },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "table-register-pressure",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer scope.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    errdefer report.deinit();
    try validate(std.testing.allocator, &report, &program, &scope);
    return report;
}

test "table construction over retained locals is bounded by the locals budget" {
    var retained = try tableTemporaryPressureReport(127);
    defer retained.deinit();
    try std.testing.expectEqual(@as(usize, 0), retained.diagnostics.items.len);

    var boundary = try tableTemporaryPressureReport(198);
    defer boundary.deinit();
    try std.testing.expectEqual(@as(usize, 0), boundary.diagnostics.items.len);

    var excessive = try tableTemporaryPressureReport(199);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_register_pressure));
    try std.testing.expect(!excessive.contains(.unsupported_readable_temporary_register_pressure));
}

fn registerAtomicKeyedTableReport(comptime field_count: usize) !diagnostics.Report {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const scalar_count = field_count * 2;
    const table_id = ir.InstructionId.fromIndex(scalar_count);
    const table_value = ir.ValueId.fromIndex(scalar_count);
    var scalar_results: [scalar_count]ir.ValueId = undefined;
    var values: [scalar_count + 1]ir.Value = undefined;
    var instruction_ids: [scalar_count + 1]ir.InstructionId = undefined;
    var instructions: [scalar_count + 1]ir.Instruction = undefined;
    var fields: [field_count]ir.TableConstructorField = undefined;
    for (0..field_count) |field_index| {
        const key_index = field_index * 2;
        const value_index = key_index + 1;
        const key_id = ir.ValueId.fromIndex(key_index);
        const value_id = ir.ValueId.fromIndex(value_index);
        scalar_results[key_index] = key_id;
        scalar_results[value_index] = value_id;
        values[key_index] = .{
            .id = key_id,
            .function = function_id,
            .type = .{ .kind = .integer },
            .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(key_index), .index = 0 } },
        };
        values[value_index] = .{
            .id = value_id,
            .function = function_id,
            .type = .{ .kind = .string },
            .origin = .{ .instruction_result = .{ .instruction = ir.InstructionId.fromIndex(value_index), .index = 0 } },
        };
        instruction_ids[key_index] = ir.InstructionId.fromIndex(key_index);
        instruction_ids[value_index] = ir.InstructionId.fromIndex(value_index);
        instructions[key_index] = .{
            .id = instruction_ids[key_index],
            .block = block_id,
            .operation = .{ .constant = .{ .integer = "1" } },
            .results = scalar_results[key_index .. key_index + 1],
            .effects = .pure,
        };
        instructions[value_index] = .{
            .id = instruction_ids[value_index],
            .block = block_id,
            .operation = .{ .constant = .{ .string = "value" } },
            .results = scalar_results[value_index .. value_index + 1],
            .effects = .pure,
        };
        fields[field_index] = .{ .keyed = .{ .key = key_id, .value = value_id } };
    }
    values[table_value.index()] = .{
        .id = table_value,
        .function = function_id,
        .type = .{ .kind = .table },
        .origin = .{ .instruction_result = .{ .instruction = table_id, .index = 0 } },
    };
    instruction_ids[scalar_count] = table_id;
    const table_results = [_]ir.ValueId{table_value};
    instructions[scalar_count] = .{
        .id = table_id,
        .block = block_id,
        .operation = .{ .make_table_literal = .{ .fields = &fields } },
        .results = &table_results,
        .effects = .pure,
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &instruction_ids,
        .terminator = .{ .return_values = &table_results },
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
    }};
    const program: ir.Program = .{
        .program_id = "register-atomic-keyed-table",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer scope.deinit();
    var report = diagnostics.Report.init(std.testing.allocator);
    errdefer report.deinit();
    try validate(std.testing.allocator, &report, &program, &scope);
    return report;
}

test "register-atomic keyed constructor fields reuse a sequential frame" {
    var report = try registerAtomicKeyedTableReport(256);
    defer report.deinit();
    try std.testing.expect(report.isClean());
}

/// One entry function built in creation order (its parameters first, then each instruction and its result value), as
/// the source frontend lowers a returned constructor; blocks after the first only for the branch shape. Each program is
/// validated in direct locals, where the constants are inlined and the calls fused into the constructor, which is fused
/// into the return, so the certified total is the parameters and the constructor's frame.
const ConstructorProgram = struct {
    arena: std.heap.ArenaAllocator,
    parameters: std.ArrayList(ir.ValueId) = .empty,
    blocks: std.ArrayList(ir.Block) = .empty,
    block_instructions: std.ArrayList(std.ArrayList(ir.InstructionId)) = .empty,
    block_parameters: std.ArrayList(std.ArrayList(ir.ValueId)) = .empty,
    instructions: std.ArrayList(ir.Instruction) = .empty,
    values: std.ArrayList(ir.Value) = .empty,
    packs: std.ArrayList(ir.ValuePack) = .empty,

    const function_id = ir.FunctionId.fromIndex(0);

    fn init() ConstructorProgram {
        return .{ .arena = std.heap.ArenaAllocator.init(std.testing.allocator) };
    }

    fn deinit(self: *ConstructorProgram) void {
        self.arena.deinit();
    }

    fn parameter(self: *ConstructorProgram) std.mem.Allocator.Error!ir.ValueId {
        const allocator = self.arena.allocator();
        const id = ir.ValueId.fromIndex(self.values.items.len);
        try self.values.append(allocator, .{ .id = id, .function = function_id, .origin = .{ .parameter = @intCast(self.parameters.items.len) } });
        try self.parameters.append(allocator, id);
        return id;
    }

    fn block(self: *ConstructorProgram) std.mem.Allocator.Error!ir.BlockId {
        const allocator = self.arena.allocator();
        const id = ir.BlockId.fromIndex(self.blocks.items.len);
        try self.blocks.append(allocator, .{ .id = id, .function = function_id, .terminator = .unreachable_block });
        try self.block_instructions.append(allocator, .empty);
        try self.block_parameters.append(allocator, .empty);
        return id;
    }

    fn blockParameter(self: *ConstructorProgram, target: ir.BlockId) std.mem.Allocator.Error!ir.ValueId {
        const allocator = self.arena.allocator();
        const id = ir.ValueId.fromIndex(self.values.items.len);
        const list = &self.block_parameters.items[target.index()];
        try self.values.append(allocator, .{
            .id = id,
            .function = function_id,
            .origin = .{ .block_parameter = .{ .block = target, .index = @intCast(list.items.len) } },
        });
        try list.append(allocator, id);
        return id;
    }

    /// Appends an instruction to `target` with one result of `value_type`.
    fn add(
        self: *ConstructorProgram,
        target: ir.BlockId,
        operation: ir.Operation,
        effects: ir.EffectSummary,
        value_type: ir.ValueType,
    ) std.mem.Allocator.Error!ir.ValueId {
        const allocator = self.arena.allocator();
        const instruction_id = ir.InstructionId.fromIndex(self.instructions.items.len);
        const value_id = ir.ValueId.fromIndex(self.values.items.len);
        try self.values.append(allocator, .{
            .id = value_id,
            .function = function_id,
            .type = value_type,
            .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
        });
        try self.instructions.append(allocator, .{
            .id = instruction_id,
            .block = target,
            .operation = operation,
            .results = try allocator.dupe(ir.ValueId, &.{value_id}),
            .effects = effects,
        });
        try self.block_instructions.items[target.index()].append(allocator, instruction_id);
        return value_id;
    }

    /// `count` string constants `<prefix>0` ... appended to `fields` as list items.
    fn strings(
        self: *ConstructorProgram,
        target: ir.BlockId,
        fields: *std.ArrayList(ir.TableConstructorField),
        count: usize,
        prefix: []const u8,
    ) std.mem.Allocator.Error!void {
        const allocator = self.arena.allocator();
        for (0..count) |index| {
            const text = try std.fmt.allocPrint(allocator, "{s}{d}", .{ prefix, index });
            const result = try self.add(target, .{ .constant = .{ .string = text } }, .pure, ir.ValueType.string);
            try fields.append(allocator, .{ .list = result });
        }
    }

    fn repeated(self: *ConstructorProgram, item: ir.ValueId, count: usize) std.mem.Allocator.Error![]ir.ValueId {
        const items = try self.arena.allocator().alloc(ir.ValueId, count);
        @memset(items, item);
        return items;
    }

    fn call(self: *ConstructorProgram, target: ir.BlockId, callee: ir.ValueId, arguments: []const ir.ValueId) std.mem.Allocator.Error!ir.ValueId {
        const owned = try self.arena.allocator().dupe(ir.ValueId, arguments);
        return self.add(target, .{ .call = .{ .callee = callee, .arguments = owned, .result_arity = .{ .fixed = 1 } } }, .dynamic_call, ir.ValueType.dynamic);
    }

    /// `callee(arguments)` with every result, the pack of a constructor's tail.
    fn packCall(self: *ConstructorProgram, target: ir.BlockId, callee: ir.ValueId, arguments: []const ir.ValueId) std.mem.Allocator.Error!ir.ValuePackId {
        const allocator = self.arena.allocator();
        const instruction_id = ir.InstructionId.fromIndex(self.instructions.items.len);
        const pack_id = ir.ValuePackId.fromIndex(self.packs.items.len);
        try self.packs.append(allocator, .{ .id = pack_id, .function = function_id, .origin = .{ .instruction_result = instruction_id } });
        try self.instructions.append(allocator, .{
            .id = instruction_id,
            .block = target,
            .operation = .{ .call = .{ .callee = callee, .arguments = try allocator.dupe(ir.ValueId, arguments), .result_arity = .variadic } },
            .results = &.{},
            .pack_result = pack_id,
            .effects = .dynamic_call,
        });
        try self.block_instructions.items[target.index()].append(allocator, instruction_id);
        return pack_id;
    }

    fn make(
        self: *ConstructorProgram,
        target: ir.BlockId,
        fields: []const ir.TableConstructorField,
        tail_pack: ?ir.ValuePackId,
    ) std.mem.Allocator.Error!ir.ValueId {
        const owned = try self.arena.allocator().dupe(ir.TableConstructorField, fields);
        return self.add(target, .{ .make_table_literal = .{ .fields = owned, .tail_pack = tail_pack } }, .table_constructor, .{ .kind = .table });
    }

    /// `levels` nested constructors, each 15 strings and then the next level as its 16th item; the innermost holds
    /// `innermost` strings.
    fn chain(self: *ConstructorProgram, target: ir.BlockId, levels: usize, innermost: usize) std.mem.Allocator.Error!ir.ValueId {
        const allocator = self.arena.allocator();
        var fields: std.ArrayList(ir.TableConstructorField) = .empty;
        if (levels == 1) {
            try self.strings(target, &fields, innermost, "c");
            return self.make(target, fields.items, null);
        }
        try self.strings(target, &fields, 15, try std.fmt.allocPrint(allocator, "c{d}_", .{levels}));
        const next = try self.chain(target, levels - 1, innermost);
        try fields.append(allocator, .{ .list = next });
        return self.make(target, fields.items, null);
    }

    fn returns(self: *ConstructorProgram, target: ir.BlockId, results: []const ir.ValueId) std.mem.Allocator.Error!void {
        self.blocks.items[target.index()].terminator = .{ .return_values = try self.arena.allocator().dupe(ir.ValueId, results) };
    }

    fn jump(self: *ConstructorProgram, source: ir.BlockId, target: ir.BlockId, arguments: []const ir.ValueId) std.mem.Allocator.Error!void {
        self.blocks.items[source.index()].terminator = .{ .jump = .{
            .target = target,
            .arguments = try self.arena.allocator().dupe(ir.ValueId, arguments),
        } };
    }

    fn validated(self: *ConstructorProgram) !diagnostics.Report {
        const allocator = self.arena.allocator();
        for (self.blocks.items, self.block_instructions.items, self.block_parameters.items) |*item, instruction_list, parameter_list| {
            item.instructions = instruction_list.items;
            item.parameters = parameter_list.items;
        }
        const block_ids = try allocator.alloc(ir.BlockId, self.blocks.items.len);
        for (block_ids, 0..) |*id, index| id.* = ir.BlockId.fromIndex(index);
        const function: ir.Function = .{
            .id = function_id,
            .parameters = self.parameters.items,
            .blocks = block_ids,
            .entry_block = ir.BlockId.fromIndex(0),
        };
        const program: ir.Program = .{
            .program_id = "table-constructor-register-frame",
            .entry_function = function_id,
            .functions = try allocator.dupe(ir.Function, &.{function}),
            .blocks = self.blocks.items,
            .instructions = self.instructions.items,
            .values = self.values.items,
            .value_packs = self.packs.items,
        };
        var scope = try readable_scope.Scope.init(std.testing.allocator, &program);
        defer scope.deinit();
        var result = diagnostics.Report.init(std.testing.allocator);
        errdefer result.deinit();
        try validate(std.testing.allocator, &result, &program, &scope);
        return result;
    }
};

/// `count` string constants returned as one constructor.
fn manyItemsReport(count: usize) !diagnostics.Report {
    var builder = ConstructorProgram.init();
    defer builder.deinit();
    const entry = try builder.block();
    var fields: std.ArrayList(ir.TableConstructorField) = .empty;
    try builder.strings(entry, &fields, count, "s");
    try builder.returns(entry, &.{try builder.make(entry, fields.items, null)});
    return builder.validated();
}

test "a constructor with many array items takes one batch of sixteen registers" {
    for ([_]usize{ 255, 300, 1000 }) |count| {
        var report = try manyItemsReport(count);
        defer report.deinit();
        try std.testing.expectEqual(@as(usize, 0), report.diagnostics.items.len);
    }
}

/// The 16-level nested chain returned, its innermost level `innermost` strings.
fn nestedChainReport(innermost: usize) !diagnostics.Report {
    var builder = ConstructorProgram.init();
    defer builder.deinit();
    const entry = try builder.block();
    try builder.returns(entry, &.{try builder.chain(entry, 16, innermost)});
    return builder.validated();
}

test "a nested chain of constructors is built at its batch slots with each batch above the last" {
    var boundary = try nestedChainReport(14);
    defer boundary.deinit();
    try std.testing.expectEqual(@as(usize, 0), boundary.diagnostics.items.len);

    var excessive = try nestedChainReport(15);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

/// 19 strings, then the 15-level nested chain (innermost `innermost`) as the last item, at slot 3 of the second batch.
fn lastNestedChainReport(innermost: usize) !diagnostics.Report {
    var builder = ConstructorProgram.init();
    defer builder.deinit();
    const entry = try builder.block();
    var fields: std.ArrayList(ir.TableConstructorField) = .empty;
    try builder.strings(entry, &fields, 19, "w");
    const nested = try builder.chain(entry, 15, innermost);
    try fields.append(builder.arena.allocator(), .{ .list = nested });
    try builder.returns(entry, &.{try builder.make(entry, fields.items, null)});
    return builder.validated();
}

test "a nested chain as the last item of a partial batch is built above the batch" {
    var boundary = try lastNestedChainReport(14);
    defer boundary.deinit();
    try std.testing.expectEqual(@as(usize, 0), boundary.diagnostics.items.len);

    var excessive = try lastNestedChainReport(15);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

/// Parameters f and a; `string_count` strings, then f(a, ..., a) with `argument_count` arguments as the last item,
/// written in parentheses.
fn lastCallReport(string_count: usize, argument_count: usize) !diagnostics.Report {
    var builder = ConstructorProgram.init();
    defer builder.deinit();
    const entry = try builder.block();
    const callee = try builder.parameter();
    const argument = try builder.parameter();
    var fields: std.ArrayList(ir.TableConstructorField) = .empty;
    try builder.strings(entry, &fields, string_count, "w");
    const result = try builder.call(entry, callee, try builder.repeated(argument, argument_count));
    try fields.append(builder.arena.allocator(), .{ .list = result });
    try builder.returns(entry, &.{try builder.make(entry, fields.items, null)});
    return builder.validated();
}

test "a call in parentheses as the last item of a partial batch is built above the batch" {
    var boundary = try lastCallReport(19, 235);
    defer boundary.deinit();
    try std.testing.expectEqual(@as(usize, 0), boundary.diagnostics.items.len);

    var excessive = try lastCallReport(19, 236);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

test "a call as the last item at the last slot of its batch is built at its slot" {
    var boundary = try lastCallReport(15, 236);
    defer boundary.deinit();
    try std.testing.expectEqual(@as(usize, 0), boundary.diagnostics.items.len);

    var excessive = try lastCallReport(15, 237);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

/// 199 parameters (the last one a); 15 strings, then a .. a .. ... .. a with `operand_count` operands, then "z".
fn concatenationReport(operand_count: usize) !diagnostics.Report {
    var builder = ConstructorProgram.init();
    defer builder.deinit();
    const entry = try builder.block();
    var operand: ir.ValueId = undefined;
    for (0..199) |_| operand = try builder.parameter();
    var fields: std.ArrayList(ir.TableConstructorField) = .empty;
    try builder.strings(entry, &fields, 15, "w");
    var right = operand;
    for (1..operand_count) |_| {
        right = try builder.add(entry, .{ .binary = .{ .operator = .concat, .left = operand, .right = right } }, .dynamic_call, ir.ValueType.dynamic);
    }
    try fields.append(builder.arena.allocator(), .{ .list = right });
    const last = try builder.add(entry, .{ .constant = .{ .string = "z" } }, .pure, ir.ValueType.string);
    try fields.append(builder.arena.allocator(), .{ .list = last });
    try builder.returns(entry, &.{try builder.make(entry, fields.items, null)});
    return builder.validated();
}

test "a concatenation takes its operands in consecutive registers above its slot" {
    var boundary = try concatenationReport(39);
    defer boundary.deinit();
    try std.testing.expectEqual(@as(usize, 0), boundary.diagnostics.items.len);

    var excessive = try concatenationReport(40);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

/// Parameters f and a; 16 strings, then k1 = f(a, ..., a) with `argument_count` arguments.
fn keyedCallReport(argument_count: usize) !diagnostics.Report {
    var builder = ConstructorProgram.init();
    defer builder.deinit();
    const entry = try builder.block();
    const callee = try builder.parameter();
    const argument = try builder.parameter();
    var fields: std.ArrayList(ir.TableConstructorField) = .empty;
    try builder.strings(entry, &fields, 16, "w");
    const key = try builder.add(entry, .{ .constant = .{ .string = "k1" } }, .pure, ir.ValueType.string);
    const result = try builder.call(entry, callee, try builder.repeated(argument, argument_count));
    try fields.append(builder.arena.allocator(), .{ .keyed = .{ .key = key, .value = result } });
    try builder.returns(entry, &.{try builder.make(entry, fields.items, null)});
    return builder.validated();
}

test "a keyed field with a call is built above the whole batch with its name in a register" {
    var boundary = try keyedCallReport(234);
    defer boundary.deinit();
    try std.testing.expectEqual(@as(usize, 0), boundary.diagnostics.items.len);

    var excessive = try keyedCallReport(235);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

/// 10 strings, k1 = 1, the 16-level nested chain (innermost `innermost`), then "z".
fn keyedResetReport(innermost: usize) !diagnostics.Report {
    var builder = ConstructorProgram.init();
    defer builder.deinit();
    const entry = try builder.block();
    var fields: std.ArrayList(ir.TableConstructorField) = .empty;
    try builder.strings(entry, &fields, 10, "w");
    const key = try builder.add(entry, .{ .constant = .{ .string = "k1" } }, .pure, ir.ValueType.string);
    const one = try builder.add(entry, .{ .constant = .{ .number = 1 } }, .pure, ir.ValueType.number);
    try fields.append(builder.arena.allocator(), .{ .keyed = .{ .key = key, .value = one } });
    const nested = try builder.chain(entry, 16, innermost);
    try fields.append(builder.arena.allocator(), .{ .list = nested });
    const last = try builder.add(entry, .{ .constant = .{ .string = "z" } }, .pure, ir.ValueType.string);
    try fields.append(builder.arena.allocator(), .{ .list = last });
    try builder.returns(entry, &.{try builder.make(entry, fields.items, null)});
    return builder.validated();
}

test "the batch slot returns to zero after a keyed field" {
    var boundary = try keyedResetReport(13);
    defer boundary.deinit();
    try std.testing.expectEqual(@as(usize, 0), boundary.diagnostics.items.len);

    var excessive = try keyedResetReport(14);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

/// Parameters f and a; 19 strings, then f(a, ..., a) with `argument_count` arguments as the tail pack.
fn tailCallReport(argument_count: usize) !diagnostics.Report {
    var builder = ConstructorProgram.init();
    defer builder.deinit();
    const entry = try builder.block();
    const callee = try builder.parameter();
    const argument = try builder.parameter();
    var fields: std.ArrayList(ir.TableConstructorField) = .empty;
    try builder.strings(entry, &fields, 19, "w");
    const tail = try builder.packCall(entry, callee, try builder.repeated(argument, argument_count));
    try builder.returns(entry, &.{try builder.make(entry, fields.items, tail)});
    return builder.validated();
}

test "a call as the tail of a constructor is built at its slot" {
    var boundary = try tailCallReport(248);
    defer boundary.deinit();
    try std.testing.expectEqual(@as(usize, 0), boundary.diagnostics.items.len);

    var excessive = try tailCallReport(249);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

/// Parameters f, a, b and c (b and c strings); 15 strings, then f(a, ..., a, a and b .. c) with `argument_count`
/// arguments, then "z".
fn logicalArgumentReport(argument_count: usize) !diagnostics.Report {
    var builder = ConstructorProgram.init();
    defer builder.deinit();
    const entry = try builder.block();
    const callee = try builder.parameter();
    const argument = try builder.parameter();
    const left = try builder.parameter();
    const right = try builder.parameter();
    builder.values.items[left.index()].type = ir.ValueType.string;
    builder.values.items[right.index()].type = ir.ValueType.string;
    var fields: std.ArrayList(ir.TableConstructorField) = .empty;
    try builder.strings(entry, &fields, 15, "w");
    const joined = try builder.add(entry, .{ .binary = .{ .operator = .concat, .left = left, .right = right, .mode = .primitive } }, .pure, ir.ValueType.string);
    const both = try builder.add(entry, .{ .binary = .{ .operator = .logical_and, .left = argument, .right = joined } }, .pure, ir.ValueType.dynamic);
    const arguments = try builder.repeated(argument, argument_count);
    arguments[argument_count - 1] = both;
    const result = try builder.call(entry, callee, arguments);
    try fields.append(builder.arena.allocator(), .{ .list = result });
    const last = try builder.add(entry, .{ .constant = .{ .string = "z" } }, .pure, ir.ValueType.string);
    try fields.append(builder.arena.allocator(), .{ .list = last });
    try builder.returns(entry, &.{try builder.make(entry, fields.items, null)});
    return builder.validated();
}

test "an and whose right operand is not a register takes the larger frame of its two operands" {
    var boundary = try logicalArgumentReport(232);
    defer boundary.deinit();
    try std.testing.expectEqual(@as(usize, 0), boundary.diagnostics.items.len);

    var excessive = try logicalArgumentReport(233);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}

/// Parameters f, g, a and b; `string_count` strings, then f(a and g(b)) through a branch and its join, then "z". The
/// emitter may write the join as the branch composition `a and g(b)` in the call.
fn composedArgumentReport(string_count: usize) !diagnostics.Report {
    var builder = ConstructorProgram.init();
    defer builder.deinit();
    const entry = try builder.block();
    const right = try builder.block();
    const short = try builder.block();
    const join = try builder.block();
    const callee = try builder.parameter();
    const inner_callee = try builder.parameter();
    const condition = try builder.parameter();
    const argument = try builder.parameter();
    var fields: std.ArrayList(ir.TableConstructorField) = .empty;
    try builder.strings(entry, &fields, string_count, "w");
    builder.blocks.items[entry.index()].terminator = .{ .branch = .{
        .condition = condition,
        .then_edge = .{ .target = right },
        .else_edge = .{ .target = short },
    } };
    const inner = try builder.call(right, inner_callee, &.{argument});
    try builder.jump(right, join, &.{inner});
    try builder.jump(short, join, &.{condition});
    const joined = try builder.blockParameter(join);
    const result = try builder.call(join, callee, &.{joined});
    try fields.append(builder.arena.allocator(), .{ .list = result });
    const last = try builder.add(join, .{ .constant = .{ .string = "z" } }, .pure, ir.ValueType.string);
    try fields.append(builder.arena.allocator(), .{ .list = last });
    try builder.returns(join, &.{try builder.make(join, fields.items, null)});
    return builder.validated();
}

test "a constructor item that a branch composition may write keeps the per-field charge" {
    var report = try composedArgumentReport(253);
    defer report.deinit();
    try std.testing.expectEqual(@as(usize, 1), report.diagnostics.items.len);
    try std.testing.expect(report.contains(.unsupported_readable_temporary_register_pressure));
}
