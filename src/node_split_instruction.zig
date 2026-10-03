const std = @import("std");
const ir = @import("ir.zig");
const operator_domain = @import("operator_domain.zig");

fn IdMapping(comptime Id: type) type {
    return struct {
        ids: ?[]const Id = null,
        flags: ?[]const bool = null,

        fn contains(self: @This(), id: Id) bool {
            if (self.flags) |flags| return id.index() < flags.len and flags[id.index()];
            for (self.ids orelse &.{}) |mapped| if (mapped == id) return true;
            return false;
        }
    };
}

const ValueMapping = IdMapping(ir.ValueId);
const PackMapping = IdMapping(ir.ValuePackId);

pub fn sequenceIsCloneable(program: *const ir.Program, source: ir.Block) bool {
    return sequenceIsCloneableWithMappings(program, source, &.{}, &.{});
}

pub fn sequenceIsCloneableWithMappings(
    program: *const ir.Program,
    source: ir.Block,
    mapped_values: []const ir.ValueId,
    mapped_packs: []const ir.ValuePackId,
) bool {
    return sequenceIsCloneableWithAvailability(
        program,
        source,
        .{ .ids = mapped_values },
        .{ .ids = mapped_packs },
    );
}

pub fn sequenceIsCloneableWithMappedFlags(
    program: *const ir.Program,
    source: ir.Block,
    mapped_values: []const bool,
    mapped_packs: []const bool,
) bool {
    return sequenceIsCloneableWithAvailability(
        program,
        source,
        .{ .flags = mapped_values },
        .{ .flags = mapped_packs },
    );
}

fn sequenceIsCloneableWithAvailability(
    program: *const ir.Program,
    source: ir.Block,
    mapped_values: ValueMapping,
    mapped_packs: PackMapping,
) bool {
    if (!terminatorIsCloneable(source.terminator)) return false;
    for (source.instructions, 0..) |instruction_id, instruction_index| {
        if (instruction_id.index() >= program.instructions.len) return false;
        for (source.instructions[0..instruction_index]) |prior| if (prior == instruction_id) return false;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.id != instruction_id or
            instruction.block != source.id or
            instruction.results.len != (cloneableResultCount(instruction) orelse return false) or
            !resultShapeIsCloneable(program, source, instruction) or
            instruction.claims.len != 0 or
            !instructionEffectsAreCloneable(program, instruction.operation, instruction.effects) or
            !sourceOperationIsCloneable(
                program,
                source,
                instruction_index,
                instruction.operation,
                mapped_values,
                mapped_packs,
            )) return false;

        for (instruction.results, 0..) |result_id, result_index| {
            if (result_id.index() >= program.values.len) return false;
            const value = program.values[result_id.index()];
            if (value.id != result_id or value.function != source.function) return false;
            const origin = switch (value.origin) {
                .instruction_result => |origin| origin,
                else => return false,
            };
            if (origin.instruction != instruction_id or origin.index != result_index) return false;
        }
    }
    return true;
}

pub fn remapOperation(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    values: []const ir.Value,
    function: ir.FunctionId,
    operation: ir.Operation,
    source_values: []const ir.ValueId,
    clone_values: []const ir.ValueId,
    source_packs: []const ir.ValuePackId,
    clone_packs: []const ir.ValuePackId,
) std.mem.Allocator.Error!?ir.Operation {
    return switch (operation) {
        .pack_values => null,
        .constant => |literal| .{ .constant = literal },
        .function_ref => |function_id| .{ .function_ref = function_id },
        .copy => |value| .{ .copy = remapCloneSafeValue(program, values, function, value, source_values, clone_values) orelse return null },
        .unary => |unary| .{ .unary = .{
            .operator = unary.operator,
            .operand = remapCloneSafeValue(program, values, function, unary.operand, source_values, clone_values) orelse return null,
            .mode = unary.mode,
        } },
        .binary => |binary| .{ .binary = .{
            .operator = binary.operator,
            .left = remapCloneSafeValue(program, values, function, binary.left, source_values, clone_values) orelse return null,
            .right = remapCloneSafeValue(program, values, function, binary.right, source_values, clone_values) orelse return null,
            .mode = binary.mode,
            .shift_behavior = binary.shift_behavior,
        } },
        .call => |call| blk: {
            const callee = remapCloneSafeValue(program, values, function, call.callee, source_values, clone_values) orelse break :blk null;
            const argument_pack = if (call.argument_pack) |pack_id|
                remapPack(program, function, pack_id, source_packs, clone_packs) orelse break :blk null
            else
                null;
            const arguments = try remapValueListAlloc(
                allocator,
                program,
                values,
                function,
                call.arguments,
                source_values,
                clone_values,
            ) orelse break :blk null;
            break :blk .{ .call = .{
                .callee = callee,
                .arguments = arguments,
                .argument_pack = argument_pack,
                .result_arity = call.result_arity,
            } };
        },
        .call_repeated_table_get => |call| blk: {
            const callee = remapCloneSafeValue(program, values, function, call.callee, source_values, clone_values) orelse break :blk null;
            const prefix_arguments = try remapValueListAlloc(
                allocator,
                program,
                values,
                function,
                call.prefix_arguments,
                source_values,
                clone_values,
            ) orelse break :blk null;
            const table = remapCloneSafeValue(program, values, function, call.table, source_values, clone_values) orelse break :blk null;
            const key = remapCloneSafeValue(program, values, function, call.key, source_values, clone_values) orelse break :blk null;
            const from = remapCloneSafeValue(program, values, function, call.from, source_values, clone_values) orelse break :blk null;
            const to = remapCloneSafeValue(program, values, function, call.to, source_values, clone_values) orelse break :blk null;
            const step = remapCloneSafeValue(program, values, function, call.step, source_values, clone_values) orelse break :blk null;
            const counter = if (call.counter) |place_id| counter_block: {
                if (!placeIsCloneSafe(program, function, place_id)) break :counter_block null;
                break :counter_block place_id;
            } else null;
            break :blk .{ .call_repeated_table_get = .{
                .callee = callee,
                .prefix_arguments = prefix_arguments,
                .table = table,
                .key = key,
                .from = from,
                .to = to,
                .step = step,
                .counter = counter,
                .result_arity = call.result_arity,
            } };
        },
        .namecall => |namecall| blk: {
            const receiver = remapCloneSafeValue(program, values, function, namecall.receiver, source_values, clone_values) orelse break :blk null;
            const argument_pack = if (namecall.argument_pack) |pack_id|
                remapPack(program, function, pack_id, source_packs, clone_packs) orelse break :blk null
            else
                null;
            const arguments = try remapValueListAlloc(
                allocator,
                program,
                values,
                function,
                namecall.arguments,
                source_values,
                clone_values,
            ) orelse break :blk null;
            break :blk .{ .namecall = .{
                .receiver = receiver,
                .method = namecall.method,
                .arguments = arguments,
                .argument_pack = argument_pack,
                .result_arity = namecall.result_arity,
            } };
        },
        .protected_call => |protected_call| blk: {
            const callee = remapCloneSafeValue(program, values, function, protected_call.callee, source_values, clone_values) orelse break :blk null;
            const error_handler = if (protected_call.error_handler) |handler|
                remapCloneSafeValue(program, values, function, handler, source_values, clone_values) orelse break :blk null
            else
                null;
            const argument_pack = if (protected_call.argument_pack) |pack_id|
                remapPack(program, function, pack_id, source_packs, clone_packs) orelse break :blk null
            else
                null;
            const arguments = try remapValueListAlloc(
                allocator,
                program,
                values,
                function,
                protected_call.arguments,
                source_values,
                clone_values,
            ) orelse break :blk null;
            break :blk .{ .protected_call = .{
                .callee = callee,
                .error_handler = error_handler,
                .arguments = arguments,
                .argument_pack = argument_pack,
                .result_arity = protected_call.result_arity,
            } };
        },
        .coroutine_create => |coroutine_create| .{ .coroutine_create = .{
            .callee = remapCloneSafeValue(
                program,
                values,
                function,
                coroutine_create.callee,
                source_values,
                clone_values,
            ) orelse return null,
        } },
        .coroutine_resume => |coroutine_resume| blk: {
            const thread = remapCloneSafeValue(
                program,
                values,
                function,
                coroutine_resume.thread,
                source_values,
                clone_values,
            ) orelse break :blk null;
            const argument_pack = if (coroutine_resume.argument_pack) |pack_id|
                remapPack(program, function, pack_id, source_packs, clone_packs) orelse break :blk null
            else
                null;
            const arguments = try remapValueListAlloc(
                allocator,
                program,
                values,
                function,
                coroutine_resume.arguments,
                source_values,
                clone_values,
            ) orelse break :blk null;
            break :blk .{ .coroutine_resume = .{
                .thread = thread,
                .arguments = arguments,
                .argument_pack = argument_pack,
                .result_arity = coroutine_resume.result_arity,
            } };
        },
        .coroutine_yield => |coroutine_yield| blk: {
            const argument_pack = if (coroutine_yield.argument_pack) |pack_id|
                remapPack(program, function, pack_id, source_packs, clone_packs) orelse break :blk null
            else
                null;
            const arguments = try remapValueListAlloc(
                allocator,
                program,
                values,
                function,
                coroutine_yield.arguments,
                source_values,
                clone_values,
            ) orelse break :blk null;
            break :blk .{ .coroutine_yield = .{
                .arguments = arguments,
                .argument_pack = argument_pack,
                .result_arity = coroutine_yield.result_arity,
            } };
        },
        .make_table => .{ .make_table = {} },
        .make_table_literal => |constructor| blk: {
            const tail_pack = if (constructor.tail_pack) |pack_id|
                remapPack(program, function, pack_id, source_packs, clone_packs) orelse break :blk null
            else
                null;
            const fields = try remapTableFieldsAlloc(
                allocator,
                program,
                values,
                function,
                constructor.fields,
                source_values,
                clone_values,
            ) orelse break :blk null;
            break :blk .{ .make_table_literal = .{ .fields = fields, .tail_pack = tail_pack } };
        },
        .string_interpolate => |interpolation| blk: {
            const mapped_values = try remapValueListAlloc(
                allocator,
                program,
                values,
                function,
                interpolation.values,
                source_values,
                clone_values,
            ) orelse break :blk null;
            break :blk .{ .string_interpolate = .{
                .segments = interpolation.segments,
                .values = mapped_values,
            } };
        },
        .make_closure => |closure| blk: {
            const bindings = try remapClosureBindingsAlloc(
                allocator,
                program,
                values,
                function,
                closure.bindings,
                source_values,
                clone_values,
            ) orelse break :blk null;
            break :blk .{ .make_closure = .{
                .function = closure.function,
                .bindings = bindings,
            } };
        },
        .table_get => |table_get| .{ .table_get = .{
            .table = remapCloneSafeValue(program, values, function, table_get.table, source_values, clone_values) orelse return null,
            .key = remapCloneSafeValue(program, values, function, table_get.key, source_values, clone_values) orelse return null,
            .mode = table_get.mode,
        } },
        .table_set => |table_set| .{ .table_set = .{
            .table = remapCloneSafeValue(program, values, function, table_set.table, source_values, clone_values) orelse return null,
            .key = remapCloneSafeValue(program, values, function, table_set.key, source_values, clone_values) orelse return null,
            .value = remapCloneSafeValue(program, values, function, table_set.value, source_values, clone_values) orelse return null,
            .mode = table_set.mode,
        } },
        .table_set_pack => |table_set_pack| .{ .table_set_pack = .{
            .table = remapCloneSafeValue(program, values, function, table_set_pack.table, source_values, clone_values) orelse return null,
            .first_index = table_set_pack.first_index,
            .pack = remapPack(program, function, table_set_pack.pack, source_packs, clone_packs) orelse return null,
        } },
        .environment_get => |environment_get| .{ .environment_get = .{
            .target = remapEnvironmentTarget(program, values, function, environment_get.target, source_values, clone_values) orelse return null,
            .name = environment_get.name,
            .mode = environment_get.mode,
        } },
        .environment_set => |environment_set| if (environment_set.target == .ambient and environment_set.mode == .raw) null else .{ .environment_set = .{
            .target = remapEnvironmentTarget(program, values, function, environment_set.target, source_values, clone_values) orelse return null,
            .name = environment_set.name,
            .value = remapCloneSafeValue(program, values, function, environment_set.value, source_values, clone_values) orelse return null,
            .mode = environment_set.mode,
        } },
        .place_read => |place_id| if (!placeIsCloneSafe(program, function, place_id)) null else .{ .place_read = place_id },
        .place_write => |place_write| if (!placeIsCloneSafe(program, function, place_write.place)) null else .{ .place_write = .{
            .place = place_write.place,
            .value = remapCloneSafeValue(program, values, function, place_write.value, source_values, clone_values) orelse return null,
        } },
        .adjust_pack => |pack_id| .{
            .adjust_pack = remapPack(program, function, pack_id, source_packs, clone_packs) orelse return null,
        },
        .numeric_for_next => |next| .{ .numeric_for_next = .{
            .control = remapCloneSafeValue(program, values, function, next.control, source_values, clone_values) orelse return null,
            .limit = remapCloneSafeValue(program, values, function, next.limit, source_values, clone_values) orelse return null,
            .step = remapCloneSafeValue(program, values, function, next.step, source_values, clone_values) orelse return null,
            .initial = remapCloneSafeValue(program, values, function, next.initial, source_values, clone_values) orelse return null,
            .mode = next.mode,
        } },
        .generic_for_next => |next| .{ .generic_for_next = .{
            .iterator = remapCloneSafeValue(program, values, function, next.iterator, source_values, clone_values) orelse return null,
            .state = remapCloneSafeValue(program, values, function, next.state, source_values, clone_values) orelse return null,
            .control = remapCloneSafeValue(program, values, function, next.control, source_values, clone_values) orelse return null,
            .initial = remapCloneSafeValue(program, values, function, next.initial, source_values, clone_values) orelse return null,
            .variable_count = next.variable_count,
        } },
    };
}

pub fn deinitRemappedOperation(allocator: std.mem.Allocator, operation: ir.Operation) void {
    switch (operation) {
        .call => |call| if (call.arguments.len != 0) allocator.free(call.arguments),
        .call_repeated_table_get => |call| if (call.prefix_arguments.len != 0) allocator.free(call.prefix_arguments),
        .namecall => |namecall| if (namecall.arguments.len != 0) allocator.free(namecall.arguments),
        .protected_call => |protected_call| if (protected_call.arguments.len != 0) allocator.free(protected_call.arguments),
        .coroutine_resume => |coroutine_resume| if (coroutine_resume.arguments.len != 0) allocator.free(coroutine_resume.arguments),
        .coroutine_yield => |coroutine_yield| if (coroutine_yield.arguments.len != 0) allocator.free(coroutine_yield.arguments),
        .make_table_literal => |constructor| if (constructor.fields.len != 0) allocator.free(constructor.fields),
        .string_interpolate => |interpolation| if (interpolation.values.len != 0) allocator.free(interpolation.values),
        .make_closure => |closure| if (closure.bindings.len != 0) allocator.free(closure.bindings),
        else => {},
    }
}

pub fn sameOperation(left: ir.Operation, right: ir.Operation) bool {
    if (std.meta.activeTag(left) != std.meta.activeTag(right)) return false;
    return switch (left) {
        .constant => |literal| sameLiteral(literal, right.constant),
        .function_ref => |function_id| function_id == right.function_ref,
        .copy => |value| value == right.copy,
        .unary => |unary| unary.operator == right.unary.operator and
            unary.operand == right.unary.operand and unary.mode == right.unary.mode,
        .binary => |binary| binary.operator == right.binary.operator and
            binary.left == right.binary.left and binary.right == right.binary.right and
            binary.mode == right.binary.mode and binary.shift_behavior == right.binary.shift_behavior,
        .call => |call| call.callee == right.call.callee and
            call.argument_pack == right.call.argument_pack and
            sameResultArity(call.result_arity, right.call.result_arity) and
            std.mem.eql(ir.ValueId, call.arguments, right.call.arguments),
        .call_repeated_table_get => |call| call.callee == right.call_repeated_table_get.callee and
            std.mem.eql(ir.ValueId, call.prefix_arguments, right.call_repeated_table_get.prefix_arguments) and
            call.table == right.call_repeated_table_get.table and
            call.key == right.call_repeated_table_get.key and
            call.from == right.call_repeated_table_get.from and
            call.to == right.call_repeated_table_get.to and
            call.step == right.call_repeated_table_get.step and
            call.counter == right.call_repeated_table_get.counter and
            sameResultArity(call.result_arity, right.call_repeated_table_get.result_arity),
        .namecall => |namecall| namecall.receiver == right.namecall.receiver and
            std.mem.eql(u8, namecall.method, right.namecall.method) and
            namecall.argument_pack == right.namecall.argument_pack and
            sameResultArity(namecall.result_arity, right.namecall.result_arity) and
            std.mem.eql(ir.ValueId, namecall.arguments, right.namecall.arguments),
        .protected_call => |protected_call| protected_call.callee == right.protected_call.callee and
            protected_call.error_handler == right.protected_call.error_handler and
            protected_call.argument_pack == right.protected_call.argument_pack and
            sameResultArity(protected_call.result_arity, right.protected_call.result_arity) and
            std.mem.eql(ir.ValueId, protected_call.arguments, right.protected_call.arguments),
        .coroutine_create => |coroutine_create| coroutine_create.callee == right.coroutine_create.callee,
        .coroutine_resume => |coroutine_resume| coroutine_resume.thread == right.coroutine_resume.thread and
            coroutine_resume.argument_pack == right.coroutine_resume.argument_pack and
            sameResultArity(coroutine_resume.result_arity, right.coroutine_resume.result_arity) and
            std.mem.eql(ir.ValueId, coroutine_resume.arguments, right.coroutine_resume.arguments),
        .coroutine_yield => |coroutine_yield| coroutine_yield.argument_pack == right.coroutine_yield.argument_pack and
            sameResultArity(coroutine_yield.result_arity, right.coroutine_yield.result_arity) and
            std.mem.eql(ir.ValueId, coroutine_yield.arguments, right.coroutine_yield.arguments),
        .make_table => true,
        .make_table_literal => |constructor| constructor.tail_pack == right.make_table_literal.tail_pack and
            sameTableFields(constructor.fields, right.make_table_literal.fields),
        .string_interpolate => |interpolation| sameStringSegments(interpolation.segments, right.string_interpolate.segments) and
            std.mem.eql(ir.ValueId, interpolation.values, right.string_interpolate.values),
        .make_closure => |closure| closure.function == right.make_closure.function and
            sameClosureBindings(closure.bindings, right.make_closure.bindings),
        .table_get => |table_get| table_get.table == right.table_get.table and
            table_get.key == right.table_get.key and table_get.mode == right.table_get.mode,
        .table_set => |table_set| table_set.table == right.table_set.table and
            table_set.key == right.table_set.key and table_set.value == right.table_set.value and
            table_set.mode == right.table_set.mode,
        .table_set_pack => |operation| operation.table == right.table_set_pack.table and
            operation.first_index == right.table_set_pack.first_index and operation.pack == right.table_set_pack.pack,
        .environment_get => |environment_get| environment_get.mode == right.environment_get.mode and
            sameEnvironmentTarget(environment_get.target, right.environment_get.target) and
            std.mem.eql(u8, environment_get.name, right.environment_get.name),
        .environment_set => |environment_set| environment_set.mode == right.environment_set.mode and
            environment_set.value == right.environment_set.value and
            sameEnvironmentTarget(environment_set.target, right.environment_set.target) and
            std.mem.eql(u8, environment_set.name, right.environment_set.name),
        .place_read => |place_id| place_id == right.place_read,
        .place_write => |place_write| place_write.place == right.place_write.place and
            place_write.value == right.place_write.value,
        .pack_values => |values| std.mem.eql(ir.ValueId, values, right.pack_values),
        .adjust_pack => |pack_id| pack_id == right.adjust_pack,
        .numeric_for_next => |next| next.control == right.numeric_for_next.control and
            next.limit == right.numeric_for_next.limit and
            next.step == right.numeric_for_next.step and
            next.initial == right.numeric_for_next.initial and
            next.mode == right.numeric_for_next.mode,
        .generic_for_next => |next| next.iterator == right.generic_for_next.iterator and
            next.state == right.generic_for_next.state and
            next.control == right.generic_for_next.control and
            next.initial == right.generic_for_next.initial and
            next.variable_count == right.generic_for_next.variable_count,
    };
}

pub fn sameEffects(left: ir.EffectSummary, right: ir.EffectSummary) bool {
    return left.precision == right.precision and
        left.reads_memory == right.reads_memory and
        left.writes_memory == right.writes_memory and
        left.may_throw == right.may_throw and
        left.may_yield == right.may_yield and
        left.invokes_unknown_code == right.invokes_unknown_code;
}

fn sourceOperationIsCloneable(
    program: *const ir.Program,
    source: ir.Block,
    instruction_index: usize,
    operation: ir.Operation,
    mapped_values: ValueMapping,
    mapped_packs: PackMapping,
) bool {
    return switch (operation) {
        .constant, .function_ref => true,
        .copy => |value| sourceValueIsAvailable(program, source, instruction_index, value, mapped_values),
        .unary => |unary| sourceValueIsAvailable(program, source, instruction_index, unary.operand, mapped_values),
        .binary => |binary| sourceValueIsAvailable(program, source, instruction_index, binary.left, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, binary.right, mapped_values),
        .call => |call| (call.argument_pack == null or
            sourcePackIsAvailable(program, source, instruction_index, call.argument_pack.?, mapped_packs)) and
            sourceValueIsAvailable(program, source, instruction_index, call.callee, mapped_values) and
            sourceValuesAreAvailable(program, source, instruction_index, call.arguments, mapped_values),
        .call_repeated_table_get => |call| (call.counter == null or placeIsCloneSafe(program, source.function, call.counter.?)) and
            sourceValueIsAvailable(program, source, instruction_index, call.callee, mapped_values) and
            sourceValuesAreAvailable(program, source, instruction_index, call.prefix_arguments, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, call.table, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, call.key, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, call.from, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, call.to, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, call.step, mapped_values),
        .namecall => |namecall| namecall.method.len != 0 and
            (namecall.argument_pack == null or
                sourcePackIsAvailable(program, source, instruction_index, namecall.argument_pack.?, mapped_packs)) and
            sourceValueIsAvailable(program, source, instruction_index, namecall.receiver, mapped_values) and
            sourceValuesAreAvailable(program, source, instruction_index, namecall.arguments, mapped_values),
        .protected_call => |protected_call| (protected_call.argument_pack == null or
            sourcePackIsAvailable(program, source, instruction_index, protected_call.argument_pack.?, mapped_packs)) and
            sourceValueIsAvailable(program, source, instruction_index, protected_call.callee, mapped_values) and
            (protected_call.error_handler == null or
                sourceValueIsAvailable(program, source, instruction_index, protected_call.error_handler.?, mapped_values)) and
            sourceValuesAreAvailable(program, source, instruction_index, protected_call.arguments, mapped_values),
        .coroutine_create => |coroutine_create| sourceValueIsAvailable(program, source, instruction_index, coroutine_create.callee, mapped_values),
        .coroutine_resume => |coroutine_resume| sourceThreadIsAvailable(
            program,
            source,
            instruction_index,
            coroutine_resume.thread,
            mapped_values,
        ) and (coroutine_resume.argument_pack == null or
            sourcePackIsAvailable(program, source, instruction_index, coroutine_resume.argument_pack.?, mapped_packs)) and
            sourceValuesAreAvailable(program, source, instruction_index, coroutine_resume.arguments, mapped_values),
        .coroutine_yield => |coroutine_yield| (coroutine_yield.argument_pack == null or
            sourcePackIsAvailable(program, source, instruction_index, coroutine_yield.argument_pack.?, mapped_packs)) and
            sourceValuesAreAvailable(program, source, instruction_index, coroutine_yield.arguments, mapped_values),
        .make_table => true,
        .make_table_literal => |constructor| (constructor.tail_pack == null or
            sourcePackIsAvailable(program, source, instruction_index, constructor.tail_pack.?, mapped_packs)) and
            sourceTableFieldsAreAvailable(program, source, instruction_index, constructor.fields, mapped_values),
        .string_interpolate => |interpolation| sourceInterpolationIsCloneable(
            program,
            source,
            instruction_index,
            interpolation,
            mapped_values,
        ),
        .make_closure => |closure| sourceClosureIsCloneable(program, source, instruction_index, closure, mapped_values),
        .table_get => |table_get| sourceValueIsAvailable(program, source, instruction_index, table_get.table, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, table_get.key, mapped_values),
        .table_set => |table_set| sourceValueIsAvailable(program, source, instruction_index, table_set.table, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, table_set.key, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, table_set.value, mapped_values),
        .table_set_pack => |table_set_pack| sourceValueIsAvailable(program, source, instruction_index, table_set_pack.table, mapped_values) and
            sourcePackIsAvailable(program, source, instruction_index, table_set_pack.pack, mapped_packs),
        .environment_get => |environment_get| switch (environment_get.target) {
            .ambient => environment_get.mode == .semantic,
            .value => |target| sourceValueIsAvailable(program, source, instruction_index, target, mapped_values),
        },
        .environment_set => |environment_set| sourceValueIsAvailable(program, source, instruction_index, environment_set.value, mapped_values) and
            switch (environment_set.target) {
                .ambient => environment_set.mode == .semantic,
                .value => |target| sourceValueIsAvailable(program, source, instruction_index, target, mapped_values),
            },
        .place_read => |place_id| placeIsCloneSafe(program, source.function, place_id),
        .place_write => |place_write| placeIsCloneSafe(program, source.function, place_write.place) and
            sourceValueIsAvailable(program, source, instruction_index, place_write.value, mapped_values),
        .pack_values => false,
        .adjust_pack => |pack_id| sourcePackIsAvailable(program, source, instruction_index, pack_id, mapped_packs),
        .numeric_for_next => |next| sourceValueIsAvailable(program, source, instruction_index, next.control, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, next.limit, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, next.step, mapped_values) and
            sourceBooleanIsAvailable(program, source, instruction_index, next.initial, mapped_values),
        .generic_for_next => |next| next.variable_count != 0 and
            sourceValueIsAvailable(program, source, instruction_index, next.iterator, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, next.state, mapped_values) and
            sourceValueIsAvailable(program, source, instruction_index, next.control, mapped_values) and
            sourceBooleanIsAvailable(program, source, instruction_index, next.initial, mapped_values),
    };
}

fn cloneableResultCount(instruction: ir.Instruction) ?usize {
    return switch (instruction.operation) {
        .constant, .copy, .unary, .binary, .function_ref, .make_closure, .coroutine_create, .make_table, .make_table_literal, .string_interpolate, .table_get, .environment_get, .place_read => 1,
        .table_set, .table_set_pack, .environment_set, .place_write => 0,
        .call => |call| invocationOrdinaryResultCount(call.result_arity),
        .call_repeated_table_get => |call| invocationOrdinaryResultCount(call.result_arity),
        .namecall => |namecall| invocationOrdinaryResultCount(namecall.result_arity),
        .protected_call => |protected_call| invocationOrdinaryResultCount(protected_call.result_arity),
        .coroutine_resume => |coroutine_resume| invocationOrdinaryResultCount(coroutine_resume.result_arity),
        .coroutine_yield => |coroutine_yield| invocationOrdinaryResultCount(coroutine_yield.result_arity),
        .pack_values => null,
        .adjust_pack => instruction.results.len,
        .numeric_for_next => 4,
        .generic_for_next => |next| genericIterationResultCount(next.variable_count),
    };
}

fn invocationOrdinaryResultCount(result_arity: ir.ResultArity) usize {
    return switch (result_arity) {
        .fixed => |count| @intCast(count),
        .variadic => 0,
    };
}

fn resultShapeIsCloneable(program: *const ir.Program, source: ir.Block, instruction: ir.Instruction) bool {
    return switch (instruction.operation) {
        .call => |call| invocationPackResultIsCloneable(program, source, instruction, call.result_arity),
        .namecall => |namecall| invocationPackResultIsCloneable(program, source, instruction, namecall.result_arity),
        .protected_call => |protected_call| invocationPackResultIsCloneable(program, source, instruction, protected_call.result_arity) and
            statusPrefixResultIsCloneable(program, instruction, protected_call.result_arity),
        .coroutine_create => instruction.pack_result == null and coroutineCreateResultIsCloneable(program, instruction),
        .coroutine_resume => |coroutine_resume| invocationPackResultIsCloneable(program, source, instruction, coroutine_resume.result_arity) and
            statusPrefixResultIsCloneable(program, instruction, coroutine_resume.result_arity),
        .coroutine_yield => |coroutine_yield| invocationPackResultIsCloneable(program, source, instruction, coroutine_yield.result_arity),
        .make_table, .make_table_literal => instruction.pack_result == null and tableResultIsCloneable(program, instruction),
        .string_interpolate => instruction.pack_result == null and stringResultIsCloneable(program, instruction),
        .make_closure => instruction.pack_result == null and closureResultIsCloneable(program, instruction),
        .numeric_for_next => instruction.pack_result == null and numericIterationResultsAreCloneable(program, instruction),
        .generic_for_next => instruction.pack_result == null and genericIterationResultsAreCloneable(program, instruction),
        else => instruction.pack_result == null,
    };
}

fn coroutineCreateResultIsCloneable(program: *const ir.Program, instruction: ir.Instruction) bool {
    return singleResultDomainIsCloneable(program, instruction, .thread);
}

fn tableResultIsCloneable(program: *const ir.Program, instruction: ir.Instruction) bool {
    return singleResultDomainIsCloneable(program, instruction, .table);
}

fn stringResultIsCloneable(program: *const ir.Program, instruction: ir.Instruction) bool {
    return singleResultDomainIsCloneable(program, instruction, .string);
}

fn closureResultIsCloneable(program: *const ir.Program, instruction: ir.Instruction) bool {
    return singleResultDomainIsCloneable(program, instruction, .function);
}

fn numericIterationResultsAreCloneable(program: *const ir.Program, instruction: ir.Instruction) bool {
    const operation = switch (instruction.operation) {
        .numeric_for_next => |value| value,
        else => return false,
    };
    const expected = switch (operation.mode) {
        .luau_numeric => [_]ir.TypeKind{ .boolean, .number, .number, .number },
        .semantic_normalized => [_]ir.TypeKind{ .boolean, .dynamic, .dynamic, .dynamic },
    };
    if (instruction.results.len != expected.len) return false;
    for (instruction.results, expected) |result_id, kind| {
        if (!valueHasExactKind(program, result_id, kind)) return false;
    }
    return true;
}

fn genericIterationResultsAreCloneable(program: *const ir.Program, instruction: ir.Instruction) bool {
    return instruction.results.len != 0 and valueHasExactKind(program, instruction.results[0], .boolean);
}

fn valueHasExactKind(program: *const ir.Program, value_id: ir.ValueId, kind: ir.TypeKind) bool {
    if (value_id.index() >= program.values.len) return false;
    const value = program.values[value_id.index()];
    return value.id == value_id and value.type.kind == kind;
}

fn singleResultDomainIsCloneable(program: *const ir.Program, instruction: ir.Instruction, expected: ir.TypeKind) bool {
    if (instruction.results.len != 1) return false;
    const result_id = instruction.results[0];
    if (result_id.index() >= program.values.len) return false;
    const result = program.values[result_id.index()];
    return result.id == result_id and (result.type.kind == expected or result.type.kind == .dynamic);
}

fn statusPrefixResultIsCloneable(program: *const ir.Program, instruction: ir.Instruction, result_arity: ir.ResultArity) bool {
    return switch (result_arity) {
        .fixed => |count| blk: {
            if (count == 0 or instruction.results.len == 0) break :blk false;
            const status_id = instruction.results[0];
            if (status_id.index() >= program.values.len) break :blk false;
            const status = program.values[status_id.index()];
            break :blk status.id == status_id and (status.type.kind == .boolean or status.type.kind == .dynamic);
        },
        .variadic => blk: {
            const pack_id = instruction.pack_result orelse break :blk false;
            if (pack_id.index() >= program.value_packs.len) break :blk false;
            const shape = program.value_packs[pack_id.index()].shape;
            break :blk shape.tail == .open and shape.prefix.len != 0 and shape.prefix[0].kind == .boolean;
        },
    };
}

fn invocationPackResultIsCloneable(
    program: *const ir.Program,
    source: ir.Block,
    instruction: ir.Instruction,
    result_arity: ir.ResultArity,
) bool {
    return switch (result_arity) {
        .fixed => instruction.pack_result == null,
        .variadic => canonicalInstructionPack(program, source, instruction) != null,
    };
}

fn canonicalInstructionPack(program: *const ir.Program, source: ir.Block, instruction: ir.Instruction) ?ir.ValuePackId {
    const pack_id = instruction.pack_result orelse return null;
    if (pack_id.index() >= program.value_packs.len) return null;
    const pack = program.value_packs[pack_id.index()];
    if (pack.id != pack_id or pack.function != source.function) return null;
    return switch (pack.origin) {
        .instruction_result => |producer| if (producer == instruction.id) pack_id else null,
        .varargs => null,
    };
}

fn terminatorIsCloneable(terminator: ir.Terminator) bool {
    return switch (terminator) {
        .return_pack, .return_expanded => false,
        else => true,
    };
}

fn sourceValueIsAvailable(
    program: *const ir.Program,
    source: ir.Block,
    instruction_index: usize,
    value_id: ir.ValueId,
    mapped_values: ValueMapping,
) bool {
    if (mapped_values.contains(value_id)) return true;
    for (source.parameters) |parameter| if (parameter == value_id) return true;
    for (source.instructions[0..instruction_index]) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return false;
        for (program.instructions[instruction_id.index()].results) |result| if (result == value_id) return true;
    }

    // An entry-block constant can be reused from a different block because
    // the entry executes first.  It is not an external value when cloning the
    // entry block itself: in that case, only the earlier-instruction scan
    // above establishes availability, and a later constant must stay invalid.
    const function = canonicalFunction(program, source.function) orelse return false;
    if (source.id == function.entry_block) {
        if (value_id.index() >= program.values.len) return false;
        const value = program.values[value_id.index()];
        if (value.id == value_id and value.origin == .instruction_result) return false;
    }
    return externalValueIsCloneSafe(program, source.function, value_id);
}

fn sourceValuesAreAvailable(
    program: *const ir.Program,
    source: ir.Block,
    instruction_index: usize,
    values: []const ir.ValueId,
    mapped_values: ValueMapping,
) bool {
    for (values) |value| if (!sourceValueIsAvailable(program, source, instruction_index, value, mapped_values)) return false;
    return true;
}

fn sourceTableFieldsAreAvailable(
    program: *const ir.Program,
    source: ir.Block,
    instruction_index: usize,
    fields: []const ir.TableConstructorField,
    mapped_values: ValueMapping,
) bool {
    for (fields) |field| switch (field) {
        .list => |value| if (!sourceValueIsAvailable(program, source, instruction_index, value, mapped_values)) return false,
        .keyed => |keyed| if (!sourceValueIsAvailable(program, source, instruction_index, keyed.key, mapped_values) or
            !sourceValueIsAvailable(program, source, instruction_index, keyed.value, mapped_values)) return false,
    };
    return true;
}

fn sourceInterpolationIsCloneable(
    program: *const ir.Program,
    source: ir.Block,
    instruction_index: usize,
    interpolation: ir.StringInterpolation,
    mapped_values: ValueMapping,
) bool {
    const expected_segments = std.math.add(usize, interpolation.values.len, 1) catch return false;
    return interpolation.segments.len == expected_segments and
        sourceValuesAreAvailable(program, source, instruction_index, interpolation.values, mapped_values);
}

fn sourceClosureIsCloneable(
    program: *const ir.Program,
    source: ir.Block,
    instruction_index: usize,
    closure: ir.Closure,
    mapped_values: ValueMapping,
) bool {
    const target = canonicalFunction(program, closure.function) orelse return false;
    if (target.lexical_parent != source.function or
        target.captures.len != closure.bindings.len or
        !evidenceListIsCanonical(program, target.evidence)) return false;
    for (closure.bindings, 0..) |binding, index| {
        const capture = canonicalCapture(program, target, target.captures[index]) orelse return false;
        if (!evidenceListIsCanonical(program, capture.evidence) or
            !captureSlotIsCanonical(program, capture.*)) return false;
        switch (capture.kind) {
            .immutable_value => if (binding != .value or
                !sourceValueIsAvailable(program, source, instruction_index, binding.value, mapped_values)) return false,
            .shared_place => if (binding != .place or
                !placeIsCloneSafe(program, source.function, binding.place) or
                !placeEvidenceIsCanonical(program, binding.place)) return false,
        }
    }
    return true;
}

fn sourceThreadIsAvailable(
    program: *const ir.Program,
    source: ir.Block,
    instruction_index: usize,
    value_id: ir.ValueId,
    mapped_values: ValueMapping,
) bool {
    if (!sourceValueIsAvailable(program, source, instruction_index, value_id, mapped_values) or value_id.index() >= program.values.len) return false;
    const value = program.values[value_id.index()];
    return value.id == value_id and (value.type.kind == .thread or value.type.kind == .dynamic);
}

fn sourceBooleanIsAvailable(
    program: *const ir.Program,
    source: ir.Block,
    instruction_index: usize,
    value_id: ir.ValueId,
    mapped_values: ValueMapping,
) bool {
    if (!sourceValueIsAvailable(program, source, instruction_index, value_id, mapped_values) or value_id.index() >= program.values.len) return false;
    const value = program.values[value_id.index()];
    return value.id == value_id and (value.type.kind == .boolean or value.type.kind == .dynamic);
}

fn sourcePackIsAvailable(
    program: *const ir.Program,
    source: ir.Block,
    instruction_index: usize,
    pack_id: ir.ValuePackId,
    mapped_packs: PackMapping,
) bool {
    if (mapped_packs.contains(pack_id)) return true;
    for (source.instructions[0..instruction_index]) |instruction_id| {
        if (instruction_id.index() >= program.instructions.len) return false;
        const instruction = program.instructions[instruction_id.index()];
        if (instruction.pack_result == pack_id and canonicalInstructionPack(program, source, instruction) != null) return true;
    }
    return externalPackIsCloneSafe(program, source.function, pack_id);
}

fn externalPackIsCloneSafe(program: *const ir.Program, function_id: ir.FunctionId, pack_id: ir.ValuePackId) bool {
    const function = canonicalFunction(program, function_id) orelse return false;
    if (!function.is_variadic or function.vararg_pack != pack_id or pack_id.index() >= program.value_packs.len) return false;
    const pack = program.value_packs[pack_id.index()];
    if (pack.id != pack_id or pack.function != function_id or pack.shape.tail != .open or pack.shape.prefix.len != 0) return false;
    return switch (pack.origin) {
        .varargs => |owner| owner == function_id,
        .instruction_result => false,
    };
}

fn externalValueIsCloneSafe(program: *const ir.Program, function_id: ir.FunctionId, value_id: ir.ValueId) bool {
    const function = canonicalFunction(program, function_id) orelse return false;
    if (value_id.index() >= program.values.len) return false;
    const value = program.values[value_id.index()];
    if (value.id != value_id or value.function != function_id) return false;
    return switch (value.origin) {
        .parameter => |index| blk: {
            const parameter_index: usize = @intCast(index);
            break :blk parameter_index < function.parameters.len and
                function.parameters[parameter_index] == value_id and
                listedExactlyOnce(ir.ValueId, function.parameters, value_id);
        },
        .capture => |capture_id| blk: {
            const capture = canonicalCapture(program, function, capture_id) orelse break :blk false;
            break :blk switch (capture.kind) {
                .immutable_value => |captured_value| captured_value == value_id,
                .shared_place => false,
            };
        },
        .instruction_result => |origin| entryConstantIsCloneSafe(program, function, value_id, origin),
        .block_parameter => false,
    };
}

fn entryConstantIsCloneSafe(
    program: *const ir.Program,
    function: *const ir.Function,
    value_id: ir.ValueId,
    origin: anytype,
) bool {
    if (origin.index != 0 or
        !listedExactlyOnce(ir.BlockId, function.blocks, function.entry_block) or
        function.entry_block.index() >= program.blocks.len) return false;
    const entry = program.blocks[function.entry_block.index()];
    if (entry.id != function.entry_block or entry.function != function.id or
        !listedExactlyOnce(ir.InstructionId, entry.instructions, origin.instruction) or
        origin.instruction.index() >= program.instructions.len) return false;
    const instruction = program.instructions[origin.instruction.index()];
    if (instruction.id != origin.instruction or instruction.block != entry.id or
        instruction.results.len != 1 or instruction.results[0] != value_id or
        instruction.pack_result != null or instruction.claims.len != 0 or
        !std.meta.eql(instruction.effects, ir.EffectSummary.pure)) return false;
    return switch (instruction.operation) {
        .constant => true,
        else => false,
    };
}

fn canonicalFunction(program: *const ir.Program, function_id: ir.FunctionId) ?*const ir.Function {
    if (function_id.index() >= program.functions.len) return null;
    const function = &program.functions[function_id.index()];
    return if (function.id == function_id) function else null;
}

fn canonicalCapture(
    program: *const ir.Program,
    function: *const ir.Function,
    capture_id: ir.CaptureId,
) ?*const ir.Capture {
    if (!listedExactlyOnce(ir.CaptureId, function.captures, capture_id) or capture_id.index() >= program.captures.len) return null;
    const capture = &program.captures[capture_id.index()];
    if (capture.id != capture_id or capture.function != function.id) return null;
    if (function.lexical_parent) |parent_id| {
        if (parent_id == function.id or canonicalFunction(program, parent_id) == null) return null;
    } else if (!entryCaptureBindingIsCanonical(program, function, capture_id, capture.*)) {
        return null;
    }
    return capture;
}

fn entryCaptureBindingIsCanonical(
    program: *const ir.Program,
    function: *const ir.Function,
    capture_id: ir.CaptureId,
    capture: ir.Capture,
) bool {
    if (function.id != program.entry_function or function.captures.len != program.entry_bindings.len) return false;
    var capture_index: ?usize = null;
    for (function.captures, 0..) |candidate, index| {
        if (candidate != capture_id) continue;
        if (capture_index != null) return false;
        capture_index = index;
    }
    const index = capture_index orelse return false;
    const binding_id = program.entry_bindings[index];
    if (binding_id.index() >= program.external_bindings.len) return false;
    const binding = program.external_bindings[binding_id.index()];
    if (binding.id != binding_id or !evidenceListIsCanonical(program, binding.evidence)) return false;
    return switch (capture.kind) {
        .immutable_value => |value_id| blk: {
            if (binding.kind != .immutable_value or value_id.index() >= program.values.len) break :blk false;
            const value = program.values[value_id.index()];
            break :blk value.id == value_id and value.function == function.id and
                std.meta.eql(value.type, binding.type) and switch (value.origin) {
                .capture => |origin| origin == capture_id,
                else => false,
            };
        },
        .shared_place => |place_id| blk: {
            if (binding.kind != .shared_place or place_id.index() >= program.places.len) break :blk false;
            const place = program.places[place_id.index()];
            break :blk place.id == place_id and place.function == function.id and
                std.meta.eql(place.type, binding.type) and switch (place.origin) {
                .capture => |origin| origin == capture_id,
                else => false,
            };
        },
    };
}

fn evidenceListIsCanonical(program: *const ir.Program, evidence_ids: []const ir.EvidenceId) bool {
    for (evidence_ids) |evidence_id| {
        if (evidence_id.index() >= program.evidence.len) return false;
        const evidence = program.evidence[evidence_id.index()];
        if (evidence.id != evidence_id or evidence.locator.len == 0 or
            (evidence.digest != null and evidence.digest.?.len == 0)) return false;
    }
    return true;
}

fn placeEvidenceIsCanonical(program: *const ir.Program, place_id: ir.PlaceId) bool {
    if (place_id.index() >= program.places.len) return false;
    const place = program.places[place_id.index()];
    return place.id == place_id and evidenceListIsCanonical(program, place.evidence);
}

fn captureSlotIsCanonical(program: *const ir.Program, capture: ir.Capture) bool {
    return switch (capture.kind) {
        .immutable_value => |value_id| blk: {
            if (value_id.index() >= program.values.len) break :blk false;
            const value = program.values[value_id.index()];
            const origin_matches = switch (value.origin) {
                .capture => |capture_id| capture_id == capture.id,
                else => false,
            };
            break :blk value.id == value_id and value.function == capture.function and origin_matches;
        },
        .shared_place => |place_id| blk: {
            if (place_id.index() >= program.places.len) break :blk false;
            const place = program.places[place_id.index()];
            const origin_matches = switch (place.origin) {
                .capture => |capture_id| capture_id == capture.id,
                else => false,
            };
            break :blk place.id == place_id and place.function == capture.function and origin_matches and
                evidenceListIsCanonical(program, place.evidence);
        },
    };
}

fn listedExactlyOnce(comptime Id: type, items: []const Id, target: Id) bool {
    var found = false;
    for (items) |item| {
        if (item != target) continue;
        if (found) return false;
        found = true;
    }
    return found;
}

fn placeIsCloneSafe(program: *const ir.Program, function_id: ir.FunctionId, place_id: ir.PlaceId) bool {
    const function = canonicalFunction(program, function_id) orelse return false;
    if (place_id.index() >= program.places.len) return false;
    const place = program.places[place_id.index()];
    if (place.id != place_id or place.function != function_id) return false;
    return switch (place.origin) {
        .local => |index| blk: {
            const place_index: usize = @intCast(index);
            break :blk place_index < function.local_places.len and
                function.local_places[place_index] == place_id and
                listedExactlyOnce(ir.PlaceId, function.local_places, place_id);
        },
        .capture => |capture_id| blk: {
            const capture = canonicalCapture(program, function, capture_id) orelse break :blk false;
            break :blk switch (capture.kind) {
                .shared_place => |captured_place| captured_place == place_id,
                .immutable_value => false,
            };
        },
        .instruction => false,
    };
}

fn remapCloneSafeValue(
    program: *const ir.Program,
    values: []const ir.Value,
    function: ir.FunctionId,
    value: ir.ValueId,
    source_values: []const ir.ValueId,
    clone_values: []const ir.ValueId,
) ?ir.ValueId {
    for (source_values, clone_values) |source, clone| if (value == source) return clone;
    if (value.index() >= values.len) return null;
    return if (externalValueIsCloneSafe(program, function, value)) value else null;
}

fn remapValueListAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    values: []const ir.Value,
    function: ir.FunctionId,
    arguments: []const ir.ValueId,
    source_values: []const ir.ValueId,
    clone_values: []const ir.ValueId,
) std.mem.Allocator.Error!?[]const ir.ValueId {
    if (arguments.len == 0) return &.{};
    const mapped = try allocator.alloc(ir.ValueId, arguments.len);
    for (arguments, 0..) |argument, index| {
        mapped[index] = remapCloneSafeValue(program, values, function, argument, source_values, clone_values) orelse {
            allocator.free(mapped);
            return null;
        };
    }
    return mapped;
}

fn remapClosureBindingsAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    values: []const ir.Value,
    function: ir.FunctionId,
    bindings: []const ir.CaptureBinding,
    source_values: []const ir.ValueId,
    clone_values: []const ir.ValueId,
) std.mem.Allocator.Error!?[]const ir.CaptureBinding {
    if (bindings.len == 0) return &.{};
    const mapped = try allocator.alloc(ir.CaptureBinding, bindings.len);
    for (bindings, 0..) |binding, index| {
        mapped[index] = switch (binding) {
            .value => |value| .{ .value = remapCloneSafeValue(
                program,
                values,
                function,
                value,
                source_values,
                clone_values,
            ) orelse {
                allocator.free(mapped);
                return null;
            } },
            .place => |place| if (placeIsCloneSafe(program, function, place))
                .{ .place = place }
            else {
                allocator.free(mapped);
                return null;
            },
        };
    }
    return mapped;
}

fn remapTableFieldsAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    values: []const ir.Value,
    function: ir.FunctionId,
    fields: []const ir.TableConstructorField,
    source_values: []const ir.ValueId,
    clone_values: []const ir.ValueId,
) std.mem.Allocator.Error!?[]const ir.TableConstructorField {
    if (fields.len == 0) return &.{};
    const mapped = try allocator.alloc(ir.TableConstructorField, fields.len);
    for (fields, 0..) |field, index| {
        mapped[index] = switch (field) {
            .list => |value| .{ .list = remapCloneSafeValue(program, values, function, value, source_values, clone_values) orelse {
                allocator.free(mapped);
                return null;
            } },
            .keyed => |keyed| .{ .keyed = .{
                .key = remapCloneSafeValue(program, values, function, keyed.key, source_values, clone_values) orelse {
                    allocator.free(mapped);
                    return null;
                },
                .value = remapCloneSafeValue(program, values, function, keyed.value, source_values, clone_values) orelse {
                    allocator.free(mapped);
                    return null;
                },
            } },
        };
    }
    return mapped;
}

fn remapPack(
    program: *const ir.Program,
    function: ir.FunctionId,
    pack_id: ir.ValuePackId,
    source_packs: []const ir.ValuePackId,
    clone_packs: []const ir.ValuePackId,
) ?ir.ValuePackId {
    for (source_packs, clone_packs) |source, clone| if (pack_id == source) return clone;
    return if (externalPackIsCloneSafe(program, function, pack_id)) pack_id else null;
}

fn remapEnvironmentTarget(
    program: *const ir.Program,
    values: []const ir.Value,
    function: ir.FunctionId,
    target: ir.EnvironmentTarget,
    source_values: []const ir.ValueId,
    clone_values: []const ir.ValueId,
) ?ir.EnvironmentTarget {
    return switch (target) {
        .ambient => .{ .ambient = {} },
        .value => |value| .{ .value = remapCloneSafeValue(program, values, function, value, source_values, clone_values) orelse return null },
    };
}

fn sameEnvironmentTarget(left: ir.EnvironmentTarget, right: ir.EnvironmentTarget) bool {
    if (std.meta.activeTag(left) != std.meta.activeTag(right)) return false;
    return switch (left) {
        .ambient => true,
        .value => |value| value == right.value,
    };
}

fn sameResultArity(left: ir.ResultArity, right: ir.ResultArity) bool {
    if (std.meta.activeTag(left) != std.meta.activeTag(right)) return false;
    return switch (left) {
        .fixed => |count| count == right.fixed,
        .variadic => true,
    };
}

fn sameTableFields(left: []const ir.TableConstructorField, right: []const ir.TableConstructorField) bool {
    if (left.len != right.len) return false;
    for (left, right) |left_field, right_field| {
        if (std.meta.activeTag(left_field) != std.meta.activeTag(right_field)) return false;
        switch (left_field) {
            .list => |value| if (value != right_field.list) return false,
            .keyed => |keyed| if (keyed.key != right_field.keyed.key or keyed.value != right_field.keyed.value) return false,
        }
    }
    return true;
}

fn sameClosureBindings(left: []const ir.CaptureBinding, right: []const ir.CaptureBinding) bool {
    if (left.len != right.len) return false;
    for (left, right) |left_binding, right_binding| {
        if (std.meta.activeTag(left_binding) != std.meta.activeTag(right_binding)) return false;
        switch (left_binding) {
            .value => |value| if (value != right_binding.value) return false,
            .place => |place| if (place != right_binding.place) return false,
        }
    }
    return true;
}

fn sameStringSegments(left: []const []const u8, right: []const []const u8) bool {
    if (left.len != right.len) return false;
    for (left, right) |left_segment, right_segment| {
        if (!std.mem.eql(u8, left_segment, right_segment)) return false;
    }
    return true;
}

fn sameLiteral(left: ir.Literal, right: ir.Literal) bool {
    if (std.meta.activeTag(left) != std.meta.activeTag(right)) return false;
    return switch (left) {
        .nil_value => true,
        .boolean => |value| value == right.boolean,
        .integer => |value| std.mem.eql(u8, value, right.integer),
        .number => |value| @as(u64, @bitCast(value)) == @as(u64, @bitCast(right.number)),
        .special_number => |value| value == right.special_number,
        .string => |value| std.mem.eql(u8, value, right.string),
    };
}

fn isExactPure(effects: ir.EffectSummary) bool {
    return effects.precision == .exact and
        !effects.reads_memory and
        !effects.writes_memory and
        !effects.may_throw and
        !effects.may_yield and
        !effects.invokes_unknown_code;
}

fn instructionEffectsAreCloneable(
    program: *const ir.Program,
    operation: ir.Operation,
    effects: ir.EffectSummary,
) bool {
    return switch (operation) {
        .pack_values => false,
        .constant, .copy, .function_ref => isExactPure(effects),
        .unary => |unary| if (operator_domain.unaryIsStatic(program.values, unary))
            isExactPure(effects) or sameEffects(effects, ir.EffectSummary.dynamic_call)
        else
            unary.mode == .semantic and sameEffects(effects, ir.EffectSummary.dynamic_call),
        .binary => |binary| if (operator_domain.binaryIsStatic(program.values, binary))
            isExactPure(effects) or sameEffects(effects, ir.EffectSummary.dynamic_call)
        else
            binary.mode == .semantic and sameEffects(effects, ir.EffectSummary.dynamic_call),
        .call => sameEffects(effects, ir.EffectSummary.dynamic_call),
        .call_repeated_table_get => sameEffects(effects, ir.EffectSummary.dynamic_call),
        .namecall => sameEffects(effects, ir.EffectSummary.namecall),
        .protected_call => sameEffects(effects, ir.EffectSummary.protected_invocation),
        .coroutine_create => sameEffects(effects, ir.EffectSummary.coroutine_create),
        .coroutine_resume => sameEffects(effects, ir.EffectSummary.coroutine_resume),
        .coroutine_yield => sameEffects(effects, ir.EffectSummary.coroutine_yield),
        .make_table, .make_table_literal => sameEffects(effects, ir.EffectSummary.table_constructor),
        .string_interpolate => sameEffects(effects, ir.EffectSummary.string_interpolation),
        .make_closure => isExactPure(effects),
        .table_get => |table_get| sameEffects(
            effects,
            if (table_get.mode == .raw) ir.EffectSummary.raw_table_read else ir.EffectSummary.semantic_table_read,
        ),
        .table_set => |table_set| sameEffects(
            effects,
            if (table_set.mode == .raw) ir.EffectSummary.raw_table_write else ir.EffectSummary.semantic_table_write,
        ),
        .table_set_pack => sameEffects(effects, ir.EffectSummary.raw_table_write),
        .environment_get => |environment_get| if (environment_get.target == .ambient and environment_get.mode == .raw)
            false
        else
            sameEffects(
                effects,
                if (environment_get.mode == .raw) ir.EffectSummary.raw_table_read else ir.EffectSummary.semantic_environment_read,
            ),
        .environment_set => |environment_set| if (environment_set.target == .ambient and environment_set.mode == .raw)
            false
        else
            sameEffects(
                effects,
                if (environment_set.mode == .raw) ir.EffectSummary.raw_table_write else ir.EffectSummary.semantic_environment_write,
            ),
        .place_read => sameEffects(effects, ir.EffectSummary.place_read),
        .place_write => sameEffects(effects, ir.EffectSummary.place_write),
        .adjust_pack => isExactPure(effects),
        .numeric_for_next => |numeric| sameEffects(effects, switch (numeric.mode) {
            .luau_numeric => ir.EffectSummary.numeric_for_next,
            .semantic_normalized => ir.EffectSummary.dynamic_call,
        }),
        .generic_for_next => sameEffects(effects, ir.EffectSummary.generic_for_next),
    };
}

fn genericIterationResultCount(variable_count: u16) ?usize {
    if (variable_count == 0) return null;
    return std.math.add(usize, @as(usize, variable_count), 3) catch null;
}
