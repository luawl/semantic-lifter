const std = @import("std");
const diagnostics = @import("diagnostics.zig");
const emit_luau = @import("emit_luau.zig");
const fixtures = @import("fixtures.zig");
const ir = @import("ir.zig");
const pack_plan = @import("pack_plan.zig");
const readable_scope = @import("readable_scope.zig");
const register_validation = @import("validate_luau_registers.zig");
const validation = @import("validate.zig");

const TailConsumer = enum {
    invocation,
    table_literal,
    table_write,
};

fn expectStoredReturn(
    program: *const ir.Program,
    producer_id: ir.InstructionId,
    effect_id: ir.InstructionId,
    return_block_id: ir.BlockId,
) ![]u8 {
    var plan = try pack_plan.Plan.init(std.testing.allocator, program);
    defer plan.deinit();
    try std.testing.expect(plan.role(producer_id) == .stored_invocation_producer);
    try std.testing.expect(plan.role(effect_id) == .ordinary);
    try std.testing.expectEqual(
        pack_plan.TerminatorRole{ .stored_pack_return = producer_id },
        plan.terminatorRole(return_block_id),
    );

    var core_report = try validation.validate(std.testing.allocator, program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try validation.validate(std.testing.allocator, program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());

    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, program);
    errdefer std.testing.allocator.free(source);
    const producer_offset = std.mem.indexOf(u8, source, "end)(produce())") orelse return error.TestUnexpectedResult;
    const effect_offset = std.mem.indexOf(u8, source, "local observed = after_producer") orelse return error.TestUnexpectedResult;
    const return_offset = std.mem.indexOf(u8, source, "return observed, observed, __lifter_table_unpack(") orelse return error.TestUnexpectedResult;
    try std.testing.expect(producer_offset < effect_offset);
    try std.testing.expect(effect_offset < return_offset);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "produce()"));
    return source;
}

test "return-only open pack storage preserves producer before observable prefix" {
    const fixture = fixtures.open_pack_adjust_module;
    var values = fixture.values;
    values[fixture.v_callee.index()].name_hint = "produce";
    values[fixture.v_first.index()].name_hint = "observed";
    var instructions = fixture.instructions;
    instructions[fixture.i_adjust.index()] = .{
        .id = fixture.i_adjust,
        .block = fixture.b_entry,
        .operation = .{ .environment_get = .{
            .target = .{ .ambient = {} },
            .name = "after_producer",
        } },
        .results = &.{fixture.v_first},
        .effects = .semantic_environment_read,
        .evidence = &.{fixture.proof},
    };
    const same_block_ids = [_]ir.InstructionId{ fixture.i_get, fixture.i_call, fixture.i_adjust };
    var same_blocks = fixture.blocks;
    same_blocks[fixture.b_entry.index()].instructions = &same_block_ids;
    same_blocks[fixture.b_entry.index()].terminator = .{ .return_expanded = .{
        .values = &.{ fixture.v_first, fixture.v_first },
        .pack = fixture.p_results,
    } };
    var same_program = fixture.program;
    same_program.values = &values;
    same_program.instructions = &instructions;
    same_program.blocks = &same_blocks;

    const same_source = try expectStoredReturn(
        &same_program,
        fixture.i_call,
        fixture.i_adjust,
        fixture.b_entry,
    );
    defer std.testing.allocator.free(same_source);

    const return_block = ir.BlockId.fromIndex(fixture.blocks.len);
    instructions[fixture.i_adjust.index()].block = return_block;
    const producer_ids = [_]ir.InstructionId{ fixture.i_get, fixture.i_call };
    const return_ids = [_]ir.InstructionId{fixture.i_adjust};
    var cross_blocks = fixture.blocks ++ [_]ir.Block{.{
        .id = return_block,
        .function = fixture.f_entry,
        .instructions = &return_ids,
        .terminator = .{ .return_expanded = .{
            .values = &.{ fixture.v_first, fixture.v_first },
            .pack = fixture.p_results,
        } },
        .evidence = &.{fixture.proof},
    }};
    cross_blocks[fixture.b_entry.index()].instructions = &producer_ids;
    cross_blocks[fixture.b_entry.index()].terminator = .{ .jump = .{ .target = return_block } };
    const function_blocks = [_]ir.BlockId{ fixture.b_entry, return_block };
    var functions = fixture.functions;
    functions[fixture.f_entry.index()].blocks = &function_blocks;
    var cross_program = fixture.program;
    cross_program.functions = &functions;
    cross_program.blocks = &cross_blocks;
    cross_program.instructions = &instructions;
    cross_program.values = &values;

    const cross_source = try expectStoredReturn(
        &cross_program,
        fixture.i_call,
        fixture.i_adjust,
        return_block,
    );
    defer std.testing.allocator.free(cross_source);
}

test "single-use open pack tails store across observable effects" {
    const function_id = ir.FunctionId.fromIndex(0);
    const producer_block_id = ir.BlockId.fromIndex(0);
    const consumer_block_id = ir.BlockId.fromIndex(1);
    const producer_id = ir.InstructionId.fromIndex(0);
    const effect_id = ir.InstructionId.fromIndex(1);
    const consumer_id = ir.InstructionId.fromIndex(2);
    const producer_value = ir.ValueId.fromIndex(0);
    const consumer_value = ir.ValueId.fromIndex(1);
    const table_value = ir.ValueId.fromIndex(2);
    const observed_value = ir.ValueId.fromIndex(3);
    const result_value = ir.ValueId.fromIndex(4);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);
    const evidence_ids = [_]ir.EvidenceId{proof};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-stored-pack-tail",
    }};
    const packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = function_id,
        .origin = .{ .instruction_result = producer_id },
        .evidence = &evidence_ids,
    }};

    for ([_]TailConsumer{ .invocation, .table_literal, .table_write }) |consumer_kind| {
        for ([_]bool{ false, true }) |cross_block| {
            var values = [_]ir.Value{
                .{ .id = producer_value, .function = function_id, .type = .function, .name_hint = "produce", .origin = .{ .parameter = 0 } },
                .{ .id = consumer_value, .function = function_id, .type = .function, .name_hint = "consume", .origin = .{ .parameter = 1 } },
                .{ .id = table_value, .function = function_id, .type = .{ .kind = .table }, .name_hint = "target", .origin = .{ .parameter = 2 } },
                .{ .id = observed_value, .function = function_id, .name_hint = "observed", .origin = .{ .instruction_result = .{ .instruction = effect_id, .index = 0 } } },
                .{ .id = result_value, .function = function_id, .name_hint = "result", .origin = .{ .instruction_result = .{ .instruction = consumer_id, .index = 0 } } },
            };
            if (consumer_kind == .table_literal) values[result_value.index()].type = .{ .kind = .table };
            var instructions = [_]ir.Instruction{
                .{
                    .id = producer_id,
                    .block = producer_block_id,
                    .operation = .{ .call = .{
                        .callee = producer_value,
                        .arguments = &.{},
                        .result_arity = .{ .variadic = {} },
                    } },
                    .results = &.{},
                    .pack_result = pack_id,
                    .effects = .dynamic_call,
                    .evidence = &evidence_ids,
                },
                .{
                    .id = effect_id,
                    .block = if (cross_block) consumer_block_id else producer_block_id,
                    .operation = .{ .environment_get = .{
                        .target = .{ .ambient = {} },
                        .name = "after_producer",
                    } },
                    .results = &.{observed_value},
                    .effects = .semantic_environment_read,
                    .evidence = &evidence_ids,
                },
                undefined,
            };
            instructions[consumer_id.index()] = switch (consumer_kind) {
                .invocation => .{
                    .id = consumer_id,
                    .block = if (cross_block) consumer_block_id else producer_block_id,
                    .operation = .{ .call = .{
                        .callee = consumer_value,
                        .arguments = &.{observed_value},
                        .argument_pack = pack_id,
                        .result_arity = .{ .fixed = 1 },
                    } },
                    .results = &.{result_value},
                    .effects = .dynamic_call,
                    .evidence = &evidence_ids,
                },
                .table_literal => .{
                    .id = consumer_id,
                    .block = if (cross_block) consumer_block_id else producer_block_id,
                    .operation = .{ .make_table_literal = .{
                        .fields = &.{.{ .list = observed_value }},
                        .tail_pack = pack_id,
                    } },
                    .results = &.{result_value},
                    .effects = .table_constructor,
                    .evidence = &evidence_ids,
                },
                .table_write => .{
                    .id = consumer_id,
                    .block = if (cross_block) consumer_block_id else producer_block_id,
                    .operation = .{ .table_set_pack = .{
                        .table = table_value,
                        .first_index = 2,
                        .pack = pack_id,
                    } },
                    .results = &.{},
                    .effects = .raw_table_write,
                    .evidence = &evidence_ids,
                },
            };

            const producer_ids = [_]ir.InstructionId{producer_id};
            const consumer_ids = [_]ir.InstructionId{ effect_id, consumer_id };
            const same_block_ids = [_]ir.InstructionId{ producer_id, effect_id, consumer_id };
            var blocks = [_]ir.Block{
                .{
                    .id = producer_block_id,
                    .function = function_id,
                    .instructions = if (cross_block) &producer_ids else &same_block_ids,
                    .terminator = if (cross_block)
                        .{ .jump = .{ .target = consumer_block_id } }
                    else if (consumer_kind == .table_write)
                        .{ .return_values = &.{} }
                    else
                        .{ .return_values = &.{result_value} },
                    .evidence = &evidence_ids,
                },
                .{
                    .id = consumer_block_id,
                    .function = function_id,
                    .instructions = &consumer_ids,
                    .terminator = if (consumer_kind == .table_write)
                        .{ .return_values = &.{} }
                    else
                        .{ .return_values = &.{result_value} },
                    .evidence = &evidence_ids,
                },
            };
            const block_ids = [_]ir.BlockId{ producer_block_id, consumer_block_id };
            const same_block = [_]ir.BlockId{producer_block_id};
            const functions = [_]ir.Function{.{
                .id = function_id,
                .parameters = &.{ producer_value, consumer_value, table_value },
                .blocks = if (cross_block) &block_ids else &same_block,
                .entry_block = producer_block_id,
                .evidence = &evidence_ids,
            }};
            const program: ir.Program = .{
                .program_id = "generic-stored-pack-tail",
                .entry_function = function_id,
                .functions = &functions,
                .blocks = if (cross_block) &blocks else blocks[0..1],
                .instructions = &instructions,
                .values = if (consumer_kind == .table_write) values[0..4] else &values,
                .value_packs = &packs,
                .evidence = &evidence,
            };

            var plan = try pack_plan.Plan.init(std.testing.allocator, &program);
            defer plan.deinit();
            try std.testing.expect(plan.role(producer_id) == .stored_invocation_producer);
            try std.testing.expect(plan.storedPackServesInstruction(producer_id, consumer_id));
            try std.testing.expect(plan.role(effect_id) == .ordinary);
            try std.testing.expect(plan.role(consumer_id) == .ordinary);

            var core_report = try validation.validate(std.testing.allocator, &program, .core);
            defer core_report.deinit();
            try std.testing.expect(core_report.isClean());
            var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
            defer readable_report.deinit();
            try std.testing.expect(readable_report.isClean());

            const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
            defer std.testing.allocator.free(source);
            const producer_offset = std.mem.indexOf(u8, source, "end)(produce())") orelse return error.TestUnexpectedResult;
            const effect_offset = std.mem.indexOf(u8, source, "after_producer") orelse return error.TestUnexpectedResult;
            const consumer_offset = std.mem.indexOf(u8, source, "__lifter_table_unpack(") orelse return error.TestUnexpectedResult;
            try std.testing.expect(producer_offset < effect_offset);
            try std.testing.expect(effect_offset < consumer_offset);
            try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "produce()"));
            try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "__lifter_table_unpack("));
        }
    }
}

test "multiple delayed open pack tails share one authenticated carrier" {
    const function_id = ir.FunctionId.fromIndex(0);
    const producer_block = ir.BlockId.fromIndex(0);
    const consumer_block = ir.BlockId.fromIndex(1);
    const producer_id = ir.InstructionId.fromIndex(0);
    const effect_id = ir.InstructionId.fromIndex(1);
    const adjust_id = ir.InstructionId.fromIndex(2);
    const first_call_id = ir.InstructionId.fromIndex(3);
    const second_call_id = ir.InstructionId.fromIndex(4);
    const literal_id = ir.InstructionId.fromIndex(5);
    const write_id = ir.InstructionId.fromIndex(6);
    const producer = ir.ValueId.fromIndex(0);
    const consumer = ir.ValueId.fromIndex(1);
    const target = ir.ValueId.fromIndex(2);
    const adjusted_result = ir.ValueId.fromIndex(3);
    const first_result = ir.ValueId.fromIndex(4);
    const second_result = ir.ValueId.fromIndex(5);
    const literal_result = ir.ValueId.fromIndex(6);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);
    const evidence_ids = [_]ir.EvidenceId{proof};
    const values = [_]ir.Value{
        .{ .id = producer, .function = function_id, .type = .function, .name_hint = "produce", .origin = .{ .parameter = 0 } },
        .{ .id = consumer, .function = function_id, .type = .function, .name_hint = "consume", .origin = .{ .parameter = 1 } },
        .{ .id = target, .function = function_id, .type = .{ .kind = .table }, .name_hint = "target", .origin = .{ .parameter = 2 } },
        .{ .id = adjusted_result, .function = function_id, .type = .dynamic, .name_hint = "adjusted", .origin = .{ .instruction_result = .{ .instruction = adjust_id, .index = 0 } } },
        .{ .id = first_result, .function = function_id, .type = .{ .kind = .table }, .name_hint = "first", .origin = .{ .instruction_result = .{ .instruction = first_call_id, .index = 0 } } },
        .{ .id = second_result, .function = function_id, .type = .{ .kind = .table }, .name_hint = "second", .origin = .{ .instruction_result = .{ .instruction = second_call_id, .index = 0 } } },
        .{ .id = literal_result, .function = function_id, .type = .{ .kind = .table }, .name_hint = "literal", .origin = .{ .instruction_result = .{ .instruction = literal_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = producer_id,
            .block = producer_block,
            .operation = .{ .call = .{ .callee = producer, .arguments = &.{}, .result_arity = .{ .variadic = {} } } },
            .results = &.{},
            .pack_result = pack_id,
            .effects = .dynamic_call,
            .evidence = &evidence_ids,
        },
        .{
            .id = effect_id,
            .block = consumer_block,
            .operation = .{ .environment_set = .{ .target = .{ .ambient = {} }, .name = "after_producer", .value = target } },
            .results = &.{},
            .effects = .semantic_environment_write,
            .evidence = &evidence_ids,
        },
        .{
            .id = adjust_id,
            .block = consumer_block,
            .operation = .{ .adjust_pack = pack_id },
            .results = &.{adjusted_result},
            .effects = .pure,
            .evidence = &evidence_ids,
        },
        .{
            .id = first_call_id,
            .block = consumer_block,
            .operation = .{ .call = .{ .callee = consumer, .arguments = &.{}, .argument_pack = pack_id, .result_arity = .{ .fixed = 1 } } },
            .results = &.{first_result},
            .effects = .dynamic_call,
            .evidence = &evidence_ids,
        },
        .{
            .id = second_call_id,
            .block = consumer_block,
            .operation = .{ .call = .{ .callee = consumer, .arguments = &.{first_result}, .argument_pack = pack_id, .result_arity = .{ .fixed = 1 } } },
            .results = &.{second_result},
            .effects = .dynamic_call,
            .evidence = &evidence_ids,
        },
        .{
            .id = literal_id,
            .block = consumer_block,
            .operation = .{ .make_table_literal = .{ .fields = &.{.{ .list = second_result }}, .tail_pack = pack_id } },
            .results = &.{literal_result},
            .effects = .table_constructor,
            .evidence = &evidence_ids,
        },
        .{
            .id = write_id,
            .block = consumer_block,
            .operation = .{ .table_set_pack = .{ .table = target, .first_index = 2, .pack = pack_id } },
            .results = &.{},
            .effects = .raw_table_write,
            .evidence = &evidence_ids,
        },
    };
    const producer_instructions = [_]ir.InstructionId{producer_id};
    const consumer_instructions = [_]ir.InstructionId{ effect_id, adjust_id, first_call_id, second_call_id, literal_id, write_id };
    var blocks = [_]ir.Block{
        .{ .id = producer_block, .function = function_id, .instructions = &producer_instructions, .terminator = .{ .jump = .{ .target = consumer_block } }, .evidence = &evidence_ids },
        .{ .id = consumer_block, .function = function_id, .instructions = &consumer_instructions, .terminator = .{ .return_expanded = .{ .values = &.{ adjusted_result, first_result, second_result, literal_result }, .pack = pack_id } }, .evidence = &evidence_ids },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ producer, consumer, target },
        .blocks = &.{ producer_block, consumer_block },
        .entry_block = producer_block,
        .evidence = &evidence_ids,
    }};
    const packs = [_]ir.ValuePack{.{ .id = pack_id, .function = function_id, .origin = .{ .instruction_result = producer_id }, .evidence = &evidence_ids }};
    const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .conformance_oracle, .locator = "fixture:multiple-stored-tails" }};
    var program: ir.Program = .{
        .program_id = "multiple-stored-tails",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
        .evidence = &evidence,
    };

    var plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer plan.deinit();
    try std.testing.expect(plan.role(producer_id) == .stored_invocation_producer);
    try std.testing.expect(plan.role(producer_id).stored_invocation_producer == null);
    try std.testing.expectEqual(pack_plan.InstructionRole{ .stored_adjustment = producer_id }, plan.role(adjust_id));
    for ([_]ir.InstructionId{ first_call_id, second_call_id, literal_id, write_id }) |consumer_id| {
        try std.testing.expect(plan.storedPackServesInstruction(producer_id, consumer_id));
        try std.testing.expect(plan.role(consumer_id) == .ordinary);
    }
    try std.testing.expect(!plan.storedPackServesInstruction(producer_id, effect_id));
    try std.testing.expectEqual(pack_plan.TerminatorRole{ .stored_pack_return = producer_id }, plan.terminatorRole(consumer_block));

    var core_report = try validation.validate(std.testing.allocator, &program, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expect(readable_report.isClean());

    const source = try emit_luau.emitStandardLuauAlloc(std.testing.allocator, &program);
    defer std.testing.allocator.free(source);
    const producer_offset = std.mem.indexOf(u8, source, "end)(produce())") orelse return error.TestUnexpectedResult;
    const effect_offset = std.mem.indexOf(u8, source, "after_producer = target") orelse return error.TestUnexpectedResult;
    const adjustment_offset = std.mem.indexOf(u8, source, "local adjusted = __lifter_rawget(") orelse return error.TestUnexpectedResult;
    const consumer_offset = std.mem.indexOf(u8, source, "consume(__lifter_table_unpack(") orelse return error.TestUnexpectedResult;
    try std.testing.expect(producer_offset < effect_offset);
    try std.testing.expect(effect_offset < adjustment_offset);
    try std.testing.expect(adjustment_offset < consumer_offset);
    try std.testing.expectEqual(@as(usize, 1), std.mem.count(u8, source, "produce()"));
    try std.testing.expectEqual(@as(usize, 5), std.mem.count(u8, source, "__lifter_table_unpack("));

    blocks[consumer_block.index()].terminator = .{ .jump = .{ .target = consumer_block } };
    var reentry_plan = try pack_plan.Plan.init(std.testing.allocator, &program);
    defer reentry_plan.deinit();
    try std.testing.expect(reentry_plan.role(producer_id) == .ordinary);
    var reentry_report = try validation.validate(std.testing.allocator, &program, .readable_luau);
    defer reentry_report.deinit();
    try std.testing.expect(reentry_report.contains(.unsupported_readable_pack_operation));
}

fn storedTailInvocationTemporaryPressureReport(argument_count: usize) !diagnostics.Report {
    const allocator = std.testing.allocator;
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const producer_id = ir.InstructionId.fromIndex(argument_count);
    const gap_id = ir.InstructionId.fromIndex(argument_count + 1);
    const consumer_id = ir.InstructionId.fromIndex(argument_count + 2);
    const callee = ir.ValueId.fromIndex(0);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const proof = ir.EvidenceId.fromIndex(0);
    const values = try allocator.alloc(ir.Value, argument_count + 1);
    defer allocator.free(values);
    const arguments = try allocator.alloc(ir.ValueId, argument_count);
    defer allocator.free(arguments);
    const result_ids = try allocator.alloc([1]ir.ValueId, argument_count);
    defer allocator.free(result_ids);
    const instructions = try allocator.alloc(ir.Instruction, argument_count + 3);
    defer allocator.free(instructions);
    const instruction_ids = try allocator.alloc(ir.InstructionId, argument_count + 3);
    defer allocator.free(instruction_ids);

    values[0] = .{
        .id = callee,
        .function = function_id,
        .type = .function,
        .name_hint = "callee",
        .origin = .{ .parameter = 0 },
    };
    for (0..argument_count) |index| {
        const instruction_id = ir.InstructionId.fromIndex(index);
        const value_id = ir.ValueId.fromIndex(index + 1);
        arguments[index] = value_id;
        result_ids[index] = .{value_id};
        instruction_ids[index] = instruction_id;
        values[index + 1] = .{
            .id = value_id,
            .function = function_id,
            .type = .{ .kind = .nil_value },
            .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } },
        };
        instructions[index] = .{
            .id = instruction_id,
            .block = block_id,
            .operation = .{ .constant = .{ .nil_value = {} } },
            .results = &result_ids[index],
            .effects = .pure,
            .evidence = &.{proof},
        };
    }
    instruction_ids[argument_count] = producer_id;
    instruction_ids[argument_count + 1] = gap_id;
    instruction_ids[argument_count + 2] = consumer_id;
    instructions[argument_count] = .{
        .id = producer_id,
        .block = block_id,
        .operation = .{ .call = .{
            .callee = callee,
            .arguments = &.{},
            .result_arity = .{ .variadic = {} },
        } },
        .results = &.{},
        .pack_result = pack_id,
        .effects = .dynamic_call,
        .evidence = &.{proof},
    };
    instructions[argument_count + 1] = .{
        .id = gap_id,
        .block = block_id,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "after_producer",
            .value = callee,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
        .evidence = &.{proof},
    };
    instructions[argument_count + 2] = .{
        .id = consumer_id,
        .block = block_id,
        .operation = .{ .call = .{
            .callee = callee,
            .arguments = arguments,
            .argument_pack = pack_id,
            .result_arity = .{ .fixed = 0 },
        } },
        .results = &.{},
        .effects = .dynamic_call,
        .evidence = &.{proof},
    };
    const packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = function_id,
        .origin = .{ .instruction_result = producer_id },
        .evidence = &.{proof},
    }};
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = instruction_ids,
        .terminator = .{ .return_values = &.{} },
        .evidence = &.{proof},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{callee},
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{proof},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .conformance_oracle,
        .locator = "fixture:stored-tail-register-pressure",
    }};
    const program: ir.Program = .{
        .program_id = "stored-tail-register-pressure",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = instructions,
        .values = values,
        .value_packs = &packs,
        .evidence = &evidence,
    };
    var scope = try readable_scope.Scope.init(allocator, &program);
    defer scope.deinit();
    var report = diagnostics.Report.init(allocator);
    errdefer report.deinit();
    try register_validation.validate(allocator, &report, &program, &scope, .standard_luau);
    return report;
}

test "stored invocation tails budget exact carrier expansion temporaries" {
    var boundary = try storedTailInvocationTemporaryPressureReport(241);
    defer boundary.deinit();
    try std.testing.expect(boundary.isClean());

    var excessive = try storedTailInvocationTemporaryPressureReport(242);
    defer excessive.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_temporary_register_pressure));
}
