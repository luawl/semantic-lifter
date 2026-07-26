const std = @import("std");
const diagnostics = @import("diagnostics.zig");
const emission_planning = @import("emit_luau_plan.zig");
const fixtures = @import("fixtures.zig");
const ir = @import("ir.zig");
const luau_runtime = @import("luau_runtime.zig");
const readable_scope = @import("readable_scope.zig");

pub fn validate(
    report: *diagnostics.Report,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    emitted_functions: []const bool,
) std.mem.Allocator.Error!void {
    return validateWithLimit(
        report,
        program,
        readable,
        emission,
        emitted_functions,
        luau_runtime.max_child_prototypes,
    );
}

fn validateWithLimit(
    report: *diagnostics.Report,
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    emitted_functions: []const bool,
    limit: usize,
) std.mem.Allocator.Error!void {
    for (program.functions) |function| {
        if (function.id.index() >= emitted_functions.len or !emitted_functions[function.id.index()]) continue;
        if (exceedsChildPrototypeLimit(childPrototypeCount(program, readable, emission, function), limit)) {
            try report.add(.unsupported_readable_child_prototype_count, function.id.index());
        }
    }
}

fn childPrototypeCount(
    program: *const ir.Program,
    readable: *const readable_scope.Scope,
    emission: *const emission_planning.Plan,
    function: ir.Function,
) usize {
    var count = if (function.id == program.entry_function) topLevelFunctionCount(program) else 0;
    for (function.blocks) |block_id| {
        if (!readable.block(block_id) or block_id.index() >= program.blocks.len) continue;
        for (program.blocks[block_id.index()].instructions) |instruction_id| {
            if (!readable.instruction(instruction_id) or instruction_id.index() >= program.instructions.len) continue;
            if (!instructionSurvives(emission, instruction_id)) continue;
            const operation = program.instructions[instruction_id.index()].operation;
            if (operation == .make_closure or
                operation == .table_set_pack or
                emission.packs.role(instruction_id) == .stored_invocation_producer)
            {
                count = std.math.add(usize, count, 1) catch return std.math.maxInt(usize);
            }
        }
    }
    return count;
}

fn topLevelFunctionCount(program: *const ir.Program) usize {
    var count: usize = 0;
    for (program.functions) |function| {
        if (function.id != program.entry_function and function.lexical_parent == null) {
            count = std.math.add(usize, count, 1) catch return std.math.maxInt(usize);
        }
    }
    return count;
}

fn instructionSurvives(emission: *const emission_planning.Plan, instruction_id: ir.InstructionId) bool {
    return !emission.dead.contains(instruction_id) or emission.dead.isInlined(instruction_id);
}

fn exceedsChildPrototypeLimit(count: usize, limit: usize) bool {
    return count > limit;
}

test "child prototype limit accepts 32768 and rejects 32769" {
    try std.testing.expect(!exceedsChildPrototypeLimit(
        luau_runtime.max_child_prototypes,
        luau_runtime.max_child_prototypes,
    ));
    try std.testing.expect(exceedsChildPrototypeLimit(
        luau_runtime.max_child_prototypes + 1,
        luau_runtime.max_child_prototypes,
    ));
}

test "table pack writer contributes its emitted child prototype" {
    const fixture = fixtures.ordered_table_vararg_module;
    var readable = try readable_scope.Scope.init(std.testing.allocator, &fixture.program);
    defer readable.deinit();
    var emission = try emission_planning.Plan.init(std.testing.allocator, &fixture.program, .standard_luau);
    defer emission.deinit();

    try std.testing.expectEqual(
        @as(usize, 1),
        childPrototypeCount(&fixture.program, &readable, &emission, fixture.functions[fixture.f_entry.index()]),
    );
}

test "prototype planning counts roots and live closures but not references or dead closures" {
    const entry = ir.FunctionId.fromIndex(0);
    const root_a = ir.FunctionId.fromIndex(1);
    const root_b = ir.FunctionId.fromIndex(2);
    const child = ir.FunctionId.fromIndex(3);
    const entry_block = ir.BlockId.fromIndex(0);
    const root_a_block = ir.BlockId.fromIndex(1);
    const root_b_block = ir.BlockId.fromIndex(2);
    const child_block = ir.BlockId.fromIndex(3);
    const reference_id = ir.InstructionId.fromIndex(0);
    const live_closure_id = ir.InstructionId.fromIndex(1);
    const dead_closure_id = ir.InstructionId.fromIndex(2);
    const reference = ir.ValueId.fromIndex(0);
    const live_closure = ir.ValueId.fromIndex(1);
    const dead_closure = ir.ValueId.fromIndex(2);

    const values = [_]ir.Value{
        .{ .id = reference, .function = entry, .type = .function, .origin = .{ .instruction_result = .{ .instruction = reference_id, .index = 0 } } },
        .{ .id = live_closure, .function = entry, .type = .function, .origin = .{ .instruction_result = .{ .instruction = live_closure_id, .index = 0 } } },
        .{ .id = dead_closure, .function = entry, .type = .function, .origin = .{ .instruction_result = .{ .instruction = dead_closure_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = reference_id, .block = entry_block, .operation = .{ .function_ref = root_a }, .results = &.{reference}, .effects = .pure },
        .{ .id = live_closure_id, .block = entry_block, .operation = .{ .make_closure = .{ .function = child, .bindings = &.{} } }, .results = &.{live_closure}, .effects = .pure },
        .{ .id = dead_closure_id, .block = entry_block, .operation = .{ .make_closure = .{ .function = child, .bindings = &.{} } }, .results = &.{dead_closure}, .effects = .pure },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry_block, .function = entry, .instructions = &.{ reference_id, live_closure_id, dead_closure_id }, .terminator = .{ .return_values = &.{ reference, live_closure } } },
        .{ .id = root_a_block, .function = root_a, .terminator = .{ .return_values = &.{} } },
        .{ .id = root_b_block, .function = root_b, .terminator = .{ .return_values = &.{} } },
        .{ .id = child_block, .function = child, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{
        .{ .id = entry, .blocks = &.{entry_block}, .entry_block = entry_block },
        .{ .id = root_a, .blocks = &.{root_a_block}, .entry_block = root_a_block },
        .{ .id = root_b, .blocks = &.{root_b_block}, .entry_block = root_b_block },
        .{ .id = child, .lexical_parent = entry, .blocks = &.{child_block}, .entry_block = child_block },
    };
    const program: ir.Program = .{
        .program_id = "child-prototype-planning",
        .entry_function = entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var readable = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer readable.deinit();
    var emission = try emission_planning.Plan.init(std.testing.allocator, &program, .standard_luau);
    defer emission.deinit();
    try std.testing.expectEqual(@as(usize, 3), childPrototypeCount(&program, &readable, &emission, functions[entry.index()]));

    const emitted = [_]bool{ true, true, true, true };
    var boundary = diagnostics.Report.init(std.testing.allocator);
    defer boundary.deinit();
    try validateWithLimit(&boundary, &program, &readable, &emission, &emitted, 3);
    try std.testing.expect(boundary.isClean());

    var excessive = diagnostics.Report.init(std.testing.allocator);
    defer excessive.deinit();
    try validateWithLimit(&excessive, &program, &readable, &emission, &emitted, 2);
    try std.testing.expectEqual(@as(usize, 1), excessive.diagnostics.items.len);
    try std.testing.expect(excessive.contains(.unsupported_readable_child_prototype_count));
}

test "closure-store fusion still contributes a child prototype" {
    const entry = ir.FunctionId.fromIndex(0);
    const child = ir.FunctionId.fromIndex(1);
    const entry_block = ir.BlockId.fromIndex(0);
    const child_block = ir.BlockId.fromIndex(1);
    const closure_id = ir.InstructionId.fromIndex(0);
    const store_id = ir.InstructionId.fromIndex(1);
    const table_value = ir.ValueId.fromIndex(0);
    const key_value = ir.ValueId.fromIndex(1);
    const closure_value = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = table_value, .function = entry, .type = .{ .kind = .table }, .origin = .{ .parameter = 0 } },
        .{ .id = key_value, .function = entry, .type = .string, .origin = .{ .parameter = 1 } },
        .{ .id = closure_value, .function = entry, .type = .function, .origin = .{ .instruction_result = .{ .instruction = closure_id, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = closure_id, .block = entry_block, .operation = .{ .make_closure = .{ .function = child, .bindings = &.{} } }, .results = &.{closure_value}, .effects = .pure },
        .{ .id = store_id, .block = entry_block, .operation = .{ .table_set = .{ .table = table_value, .key = key_value, .value = closure_value } }, .results = &.{}, .effects = .semantic_table_write },
    };
    const blocks = [_]ir.Block{
        .{ .id = entry_block, .function = entry, .instructions = &.{ closure_id, store_id }, .terminator = .{ .return_values = &.{} } },
        .{ .id = child_block, .function = child, .terminator = .{ .return_values = &.{} } },
    };
    const functions = [_]ir.Function{
        .{ .id = entry, .parameters = &.{ table_value, key_value }, .blocks = &.{entry_block}, .entry_block = entry_block },
        .{ .id = child, .lexical_parent = entry, .blocks = &.{child_block}, .entry_block = child_block },
    };
    const program: ir.Program = .{
        .program_id = "fused-child-prototype-planning",
        .entry_function = entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };
    var readable = try readable_scope.Scope.init(std.testing.allocator, &program);
    defer readable.deinit();
    var emission = try emission_planning.Plan.init(std.testing.allocator, &program, .standard_luau);
    defer emission.deinit();
    try std.testing.expectEqual(store_id, emission.closure_stores.consumerForProducer(closure_id).?);
    try std.testing.expectEqual(@as(usize, 1), childPrototypeCount(&program, &readable, &emission, functions[entry.index()]));
}
