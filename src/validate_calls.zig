const std = @import("std");
const ir = @import("ir.zig");
const diagnostics = @import("diagnostics.zig");
const type_validation = @import("validate_types.zig");
const readable_scope = @import("readable_scope.zig");

pub fn validate(allocator: std.mem.Allocator, report: *diagnostics.Report, program: *const ir.Program) !void {
    var scope = try readable_scope.Scope.init(allocator, program);
    defer scope.deinit();

    for (program.instructions) |instruction| {
        switch (instruction.operation) {
            .call => |call| {
                const target_id = knownFunction(program, call.callee, 0) orelse continue;
                if (!validId(target_id, program.functions.len)) continue;
                const target = program.functions[target_id.index()];
                try validateArguments(report, program, instruction.id, call.arguments, call.argument_pack, target);
                switch (call.result_arity) {
                    .fixed => try validateFixedResults(report, program, &scope, instruction, target),
                    .variadic => try validatePackResult(report, program, &scope, instruction, target),
                }
            },
            .protected_call => |call| {
                const target_id = knownFunction(program, call.callee, 0) orelse continue;
                if (!validId(target_id, program.functions.len)) continue;
                try validateArguments(
                    report,
                    program,
                    instruction.id,
                    call.arguments,
                    call.argument_pack,
                    program.functions[target_id.index()],
                );
            },
            else => {},
        }
    }
}

fn validateArguments(
    report: *diagnostics.Report,
    program: *const ir.Program,
    instruction_id: ir.InstructionId,
    arguments: []const ir.ValueId,
    argument_pack: ?ir.ValuePackId,
    target: ir.Function,
) !void {
    for (target.parameters, 0..) |parameter_id, index| {
        if (!validId(parameter_id, program.values.len)) continue;
        const source_type = argumentType(program, arguments, argument_pack, index) orelse continue;
        if (!typesCompatible(program.values[parameter_id.index()].type, source_type)) {
            try report.add(.call_argument_type_mismatch, instruction_id.index());
            return;
        }
    }
}

fn validateFixedResults(
    report: *diagnostics.Report,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    instruction: ir.Instruction,
    target: ir.Function,
) !void {
    for (instruction.results, 0..) |result_id, index| {
        if (!validId(result_id, program.values.len)) continue;
        for (target.blocks) |block_id| {
            if (!validId(block_id, program.blocks.len) or !scope.block(block_id)) continue;
            const source_type = fixedResultType(program, program.blocks[block_id.index()].terminator, index) orelse continue;
            if (!typesCompatible(program.values[result_id.index()].type, source_type)) {
                try report.add(.call_result_type_mismatch, instruction.id.index());
                return;
            }
        }
    }
}

fn validatePackResult(
    report: *diagnostics.Report,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    instruction: ir.Instruction,
    target: ir.Function,
) !void {
    const pack_id = instruction.pack_result orelse return;
    if (!validId(pack_id, program.value_packs.len)) return;
    const declared = program.value_packs[pack_id.index()].shape;
    for (target.blocks) |block_id| {
        if (!validId(block_id, program.blocks.len) or !scope.block(block_id)) continue;
        const terminator = program.blocks[block_id.index()].terminator;
        if (!isReturn(terminator)) continue;
        if (!shapeAcceptsReturn(program, declared, terminator)) {
            try report.add(.call_pack_shape_mismatch, instruction.id.index());
            return;
        }
    }
}

fn argumentType(program: *const ir.Program, arguments: []const ir.ValueId, argument_pack: ?ir.ValuePackId, index: usize) ?ir.ValueType {
    if (index < arguments.len) {
        const value_id = arguments[index];
        if (!validId(value_id, program.values.len)) return null;
        return program.values[value_id.index()].type;
    }
    const pack_id = argument_pack orelse return .{ .kind = .nil_value };
    return adjustedPackType(program, pack_id, index - arguments.len);
}

fn fixedResultType(program: *const ir.Program, terminator: ir.Terminator, index: usize) ?ir.ValueType {
    return switch (terminator) {
        .return_values => |values| if (index < values.len)
            valueType(program, values[index])
        else
            .{ .kind = .nil_value },
        .return_pack => |pack_id| adjustedPackType(program, pack_id, index),
        .return_expanded => |expanded| if (index < expanded.values.len)
            valueType(program, expanded.values[index])
        else
            adjustedPackType(program, expanded.pack, index - expanded.values.len),
        .jump, .branch, .throw_error, .unreachable_block => null,
    };
}

fn adjustedPackType(program: *const ir.Program, pack_id: ir.ValuePackId, index: usize) ?ir.ValueType {
    if (!validId(pack_id, program.value_packs.len)) return null;
    const shape = program.value_packs[pack_id.index()].shape;
    if (index < shape.prefix.len) return shape.prefix[index];
    return if (shape.tail == .open) .dynamic else .{ .kind = .nil_value };
}

fn shapeAcceptsReturn(program: *const ir.Program, declared: ir.PackShape, terminator: ir.Terminator) bool {
    for (declared.prefix, 0..) |target_type, index| {
        const source_type = variadicResultType(program, terminator, index) orelse return false;
        if (!typesCompatible(target_type, source_type)) return false;
    }
    if (declared.tail == .open) return true;
    const exact_length = exactReturnLength(program, terminator) orelse return true;
    return exact_length == declared.prefix.len;
}

fn variadicResultType(program: *const ir.Program, terminator: ir.Terminator, index: usize) ?ir.ValueType {
    return switch (terminator) {
        .return_values => |values| if (index < values.len) valueType(program, values[index]) else null,
        .return_pack => |pack_id| variadicPackType(program, pack_id, index),
        .return_expanded => |expanded| if (index < expanded.values.len)
            valueType(program, expanded.values[index])
        else
            variadicPackType(program, expanded.pack, index - expanded.values.len),
        .jump, .branch, .throw_error, .unreachable_block => null,
    };
}

fn variadicPackType(program: *const ir.Program, pack_id: ir.ValuePackId, index: usize) ?ir.ValueType {
    if (!validId(pack_id, program.value_packs.len)) return null;
    const shape = program.value_packs[pack_id.index()].shape;
    if (index < shape.prefix.len) return shape.prefix[index];
    return if (shape.tail == .open) .dynamic else null;
}

fn exactReturnLength(program: *const ir.Program, terminator: ir.Terminator) ?usize {
    return switch (terminator) {
        .return_values => |values| values.len,
        .return_pack => |pack_id| exactPackLength(program, pack_id),
        .return_expanded => |expanded| if (exactPackLength(program, expanded.pack)) |pack_length|
            std.math.add(usize, expanded.values.len, pack_length) catch null
        else
            null,
        .jump, .branch, .throw_error, .unreachable_block => null,
    };
}

fn exactPackLength(program: *const ir.Program, pack_id: ir.ValuePackId) ?usize {
    if (!validId(pack_id, program.value_packs.len)) return null;
    const shape = program.value_packs[pack_id.index()].shape;
    return if (shape.tail == .closed) shape.prefix.len else null;
}

fn knownFunction(program: *const ir.Program, value_id: ir.ValueId, depth: usize) ?ir.FunctionId {
    if (!validId(value_id, program.values.len) or depth > program.values.len) return null;
    const origin = switch (program.values[value_id.index()].origin) {
        .instruction_result => |value| value,
        else => return null,
    };
    if (origin.index != 0 or !validId(origin.instruction, program.instructions.len)) return null;
    return switch (program.instructions[origin.instruction.index()].operation) {
        .function_ref => |function_id| function_id,
        .make_closure => |closure| closure.function,
        .copy => |source| knownFunction(program, source, depth + 1),
        else => null,
    };
}

fn isReturn(terminator: ir.Terminator) bool {
    return switch (terminator) {
        .return_values, .return_pack, .return_expanded => true,
        .jump, .branch, .throw_error, .unreachable_block => false,
    };
}

fn valueType(program: *const ir.Program, value_id: ir.ValueId) ?ir.ValueType {
    if (!validId(value_id, program.values.len)) return null;
    return program.values[value_id.index()].type;
}

fn typesCompatible(target: ir.ValueType, source: ir.ValueType) bool {
    return source.kind == .dynamic or type_validation.isAssignable(target, source);
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}

test "known calls reject only definite argument and fixed-result contradictions" {
    const f_caller = ir.FunctionId.fromIndex(0);
    const f_target = ir.FunctionId.fromIndex(1);
    const b_caller = ir.BlockId.fromIndex(0);
    const b_target = ir.BlockId.fromIndex(1);
    const i_reference = ir.InstructionId.fromIndex(0);
    const i_argument = ir.InstructionId.fromIndex(1);
    const i_call = ir.InstructionId.fromIndex(2);
    const v_reference = ir.ValueId.fromIndex(0);
    const v_argument = ir.ValueId.fromIndex(1);
    const v_result = ir.ValueId.fromIndex(2);
    const v_parameter = ir.ValueId.fromIndex(3);

    var values = [_]ir.Value{
        .{ .id = v_reference, .function = f_caller, .type = .function, .origin = .{ .instruction_result = .{ .instruction = i_reference, .index = 0 } } },
        .{ .id = v_argument, .function = f_caller, .type = .string, .origin = .{ .instruction_result = .{ .instruction = i_argument, .index = 0 } } },
        .{ .id = v_result, .function = f_caller, .type = .integer, .origin = .{ .instruction_result = .{ .instruction = i_call, .index = 0 } } },
        .{ .id = v_parameter, .function = f_target, .type = .integer, .origin = .{ .parameter = 0 } },
    };
    var instructions = [_]ir.Instruction{
        .{ .id = i_reference, .block = b_caller, .operation = .{ .function_ref = f_target }, .results = &.{v_reference}, .effects = .pure },
        .{ .id = i_argument, .block = b_caller, .operation = .{ .constant = .{ .string = "bad" } }, .results = &.{v_argument}, .effects = .pure },
        .{ .id = i_call, .block = b_caller, .operation = .{ .call = .{
            .callee = v_reference,
            .arguments = &.{v_argument},
            .result_arity = .{ .fixed = 1 },
        } }, .results = &.{v_result}, .effects = .dynamic_call },
    };
    const blocks = [_]ir.Block{
        .{ .id = b_caller, .function = f_caller, .instructions = &.{ i_reference, i_argument, i_call }, .terminator = .{ .return_values = &.{v_result} } },
        .{ .id = b_target, .function = f_target, .terminator = .{ .return_values = &.{v_parameter} } },
    };
    const functions = [_]ir.Function{
        .{ .id = f_caller, .blocks = &.{b_caller}, .entry_block = b_caller },
        .{ .id = f_target, .parameters = &.{v_parameter}, .blocks = &.{b_target}, .entry_block = b_target },
    };
    var program: ir.Program = .{
        .program_id = "known-call-types",
        .entry_function = f_caller,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
    };

    var argument_report = diagnostics.Report.init(std.testing.allocator);
    defer argument_report.deinit();
    try validate(std.testing.allocator, &argument_report, &program);
    try std.testing.expect(argument_report.contains(.call_argument_type_mismatch));
    try std.testing.expect(!argument_report.contains(.call_result_type_mismatch));

    values[v_argument.index()].type = .integer;
    values[v_result.index()].type = .string;
    var result_report = diagnostics.Report.init(std.testing.allocator);
    defer result_report.deinit();
    try validate(std.testing.allocator, &result_report, &program);
    try std.testing.expect(!result_report.contains(.call_argument_type_mismatch));
    try std.testing.expect(result_report.contains(.call_result_type_mismatch));

    values[v_result.index()].type = .integer;
    instructions[i_call.index()].operation.call.arguments = &.{};
    var missing_report = diagnostics.Report.init(std.testing.allocator);
    defer missing_report.deinit();
    try validate(std.testing.allocator, &missing_report, &program);
    try std.testing.expect(missing_report.contains(.call_argument_type_mismatch));

    values[v_argument.index()].type = .dynamic;
    instructions[i_call.index()].operation.call.arguments = &.{v_argument};
    var unknown_report = diagnostics.Report.init(std.testing.allocator);
    defer unknown_report.deinit();
    try validate(std.testing.allocator, &unknown_report, &program);
    try std.testing.expect(unknown_report.isClean());

    values[v_argument.index()].type = .string;
    instructions[i_call.index()].operation = .{ .protected_call = .{
        .callee = v_reference,
        .arguments = &.{v_argument},
        .result_arity = .{ .fixed = 1 },
    } };
    var protected_report = diagnostics.Report.init(std.testing.allocator);
    defer protected_report.deinit();
    try validate(std.testing.allocator, &protected_report, &program);
    try std.testing.expect(protected_report.contains(.call_argument_type_mismatch));
}

test "known variadic calls validate definite result-pack shape facts" {
    const f_caller = ir.FunctionId.fromIndex(0);
    const f_target = ir.FunctionId.fromIndex(1);
    const b_caller = ir.BlockId.fromIndex(0);
    const b_target = ir.BlockId.fromIndex(1);
    const i_reference = ir.InstructionId.fromIndex(0);
    const i_call = ir.InstructionId.fromIndex(1);
    const v_reference = ir.ValueId.fromIndex(0);
    const v_argument = ir.ValueId.fromIndex(1);
    const v_returned = ir.ValueId.fromIndex(2);
    const p_results = ir.ValuePackId.fromIndex(0);
    const integer_prefix = [_]ir.ValueType{.integer};
    const string_prefix = [_]ir.ValueType{.string};

    const values = [_]ir.Value{
        .{ .id = v_reference, .function = f_caller, .type = .function, .origin = .{ .instruction_result = .{ .instruction = i_reference, .index = 0 } } },
        .{ .id = v_argument, .function = f_caller, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = v_returned, .function = f_target, .type = .integer, .origin = .{ .parameter = 0 } },
    };
    var packs = [_]ir.ValuePack{.{
        .id = p_results,
        .function = f_caller,
        .origin = .{ .instruction_result = i_call },
        .shape = .{ .prefix = &string_prefix, .tail = .closed },
    }};
    const instructions = [_]ir.Instruction{
        .{ .id = i_reference, .block = b_caller, .operation = .{ .function_ref = f_target }, .results = &.{v_reference}, .effects = .pure },
        .{ .id = i_call, .block = b_caller, .operation = .{ .call = .{
            .callee = v_reference,
            .arguments = &.{v_argument},
            .result_arity = .{ .variadic = {} },
        } }, .results = &.{}, .pack_result = p_results, .effects = .dynamic_call },
    };
    const blocks = [_]ir.Block{
        .{ .id = b_caller, .function = f_caller, .instructions = &.{ i_reference, i_call }, .terminator = .{ .return_pack = p_results } },
        .{ .id = b_target, .function = f_target, .terminator = .{ .return_values = &.{v_returned} } },
    };
    const functions = [_]ir.Function{
        .{ .id = f_caller, .parameters = &.{v_argument}, .blocks = &.{b_caller}, .entry_block = b_caller },
        .{ .id = f_target, .parameters = &.{v_returned}, .blocks = &.{b_target}, .entry_block = b_target },
    };
    var program: ir.Program = .{
        .program_id = "known-call-pack-shape",
        .entry_function = f_caller,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
    };

    var type_report = diagnostics.Report.init(std.testing.allocator);
    defer type_report.deinit();
    try validate(std.testing.allocator, &type_report, &program);
    try std.testing.expect(type_report.contains(.call_pack_shape_mismatch));

    packs[0].shape = .{ .prefix = &integer_prefix, .tail = .closed };
    var valid_report = diagnostics.Report.init(std.testing.allocator);
    defer valid_report.deinit();
    try validate(std.testing.allocator, &valid_report, &program);
    try std.testing.expect(valid_report.isClean());

    packs[0].shape = .{ .prefix = &.{}, .tail = .closed };
    var arity_report = diagnostics.Report.init(std.testing.allocator);
    defer arity_report.deinit();
    try validate(std.testing.allocator, &arity_report, &program);
    try std.testing.expect(arity_report.contains(.call_pack_shape_mismatch));
}
