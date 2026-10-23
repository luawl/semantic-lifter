const std = @import("std");
const cfg = @import("cfg.zig");
const diagnostics = @import("diagnostics.zig");
const ir = @import("ir.zig");
const luau_runtime = @import("luau_runtime.zig");
const syntax_depth = @import("validate_luau_syntax_depth.zig");
const validation = @import("validate.zig");

fn nestedBranchProgram(allocator: std.mem.Allocator, depth: usize) !ir.Program {
    const proof = ir.EvidenceId.fromIndex(0);
    const evidence_ids = try allocator.dupe(ir.EvidenceId, &.{proof});
    const function_id = ir.FunctionId.fromIndex(0);
    const block_count = depth * 2 + 1;
    const value_count = depth + 3;
    const function_blocks = try allocator.alloc(ir.BlockId, block_count);
    const instruction_ids = try allocator.alloc(ir.InstructionId, depth);
    const value_ids = try allocator.alloc(ir.ValueId, value_count);
    const blocks = try allocator.alloc(ir.Block, block_count);
    const instructions = try allocator.alloc(ir.Instruction, depth);
    const values = try allocator.alloc(ir.Value, value_count);

    for (function_blocks, 0..) |*block_id, index| block_id.* = ir.BlockId.fromIndex(index);
    for (instruction_ids, 0..) |*instruction_id, index| instruction_id.* = ir.InstructionId.fromIndex(index);
    for (value_ids, 0..) |*value_id, index| value_id.* = ir.ValueId.fromIndex(index);
    values[0] = .{ .id = value_ids[0], .function = function_id, .type = .function, .origin = .{ .parameter = 0 } };
    values[1] = .{ .id = value_ids[1], .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } };
    values[2] = .{ .id = value_ids[2], .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } };

    for (0..depth) |index| {
        const branch_id = function_blocks[index];
        const failure_id = function_blocks[depth + index];
        const condition_id = value_ids[index + 3];
        values[index + 3] = .{
            .id = condition_id,
            .function = function_id,
            .type = .boolean,
            .origin = .{ .instruction_result = .{ .instruction = instruction_ids[index], .index = 0 } },
        };
        instructions[index] = .{
            .id = instruction_ids[index],
            .block = branch_id,
            .operation = .{ .call = .{
                .callee = value_ids[0],
                .arguments = &.{},
                .result_arity = .{ .fixed = 1 },
            } },
            .results = value_ids[index + 3 .. index + 4],
            .effects = .dynamic_call,
            .evidence = evidence_ids,
        };
        blocks[index] = .{
            .id = branch_id,
            .function = function_id,
            .instructions = instruction_ids[index .. index + 1],
            .terminator = .{ .branch = .{
                .condition = condition_id,
                .then_edge = .{ .target = if (index + 1 == depth) function_blocks[block_count - 1] else function_blocks[index + 1] },
                .else_edge = .{ .target = failure_id },
            } },
            .evidence = evidence_ids,
        };
        blocks[depth + index] = .{
            .id = failure_id,
            .function = function_id,
            .terminator = .{ .return_values = value_ids[2..3] },
            .evidence = evidence_ids,
        };
    }
    blocks[block_count - 1] = .{
        .id = function_blocks[block_count - 1],
        .function = function_id,
        .terminator = .{ .return_values = value_ids[1..2] },
        .evidence = evidence_ids,
    };

    const functions = try allocator.alloc(ir.Function, 1);
    functions[0] = .{
        .id = function_id,
        .parameters = value_ids[0..3],
        .blocks = function_blocks,
        .entry_block = function_blocks[0],
        .evidence = evidence_ids,
    };
    const evidence = try allocator.dupe(ir.Evidence, &.{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:nested-readable-syntax-depth",
    }});
    return .{
        .program_id = "nested-readable-syntax-depth",
        .entry_function = function_id,
        .functions = functions,
        .blocks = blocks,
        .instructions = instructions,
        .values = values,
        .evidence = evidence,
    };
}

fn nestedClosureProgram(allocator: std.mem.Allocator, closure_depth: usize) !ir.Program {
    const proof = ir.EvidenceId.fromIndex(0);
    const evidence_ids = try allocator.dupe(ir.EvidenceId, &.{proof});
    const function_count = closure_depth + 1;
    const function_ids = try allocator.alloc(ir.FunctionId, function_count);
    const block_ids = try allocator.alloc(ir.BlockId, function_count);
    const instruction_ids = try allocator.alloc(ir.InstructionId, closure_depth);
    const value_ids = try allocator.alloc(ir.ValueId, closure_depth);
    const functions = try allocator.alloc(ir.Function, function_count);
    const blocks = try allocator.alloc(ir.Block, function_count);
    const instructions = try allocator.alloc(ir.Instruction, closure_depth);
    const values = try allocator.alloc(ir.Value, closure_depth);
    for (function_ids, 0..) |*function_id, index| function_id.* = ir.FunctionId.fromIndex(index);
    for (block_ids, 0..) |*block_id, index| block_id.* = ir.BlockId.fromIndex(index);
    for (instruction_ids, 0..) |*instruction_id, index| instruction_id.* = ir.InstructionId.fromIndex(index);
    for (value_ids, 0..) |*value_id, index| value_id.* = ir.ValueId.fromIndex(index);

    for (0..function_count) |index| {
        functions[index] = .{
            .id = function_ids[index],
            .lexical_parent = if (index == 0) null else function_ids[index - 1],
            .blocks = block_ids[index .. index + 1],
            .entry_block = block_ids[index],
            .evidence = evidence_ids,
        };
        if (index == closure_depth) {
            blocks[index] = .{
                .id = block_ids[index],
                .function = function_ids[index],
                .terminator = .{ .return_values = &.{} },
                .evidence = evidence_ids,
            };
            continue;
        }
        values[index] = .{
            .id = value_ids[index],
            .function = function_ids[index],
            .type = .function,
            .origin = .{ .instruction_result = .{ .instruction = instruction_ids[index], .index = 0 } },
        };
        instructions[index] = .{
            .id = instruction_ids[index],
            .block = block_ids[index],
            .operation = .{ .make_closure = .{ .function = function_ids[index + 1], .bindings = &.{} } },
            .results = value_ids[index .. index + 1],
            .effects = .pure,
            .evidence = evidence_ids,
        };
        blocks[index] = .{
            .id = block_ids[index],
            .function = function_ids[index],
            .instructions = instruction_ids[index .. index + 1],
            .terminator = .{ .return_values = value_ids[index .. index + 1] },
            .evidence = evidence_ids,
        };
    }

    const evidence = try allocator.dupe(ir.Evidence, &.{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:nested-readable-closure-depth",
    }});
    return .{
        .program_id = "nested-readable-closure-depth",
        .entry_function = function_ids[0],
        .functions = functions,
        .blocks = blocks,
        .instructions = instructions,
        .values = values,
        .evidence = evidence,
    };
}

test "readable syntax admission accepts 512 nested branches and rejects 513" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const boundary = try nestedBranchProgram(arena.allocator(), luau_runtime.max_emitted_syntax_nesting);
    var boundary_report = try validation.validate(std.testing.allocator, &boundary, .readable_luau);
    defer boundary_report.deinit();
    try std.testing.expect(boundary_report.isClean());

    const excessive = try nestedBranchProgram(arena.allocator(), luau_runtime.max_emitted_syntax_nesting + 1);
    var core_report = try validation.validate(std.testing.allocator, &excessive, .core);
    defer core_report.deinit();
    try std.testing.expect(core_report.isClean());
    var readable_report = try validation.validate(std.testing.allocator, &excessive, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expectEqual(@as(usize, 1), readable_report.diagnostics.items.len);
    try std.testing.expect(readable_report.contains(.unsupported_readable_syntax_depth));
}

test "deep branch spine is rejected before recursive structuring" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const boundary = try nestedBranchProgram(arena.allocator(), luau_runtime.max_emitted_syntax_nesting);
    var boundary_analysis = try cfg.Analysis.init(std.testing.allocator, &boundary, boundary.functions[0]);
    defer boundary_analysis.deinit();
    try std.testing.expect(!try syntax_depth.exceedsPlanningDepth(
        std.testing.allocator,
        &boundary,
        &boundary_analysis,
    ));

    const excessive = try nestedBranchProgram(arena.allocator(), luau_runtime.max_emitted_syntax_nesting + 1);
    var excessive_analysis = try cfg.Analysis.init(std.testing.allocator, &excessive, excessive.functions[0]);
    defer excessive_analysis.deinit();
    try std.testing.expect(try syntax_depth.exceedsPlanningDepth(
        std.testing.allocator,
        &excessive,
        &excessive_analysis,
    ));
}

test "lexical closure bodies consume the same readable syntax budget" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const boundary = try nestedClosureProgram(arena.allocator(), luau_runtime.max_emitted_syntax_nesting);
    var boundary_report = try validation.validate(std.testing.allocator, &boundary, .readable_luau);
    defer boundary_report.deinit();
    try std.testing.expect(boundary_report.isClean());

    const excessive = try nestedClosureProgram(arena.allocator(), luau_runtime.max_emitted_syntax_nesting + 1);
    var readable_report = try validation.validate(std.testing.allocator, &excessive, .readable_luau);
    defer readable_report.deinit();
    try std.testing.expectEqual(@as(usize, 1), readable_report.diagnostics.items.len);
    try std.testing.expect(readable_report.contains(.unsupported_readable_syntax_depth));
}

/// An escape chain: worker(f, observe, marker, first, last, stride), function 1, returned by the chunk, runs
/// if f(1) then if f(2) then ... if f(depth) then observe(0) goto J1 end observe(depth) ... end observe(2) end
/// J1: observe(1), then returns marker when f(-1) holds and first otherwise. The escape from the innermost arm to J1
/// is a free target of the arms on the way, so the emitter writes each of them inside a transfer wrapper
/// (`repeat ... until true`), one statement level beside its `if`, although most of them own no escape.
/// Blocks: 0 the chunk, 1 the entry, A_k = 2k and J_k = 2k + 1, the escape arm 2 * depth + 2, then the two returns.
fn escapeChainProgram(allocator: std.mem.Allocator, depth: usize) !ir.Program {
    const proof = ir.EvidenceId.fromIndex(0);
    const evidence_ids = try allocator.dupe(ir.EvidenceId, &.{proof});
    const chunk = ir.FunctionId.fromIndex(0);
    const worker = ir.FunctionId.fromIndex(1);
    const block_count = 2 * depth + 5;
    const instruction_count = 3 * depth + 5;
    const value_count = 2 * depth + 10;
    const block_ids = try allocator.alloc(ir.BlockId, block_count);
    const instruction_ids = try allocator.alloc(ir.InstructionId, instruction_count);
    const value_ids = try allocator.alloc(ir.ValueId, value_count);
    const blocks = try allocator.alloc(ir.Block, block_count);
    const instructions = try allocator.alloc(ir.Instruction, instruction_count);
    const values = try allocator.alloc(ir.Value, value_count);
    for (block_ids, 0..) |*block_id, index| block_id.* = ir.BlockId.fromIndex(index);
    for (instruction_ids, 0..) |*instruction_id, index| instruction_id.* = ir.InstructionId.fromIndex(index);
    for (value_ids, 0..) |*value_id, index| value_id.* = ir.ValueId.fromIndex(index);

    // Values 0-5: the parameters f, observe, marker, first, last and stride.
    const parameter_types = [_]ir.ValueType{ .function, .function, .dynamic, .number, .number, .number };
    for (parameter_types, 0..) |value_type, index| {
        values[index] = .{ .id = value_ids[index], .function = worker, .type = value_type, .origin = .{ .parameter = @intCast(index) } };
    }
    // Instructions 0 .. depth + 1 in the entry block: the constants -1, 0, 1, ..., depth (the constant k is value 7 + k).
    for (0..depth + 2) |offset| {
        const literal: f64 = @floatFromInt(@as(i64, @intCast(offset)) - 1);
        values[6 + offset] = .{
            .id = value_ids[6 + offset],
            .function = worker,
            .type = .number,
            .origin = .{ .instruction_result = .{ .instruction = instruction_ids[offset], .index = 0 } },
        };
        instructions[offset] = .{
            .id = instruction_ids[offset],
            .block = block_ids[1],
            .operation = .{ .constant = .{ .number = literal } },
            .results = value_ids[6 + offset .. 7 + offset],
            .effects = .pure,
            .evidence = evidence_ids,
        };
    }
    blocks[1] = .{
        .id = block_ids[1],
        .function = worker,
        .instructions = instruction_ids[0 .. depth + 2],
        .terminator = .{ .jump = .{ .target = block_ids[2] } },
        .evidence = evidence_ids,
    };
    // A_k: d_k = f(k) (instruction depth + 1 + k, value 7 + depth + k); then A_{k + 1}, or the escape arm, else J_k.
    for (1..depth + 1) |k| {
        const call_index = depth + 1 + k;
        const decision = 7 + depth + k;
        values[decision] = .{
            .id = value_ids[decision],
            .function = worker,
            .origin = .{ .instruction_result = .{ .instruction = instruction_ids[call_index], .index = 0 } },
        };
        instructions[call_index] = .{
            .id = instruction_ids[call_index],
            .block = block_ids[2 * k],
            .operation = .{ .call = .{ .callee = value_ids[0], .arguments = value_ids[7 + k .. 8 + k], .result_arity = .{ .fixed = 1 } } },
            .results = value_ids[decision .. decision + 1],
            .effects = .dynamic_call,
            .evidence = evidence_ids,
        };
        blocks[2 * k] = .{
            .id = block_ids[2 * k],
            .function = worker,
            .instructions = instruction_ids[call_index .. call_index + 1],
            .terminator = .{ .branch = .{
                .condition = value_ids[decision],
                .then_edge = .{ .target = if (k == depth) block_ids[2 * depth + 2] else block_ids[2 * k + 2] },
                .else_edge = .{ .target = block_ids[2 * k + 1] },
            } },
            .evidence = evidence_ids,
        };
    }
    // The escape arm: observe(0), then J1.
    const escape_note = 2 * depth + 2;
    instructions[escape_note] = .{
        .id = instruction_ids[escape_note],
        .block = block_ids[2 * depth + 2],
        .operation = .{ .call = .{ .callee = value_ids[1], .arguments = value_ids[7..8], .result_arity = .{ .fixed = 0 } } },
        .results = &.{},
        .effects = .dynamic_call,
        .evidence = evidence_ids,
    };
    blocks[2 * depth + 2] = .{
        .id = block_ids[2 * depth + 2],
        .function = worker,
        .instructions = instruction_ids[escape_note .. escape_note + 1],
        .terminator = .{ .jump = .{ .target = block_ids[3] } },
        .evidence = evidence_ids,
    };
    // J_k for k = depth, ..., 2: observe(k), then J_{k - 1}.
    for (2..depth + 1) |k| {
        const note = 3 * depth + 3 - k;
        instructions[note] = .{
            .id = instruction_ids[note],
            .block = block_ids[2 * k + 1],
            .operation = .{ .call = .{ .callee = value_ids[1], .arguments = value_ids[7 + k .. 8 + k], .result_arity = .{ .fixed = 0 } } },
            .results = &.{},
            .effects = .dynamic_call,
            .evidence = evidence_ids,
        };
        blocks[2 * k + 1] = .{
            .id = block_ids[2 * k + 1],
            .function = worker,
            .instructions = instruction_ids[note .. note + 1],
            .terminator = .{ .jump = .{ .target = block_ids[2 * k - 1] } },
            .evidence = evidence_ids,
        };
    }
    // J1: observe(1), then f(-1) chooses between returning marker and first.
    const join_note = 3 * depth + 2;
    const tail_call = 3 * depth + 3;
    const tail = 2 * depth + 8;
    instructions[join_note] = .{
        .id = instruction_ids[join_note],
        .block = block_ids[3],
        .operation = .{ .call = .{ .callee = value_ids[1], .arguments = value_ids[8..9], .result_arity = .{ .fixed = 0 } } },
        .results = &.{},
        .effects = .dynamic_call,
        .evidence = evidence_ids,
    };
    values[tail] = .{
        .id = value_ids[tail],
        .function = worker,
        .origin = .{ .instruction_result = .{ .instruction = instruction_ids[tail_call], .index = 0 } },
    };
    instructions[tail_call] = .{
        .id = instruction_ids[tail_call],
        .block = block_ids[3],
        .operation = .{ .call = .{ .callee = value_ids[0], .arguments = value_ids[6..7], .result_arity = .{ .fixed = 1 } } },
        .results = value_ids[tail .. tail + 1],
        .effects = .dynamic_call,
        .evidence = evidence_ids,
    };
    blocks[3] = .{
        .id = block_ids[3],
        .function = worker,
        .instructions = instruction_ids[join_note .. tail_call + 1],
        .terminator = .{ .branch = .{
            .condition = value_ids[tail],
            .then_edge = .{ .target = block_ids[2 * depth + 3] },
            .else_edge = .{ .target = block_ids[2 * depth + 4] },
        } },
        .evidence = evidence_ids,
    };
    blocks[2 * depth + 3] = .{
        .id = block_ids[2 * depth + 3],
        .function = worker,
        .terminator = .{ .return_values = value_ids[2..3] },
        .evidence = evidence_ids,
    };
    blocks[2 * depth + 4] = .{
        .id = block_ids[2 * depth + 4],
        .function = worker,
        .terminator = .{ .return_values = value_ids[3..4] },
        .evidence = evidence_ids,
    };
    // The chunk returns the worker.
    const exported_value = 2 * depth + 9;
    const exported = 3 * depth + 4;
    values[exported_value] = .{
        .id = value_ids[exported_value],
        .function = chunk,
        .type = .function,
        .origin = .{ .instruction_result = .{ .instruction = instruction_ids[exported], .index = 0 } },
    };
    instructions[exported] = .{
        .id = instruction_ids[exported],
        .block = block_ids[0],
        .operation = .{ .function_ref = worker },
        .results = value_ids[exported_value .. exported_value + 1],
        .effects = .pure,
        .evidence = evidence_ids,
    };
    blocks[0] = .{
        .id = block_ids[0],
        .function = chunk,
        .instructions = instruction_ids[exported .. exported + 1],
        .terminator = .{ .return_values = value_ids[exported_value .. exported_value + 1] },
        .evidence = evidence_ids,
    };

    const functions = try allocator.dupe(ir.Function, &.{
        .{ .id = chunk, .blocks = block_ids[0..1], .entry_block = block_ids[0], .evidence = evidence_ids },
        .{ .id = worker, .parameters = value_ids[0..6], .blocks = block_ids[1..], .entry_block = block_ids[1], .evidence = evidence_ids },
    });
    const evidence = try allocator.dupe(ir.Evidence, &.{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:escape-chain",
    }});
    return .{
        .program_id = "escape-chain",
        .entry_function = chunk,
        .functions = functions,
        .blocks = blocks,
        .instructions = instructions,
        .values = values,
        .evidence = evidence,
    };
}

test "an escape chain counts the transfer wrappers made only for its free target in the syntax budget" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    // Each arm is one `if` level and each of its transfer wrappers one `repeat` level: 2 x 300 levels.
    const excessive = try escapeChainProgram(arena.allocator(), 300);
    var excessive_report = try validation.validate(std.testing.allocator, &excessive, .readable_luau);
    defer excessive_report.deinit();
    try std.testing.expectEqual(@as(usize, 1), excessive_report.diagnostics.items.len);
    try std.testing.expect(excessive_report.contains(.unsupported_readable_syntax_depth));

    // 2 x 256 = 512 levels, the budget itself.
    const boundary = try escapeChainProgram(arena.allocator(), 256);
    var boundary_report = try validation.validate(std.testing.allocator, &boundary, .readable_luau);
    defer boundary_report.deinit();
    try std.testing.expect(boundary_report.isClean());
}
