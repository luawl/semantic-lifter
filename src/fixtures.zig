//! Family-neutral conformance fixtures for the core contract.

const ir = @import("ir.zig");

pub const arithmetic_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_entry = ir.FunctionId.fromIndex(0);
    pub const f_add = ir.FunctionId.fromIndex(1);
    pub const b_entry = ir.BlockId.fromIndex(0);
    pub const b_add = ir.BlockId.fromIndex(1);
    pub const i_export = ir.InstructionId.fromIndex(0);
    pub const i_sum = ir.InstructionId.fromIndex(1);
    pub const i_factor = ir.InstructionId.fromIndex(2);
    pub const i_result = ir.InstructionId.fromIndex(3);
    pub const v_export = ir.ValueId.fromIndex(0);
    pub const v_left = ir.ValueId.fromIndex(1);
    pub const v_right = ir.ValueId.fromIndex(2);
    pub const v_sum = ir.ValueId.fromIndex(3);
    pub const v_factor = ir.ValueId.fromIndex(4);
    pub const v_result = ir.ValueId.fromIndex(5);

    pub const values = [_]ir.Value{
        .{ .id = v_export, .function = f_entry, .type = .function, .name_hint = "exported", .origin = .{ .instruction_result = .{ .instruction = i_export, .index = 0 } } },
        .{ .id = v_left, .function = f_add, .type = .integer, .name_hint = "left", .origin = .{ .parameter = 0 } },
        .{ .id = v_right, .function = f_add, .type = .integer, .name_hint = "right", .origin = .{ .parameter = 1 } },
        .{ .id = v_sum, .function = f_add, .type = .integer, .name_hint = "sum", .origin = .{ .instruction_result = .{ .instruction = i_sum, .index = 0 } } },
        .{ .id = v_factor, .function = f_add, .type = .integer, .name_hint = "factor", .origin = .{ .instruction_result = .{ .instruction = i_factor, .index = 0 } } },
        .{ .id = v_result, .function = f_add, .type = .integer, .name_hint = "result", .origin = .{ .instruction_result = .{ .instruction = i_result, .index = 0 } } },
    };

    pub const instructions = [_]ir.Instruction{
        .{ .id = i_export, .block = b_entry, .operation = .{ .function_ref = f_add }, .results = &.{v_export}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_sum, .block = b_add, .operation = .{ .binary = .{ .operator = .add, .left = v_left, .right = v_right } }, .results = &.{v_sum}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_factor, .block = b_add, .operation = .{ .constant = .{ .integer = "2" } }, .results = &.{v_factor}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_result, .block = b_add, .operation = .{ .binary = .{ .operator = .multiply, .left = v_sum, .right = v_factor } }, .results = &.{v_result}, .effects = .pure, .evidence = &.{proof} },
    };

    pub const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f_entry, .instructions = &.{i_export}, .terminator = .{ .return_values = &.{v_export} }, .evidence = &.{proof} },
        .{ .id = b_add, .function = f_add, .instructions = &.{ i_sum, i_factor, i_result }, .terminator = .{ .return_values = &.{v_result} }, .evidence = &.{proof} },
    };

    pub const functions = [_]ir.Function{
        .{ .id = f_entry, .name_hint = "chunk", .blocks = &.{b_entry}, .entry_block = b_entry, .evidence = &.{proof} },
        .{ .id = f_add, .name_hint = "add_and_double", .parameters = &.{ v_left, v_right }, .blocks = &.{b_add}, .entry_block = b_add, .evidence = &.{proof} },
    };

    pub const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-arithmetic-module",
    }};

    pub const program: ir.Program = .{
        .program_id = "generic-arithmetic-module",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };
};

pub const function_reference_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_entry = ir.FunctionId.fromIndex(0);
    pub const f_left = ir.FunctionId.fromIndex(1);
    pub const f_right = ir.FunctionId.fromIndex(2);
    pub const b_entry = ir.BlockId.fromIndex(0);
    pub const b_left = ir.BlockId.fromIndex(1);
    pub const b_right = ir.BlockId.fromIndex(2);
    pub const i_left_a = ir.InstructionId.fromIndex(0);
    pub const i_left_b = ir.InstructionId.fromIndex(1);
    pub const i_left_copy = ir.InstructionId.fromIndex(2);
    pub const i_right = ir.InstructionId.fromIndex(3);
    pub const v_left_a = ir.ValueId.fromIndex(0);
    pub const v_left_b = ir.ValueId.fromIndex(1);
    pub const v_left_copy = ir.ValueId.fromIndex(2);
    pub const v_right = ir.ValueId.fromIndex(3);

    pub const values = [_]ir.Value{
        .{ .id = v_left_a, .function = f_entry, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = i_left_a, .index = 0 } } },
        .{ .id = v_left_b, .function = f_entry, .type = .function, .origin = .{ .instruction_result = .{ .instruction = i_left_b, .index = 0 } } },
        .{ .id = v_left_copy, .function = f_entry, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = i_left_copy, .index = 0 } } },
        .{ .id = v_right, .function = f_entry, .type = .function, .origin = .{ .instruction_result = .{ .instruction = i_right, .index = 0 } } },
    };

    pub const instructions = [_]ir.Instruction{
        .{ .id = i_left_a, .block = b_entry, .operation = .{ .function_ref = f_left }, .results = &.{v_left_a}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_left_b, .block = b_entry, .operation = .{ .function_ref = f_left }, .results = &.{v_left_b}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_left_copy, .block = b_entry, .operation = .{ .copy = v_left_a }, .results = &.{v_left_copy}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_right, .block = b_entry, .operation = .{ .function_ref = f_right }, .results = &.{v_right}, .effects = .pure, .evidence = &.{proof} },
    };

    pub const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f_entry, .instructions = &.{ i_left_a, i_left_b, i_left_copy, i_right }, .terminator = .{ .return_values = &.{ v_left_a, v_left_b, v_left_copy, v_right } }, .evidence = &.{proof} },
        .{ .id = b_left, .function = f_left, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
        .{ .id = b_right, .function = f_right, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
    };

    pub const functions = [_]ir.Function{
        .{ .id = f_entry, .blocks = &.{b_entry}, .entry_block = b_entry, .evidence = &.{proof} },
        .{ .id = f_left, .name_hint = "left", .blocks = &.{b_left}, .entry_block = b_left, .evidence = &.{proof} },
        .{ .id = f_right, .name_hint = "right", .blocks = &.{b_right}, .entry_block = b_right, .evidence = &.{proof} },
    };

    pub const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-function-reference-identity",
    }};

    pub const program: ir.Program = .{
        .program_id = "generic-function-reference-identity",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };
};

pub const dynamic_truthiness_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_entry = ir.FunctionId.fromIndex(0);
    pub const f_truthy = ir.FunctionId.fromIndex(1);
    pub const f_falsy = ir.FunctionId.fromIndex(2);
    pub const b_entry = ir.BlockId.fromIndex(0);
    pub const b_truthy_entry = ir.BlockId.fromIndex(1);
    pub const b_truthy_then = ir.BlockId.fromIndex(2);
    pub const b_truthy_else = ir.BlockId.fromIndex(3);
    pub const b_falsy_entry = ir.BlockId.fromIndex(4);
    pub const b_falsy_then = ir.BlockId.fromIndex(5);
    pub const b_falsy_else = ir.BlockId.fromIndex(6);
    pub const b_truthy_not_result = ir.BlockId.fromIndex(7);
    pub const b_falsy_not_result = ir.BlockId.fromIndex(8);
    pub const i_truthy_export = ir.InstructionId.fromIndex(0);
    pub const i_falsy_export = ir.InstructionId.fromIndex(1);
    pub const i_truthy_literal = ir.InstructionId.fromIndex(2);
    pub const i_truthy_condition = ir.InstructionId.fromIndex(3);
    pub const i_truthy_result = ir.InstructionId.fromIndex(4);
    pub const i_truthy_fallback = ir.InstructionId.fromIndex(5);
    pub const i_falsy_literal = ir.InstructionId.fromIndex(6);
    pub const i_falsy_condition = ir.InstructionId.fromIndex(7);
    pub const i_falsy_fallback = ir.InstructionId.fromIndex(8);
    pub const i_falsy_result = ir.InstructionId.fromIndex(9);
    pub const i_truthy_not = ir.InstructionId.fromIndex(10);
    pub const i_falsy_not = ir.InstructionId.fromIndex(11);
    pub const v_truthy_export = ir.ValueId.fromIndex(0);
    pub const v_falsy_export = ir.ValueId.fromIndex(1);
    pub const v_truthy_literal = ir.ValueId.fromIndex(2);
    pub const v_truthy_condition = ir.ValueId.fromIndex(3);
    pub const v_truthy_result = ir.ValueId.fromIndex(4);
    pub const v_truthy_fallback = ir.ValueId.fromIndex(5);
    pub const v_falsy_literal = ir.ValueId.fromIndex(6);
    pub const v_falsy_condition = ir.ValueId.fromIndex(7);
    pub const v_falsy_fallback = ir.ValueId.fromIndex(8);
    pub const v_falsy_result = ir.ValueId.fromIndex(9);
    pub const v_truthy_not = ir.ValueId.fromIndex(10);
    pub const v_falsy_not = ir.ValueId.fromIndex(11);

    pub const values = [_]ir.Value{
        .{ .id = v_truthy_export, .function = f_entry, .type = .function, .name_hint = "truthy_branch", .origin = .{ .instruction_result = .{ .instruction = i_truthy_export, .index = 0 } } },
        .{ .id = v_falsy_export, .function = f_entry, .type = .function, .name_hint = "falsy_branch", .origin = .{ .instruction_result = .{ .instruction = i_falsy_export, .index = 0 } } },
        .{ .id = v_truthy_literal, .function = f_truthy, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = i_truthy_literal, .index = 0 } } },
        .{ .id = v_truthy_condition, .function = f_truthy, .type = .dynamic, .name_hint = "condition", .origin = .{ .instruction_result = .{ .instruction = i_truthy_condition, .index = 0 } } },
        .{ .id = v_truthy_result, .function = f_truthy, .type = .string, .origin = .{ .instruction_result = .{ .instruction = i_truthy_result, .index = 0 } } },
        .{ .id = v_truthy_fallback, .function = f_truthy, .type = .string, .origin = .{ .instruction_result = .{ .instruction = i_truthy_fallback, .index = 0 } } },
        .{ .id = v_falsy_literal, .function = f_falsy, .type = .dynamic, .origin = .{ .instruction_result = .{ .instruction = i_falsy_literal, .index = 0 } } },
        .{ .id = v_falsy_condition, .function = f_falsy, .type = .dynamic, .name_hint = "condition", .origin = .{ .instruction_result = .{ .instruction = i_falsy_condition, .index = 0 } } },
        .{ .id = v_falsy_fallback, .function = f_falsy, .type = .string, .origin = .{ .instruction_result = .{ .instruction = i_falsy_fallback, .index = 0 } } },
        .{ .id = v_falsy_result, .function = f_falsy, .type = .string, .origin = .{ .instruction_result = .{ .instruction = i_falsy_result, .index = 0 } } },
        .{ .id = v_truthy_not, .function = f_truthy, .type = .boolean, .name_hint = "not_condition", .origin = .{ .instruction_result = .{ .instruction = i_truthy_not, .index = 0 } } },
        .{ .id = v_falsy_not, .function = f_falsy, .type = .boolean, .name_hint = "not_condition", .origin = .{ .instruction_result = .{ .instruction = i_falsy_not, .index = 0 } } },
    };

    pub const instructions = [_]ir.Instruction{
        .{ .id = i_truthy_export, .block = b_entry, .operation = .{ .function_ref = f_truthy }, .results = &.{v_truthy_export}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_falsy_export, .block = b_entry, .operation = .{ .function_ref = f_falsy }, .results = &.{v_falsy_export}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_truthy_literal, .block = b_truthy_entry, .operation = .{ .constant = .{ .string = "present" } }, .results = &.{v_truthy_literal}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_truthy_condition, .block = b_truthy_entry, .operation = .{ .copy = v_truthy_literal }, .results = &.{v_truthy_condition}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_truthy_result, .block = b_truthy_not_result, .operation = .{ .constant = .{ .string = "truthy" } }, .results = &.{v_truthy_result}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_truthy_fallback, .block = b_truthy_else, .operation = .{ .constant = .{ .string = "wrong-truthy-arm" } }, .results = &.{v_truthy_fallback}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_falsy_literal, .block = b_falsy_entry, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{v_falsy_literal}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_falsy_condition, .block = b_falsy_entry, .operation = .{ .copy = v_falsy_literal }, .results = &.{v_falsy_condition}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_falsy_fallback, .block = b_falsy_then, .operation = .{ .constant = .{ .string = "wrong-falsy-arm" } }, .results = &.{v_falsy_fallback}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_falsy_result, .block = b_falsy_not_result, .operation = .{ .constant = .{ .string = "falsy" } }, .results = &.{v_falsy_result}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_truthy_not, .block = b_truthy_then, .operation = .{ .unary = .{ .operator = .logical_not, .operand = v_truthy_condition } }, .results = &.{v_truthy_not}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_falsy_not, .block = b_falsy_else, .operation = .{ .unary = .{ .operator = .logical_not, .operand = v_falsy_condition } }, .results = &.{v_falsy_not}, .effects = .pure, .evidence = &.{proof} },
    };

    pub const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f_entry, .instructions = &.{ i_truthy_export, i_falsy_export }, .terminator = .{ .return_values = &.{ v_truthy_export, v_falsy_export } }, .evidence = &.{proof} },
        .{ .id = b_truthy_entry, .function = f_truthy, .instructions = &.{ i_truthy_literal, i_truthy_condition }, .terminator = .{ .branch = .{
            .condition = v_truthy_condition,
            .then_edge = .{ .target = b_truthy_then },
            .else_edge = .{ .target = b_truthy_else },
        } }, .evidence = &.{proof} },
        .{ .id = b_truthy_then, .function = f_truthy, .instructions = &.{i_truthy_not}, .terminator = .{ .branch = .{
            .condition = v_truthy_not,
            .then_edge = .{ .target = b_truthy_else },
            .else_edge = .{ .target = b_truthy_not_result },
        } }, .evidence = &.{proof} },
        .{ .id = b_truthy_else, .function = f_truthy, .instructions = &.{i_truthy_fallback}, .terminator = .{ .return_values = &.{v_truthy_fallback} }, .evidence = &.{proof} },
        .{ .id = b_falsy_entry, .function = f_falsy, .instructions = &.{ i_falsy_literal, i_falsy_condition }, .terminator = .{ .branch = .{
            .condition = v_falsy_condition,
            .then_edge = .{ .target = b_falsy_then },
            .else_edge = .{ .target = b_falsy_else },
        } }, .evidence = &.{proof} },
        .{ .id = b_falsy_then, .function = f_falsy, .instructions = &.{i_falsy_fallback}, .terminator = .{ .return_values = &.{v_falsy_fallback} }, .evidence = &.{proof} },
        .{ .id = b_falsy_else, .function = f_falsy, .instructions = &.{i_falsy_not}, .terminator = .{ .branch = .{
            .condition = v_falsy_not,
            .then_edge = .{ .target = b_falsy_not_result },
            .else_edge = .{ .target = b_falsy_then },
        } }, .evidence = &.{proof} },
        .{ .id = b_truthy_not_result, .function = f_truthy, .instructions = &.{i_truthy_result}, .terminator = .{ .return_values = &.{v_truthy_result} }, .evidence = &.{proof} },
        .{ .id = b_falsy_not_result, .function = f_falsy, .instructions = &.{i_falsy_result}, .terminator = .{ .return_values = &.{v_falsy_result} }, .evidence = &.{proof} },
    };

    pub const functions = [_]ir.Function{
        .{ .id = f_entry, .name_hint = "chunk", .blocks = &.{b_entry}, .entry_block = b_entry, .evidence = &.{proof} },
        .{ .id = f_truthy, .name_hint = "truthy_branch", .blocks = &.{ b_truthy_entry, b_truthy_then, b_truthy_else, b_truthy_not_result }, .entry_block = b_truthy_entry, .evidence = &.{proof} },
        .{ .id = f_falsy, .name_hint = "falsy_branch", .blocks = &.{ b_falsy_entry, b_falsy_then, b_falsy_else, b_falsy_not_result }, .entry_block = b_falsy_entry, .evidence = &.{proof} },
    };

    pub const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-dynamic-truthiness",
    }};

    pub const program: ir.Program = .{
        .program_id = "generic-dynamic-truthiness",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };
};

pub const fresh_reference_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_entry = ir.FunctionId.fromIndex(0);
    pub const f_worker = ir.FunctionId.fromIndex(1);
    pub const b_entry = ir.BlockId.fromIndex(0);
    pub const b_worker = ir.BlockId.fromIndex(1);
    pub const i_worker = ir.InstructionId.fromIndex(0);
    pub const i_table_a = ir.InstructionId.fromIndex(1);
    pub const i_table_b = ir.InstructionId.fromIndex(2);
    pub const i_table_copy = ir.InstructionId.fromIndex(3);
    pub const i_thread_a = ir.InstructionId.fromIndex(4);
    pub const i_thread_b = ir.InstructionId.fromIndex(5);
    pub const v_worker = ir.ValueId.fromIndex(0);
    pub const v_table_a = ir.ValueId.fromIndex(1);
    pub const v_table_b = ir.ValueId.fromIndex(2);
    pub const v_table_copy = ir.ValueId.fromIndex(3);
    pub const v_thread_a = ir.ValueId.fromIndex(4);
    pub const v_thread_b = ir.ValueId.fromIndex(5);

    pub const values = [_]ir.Value{
        .{ .id = v_worker, .function = f_entry, .type = .function, .name_hint = "worker", .origin = .{ .instruction_result = .{ .instruction = i_worker, .index = 0 } } },
        .{ .id = v_table_a, .function = f_entry, .type = .dynamic, .name_hint = "first_table", .origin = .{ .instruction_result = .{ .instruction = i_table_a, .index = 0 } } },
        .{ .id = v_table_b, .function = f_entry, .type = .{ .kind = .table }, .name_hint = "second_table", .origin = .{ .instruction_result = .{ .instruction = i_table_b, .index = 0 } } },
        .{ .id = v_table_copy, .function = f_entry, .type = .dynamic, .name_hint = "first_table_copy", .origin = .{ .instruction_result = .{ .instruction = i_table_copy, .index = 0 } } },
        .{ .id = v_thread_a, .function = f_entry, .type = .dynamic, .name_hint = "first_thread", .origin = .{ .instruction_result = .{ .instruction = i_thread_a, .index = 0 } } },
        .{ .id = v_thread_b, .function = f_entry, .type = .{ .kind = .thread }, .name_hint = "second_thread", .origin = .{ .instruction_result = .{ .instruction = i_thread_b, .index = 0 } } },
    };

    pub const instructions = [_]ir.Instruction{
        .{ .id = i_worker, .block = b_entry, .operation = .{ .function_ref = f_worker }, .results = &.{v_worker}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_table_a, .block = b_entry, .operation = .{ .make_table = {} }, .results = &.{v_table_a}, .effects = .table_constructor, .evidence = &.{proof} },
        .{ .id = i_table_b, .block = b_entry, .operation = .{ .make_table_literal = .{ .fields = &.{} } }, .results = &.{v_table_b}, .effects = .table_constructor, .evidence = &.{proof} },
        .{ .id = i_table_copy, .block = b_entry, .operation = .{ .copy = v_table_a }, .results = &.{v_table_copy}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_thread_a, .block = b_entry, .operation = .{ .coroutine_create = .{ .callee = v_worker } }, .results = &.{v_thread_a}, .effects = .coroutine_create, .evidence = &.{proof} },
        .{ .id = i_thread_b, .block = b_entry, .operation = .{ .coroutine_create = .{ .callee = v_worker } }, .results = &.{v_thread_b}, .effects = .coroutine_create, .evidence = &.{proof} },
    };

    pub const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f_entry, .instructions = &.{ i_worker, i_table_a, i_table_b, i_table_copy, i_thread_a, i_thread_b }, .terminator = .{ .return_values = &.{ v_table_a, v_table_b, v_table_copy, v_thread_a, v_thread_b } }, .evidence = &.{proof} },
        .{ .id = b_worker, .function = f_worker, .instructions = &.{}, .terminator = .{ .return_values = &.{} }, .evidence = &.{proof} },
    };

    pub const functions = [_]ir.Function{
        .{ .id = f_entry, .name_hint = "chunk", .blocks = &.{b_entry}, .entry_block = b_entry, .evidence = &.{proof} },
        .{ .id = f_worker, .name_hint = "worker", .blocks = &.{b_worker}, .entry_block = b_worker, .evidence = &.{proof} },
    };

    pub const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:fresh-reference-identity",
    }};

    pub const program: ir.Program = .{
        .program_id = "fresh-reference-identity",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };
};

pub const automatic_promotion_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_entry = ir.FunctionId.fromIndex(0);
    pub const f_probe = ir.FunctionId.fromIndex(1);
    pub const b_chunk = ir.BlockId.fromIndex(0);
    pub const b_entry = ir.BlockId.fromIndex(1);
    pub const b_matched = ir.BlockId.fromIndex(2);
    pub const b_unreachable = ir.BlockId.fromIndex(3);
    pub const i_export = ir.InstructionId.fromIndex(0);
    pub const i_left = ir.InstructionId.fromIndex(1);
    pub const i_mask = ir.InstructionId.fromIndex(2);
    pub const i_zero = ir.InstructionId.fromIndex(3);
    pub const i_masked = ir.InstructionId.fromIndex(4);
    pub const i_condition = ir.InstructionId.fromIndex(5);
    pub const i_matched = ir.InstructionId.fromIndex(6);
    pub const i_unreachable = ir.InstructionId.fromIndex(7);
    pub const v_export = ir.ValueId.fromIndex(0);
    pub const v_left = ir.ValueId.fromIndex(1);
    pub const v_mask = ir.ValueId.fromIndex(2);
    pub const v_zero = ir.ValueId.fromIndex(3);
    pub const v_masked = ir.ValueId.fromIndex(4);
    pub const v_condition = ir.ValueId.fromIndex(5);
    pub const v_matched = ir.ValueId.fromIndex(6);
    pub const v_unreachable = ir.ValueId.fromIndex(7);
    pub const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };

    pub const values = [_]ir.Value{
        .{ .id = v_export, .function = f_entry, .type = .function, .name_hint = "exported", .origin = .{ .instruction_result = .{ .instruction = i_export, .index = 0 } } },
        .{ .id = v_left, .function = f_probe, .type = u32_type, .name_hint = "left", .origin = .{ .instruction_result = .{ .instruction = i_left, .index = 0 } } },
        .{ .id = v_mask, .function = f_probe, .type = u32_type, .name_hint = "mask", .origin = .{ .instruction_result = .{ .instruction = i_mask, .index = 0 } } },
        .{ .id = v_zero, .function = f_probe, .type = u32_type, .name_hint = "zero", .origin = .{ .instruction_result = .{ .instruction = i_zero, .index = 0 } } },
        .{ .id = v_masked, .function = f_probe, .type = u32_type, .name_hint = "masked", .origin = .{ .instruction_result = .{ .instruction = i_masked, .index = 0 } } },
        .{ .id = v_condition, .function = f_probe, .type = .boolean, .name_hint = "is_zero", .origin = .{ .instruction_result = .{ .instruction = i_condition, .index = 0 } } },
        .{ .id = v_matched, .function = f_probe, .type = .string, .name_hint = "matched", .origin = .{ .instruction_result = .{ .instruction = i_matched, .index = 0 } } },
        .{ .id = v_unreachable, .function = f_probe, .type = .string, .name_hint = "unreachable", .origin = .{ .instruction_result = .{ .instruction = i_unreachable, .index = 0 } } },
    };

    pub const instructions = [_]ir.Instruction{
        .{ .id = i_export, .block = b_chunk, .operation = .{ .function_ref = f_probe }, .results = &.{v_export}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_left, .block = b_entry, .operation = .{ .constant = .{ .integer = "6" } }, .results = &.{v_left}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_mask, .block = b_entry, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_mask}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_zero, .block = b_entry, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_zero}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_masked, .block = b_entry, .operation = .{ .binary = .{
            .operator = .bit_and,
            .left = v_left,
            .right = v_mask,
            .mode = .primitive,
        } }, .results = &.{v_masked}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_condition, .block = b_entry, .operation = .{ .binary = .{
            .operator = .equal,
            .left = v_masked,
            .right = v_zero,
            .mode = .primitive,
        } }, .results = &.{v_condition}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_matched, .block = b_matched, .operation = .{ .constant = .{ .string = "matched" } }, .results = &.{v_matched}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_unreachable, .block = b_unreachable, .operation = .{ .constant = .{ .string = "unreachable" } }, .results = &.{v_unreachable}, .effects = .pure, .evidence = &.{proof} },
    };

    pub const blocks = [_]ir.Block{
        .{ .id = b_chunk, .function = f_entry, .instructions = &.{i_export}, .terminator = .{ .return_values = &.{v_export} }, .evidence = &.{proof} },
        .{ .id = b_entry, .function = f_probe, .instructions = &.{ i_left, i_mask, i_zero, i_masked, i_condition }, .terminator = .{ .branch = .{
            .condition = v_condition,
            .then_edge = .{ .target = b_matched },
            .else_edge = .{ .target = b_unreachable },
        } }, .evidence = &.{proof} },
        .{ .id = b_matched, .function = f_probe, .instructions = &.{i_matched}, .terminator = .{ .return_values = &.{v_matched} }, .evidence = &.{proof} },
        .{ .id = b_unreachable, .function = f_probe, .instructions = &.{i_unreachable}, .terminator = .{ .return_values = &.{v_unreachable} }, .evidence = &.{proof} },
    };

    pub const functions = [_]ir.Function{
        .{ .id = f_entry, .name_hint = "chunk", .blocks = &.{b_chunk}, .entry_block = b_chunk, .evidence = &.{proof} },
        .{ .id = f_probe, .name_hint = "probe", .blocks = &.{ b_entry, b_matched, b_unreachable }, .entry_block = b_entry, .evidence = &.{proof} },
    };

    pub const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-automatic-solver-promotion",
    }};

    pub const program: ir.Program = .{
        .program_id = "generic-automatic-solver-promotion",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };
};

pub const relational_dispatch_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_entry = ir.FunctionId.fromIndex(0);
    pub const f_probe = ir.FunctionId.fromIndex(1);
    pub const b_chunk = ir.BlockId.fromIndex(0);
    pub const b_entry = ir.BlockId.fromIndex(1);
    pub const b_left = ir.BlockId.fromIndex(2);
    pub const b_right = ir.BlockId.fromIndex(3);
    pub const b_dispatch = ir.BlockId.fromIndex(4);
    pub const b_true = ir.BlockId.fromIndex(5);
    pub const b_false = ir.BlockId.fromIndex(6);
    pub const i_export = ir.InstructionId.fromIndex(0);
    pub const i_left_state = ir.InstructionId.fromIndex(1);
    pub const i_right_state = ir.InstructionId.fromIndex(2);
    pub const i_one = ir.InstructionId.fromIndex(3);
    pub const i_next_state = ir.InstructionId.fromIndex(4);
    pub const i_eight = ir.InstructionId.fromIndex(5);
    pub const i_condition = ir.InstructionId.fromIndex(6);
    pub const i_true_result = ir.InstructionId.fromIndex(7);
    pub const i_false_result = ir.InstructionId.fromIndex(8);
    pub const v_export = ir.ValueId.fromIndex(0);
    pub const v_selector = ir.ValueId.fromIndex(1);
    pub const v_left_state = ir.ValueId.fromIndex(2);
    pub const v_right_state = ir.ValueId.fromIndex(3);
    pub const v_dispatch_state = ir.ValueId.fromIndex(4);
    pub const v_one = ir.ValueId.fromIndex(5);
    pub const v_next_state = ir.ValueId.fromIndex(6);
    pub const v_eight = ir.ValueId.fromIndex(7);
    pub const v_condition = ir.ValueId.fromIndex(8);
    pub const v_true_result = ir.ValueId.fromIndex(9);
    pub const v_false_result = ir.ValueId.fromIndex(10);
    pub const t_state = ir.SolverTermId.fromIndex(0);
    pub const t_seven = ir.SolverTermId.fromIndex(1);
    pub const t_equal = ir.SolverTermId.fromIndex(2);
    pub const t_not_equal = ir.SolverTermId.fromIndex(3);
    pub const c_left = ir.ConstraintId.fromIndex(0);
    pub const c_right = ir.ConstraintId.fromIndex(1);

    pub const values = [_]ir.Value{
        .{ .id = v_export, .function = f_entry, .type = .function, .name_hint = "probe", .origin = .{ .instruction_result = .{ .instruction = i_export, .index = 0 } } },
        .{ .id = v_selector, .function = f_probe, .type = .boolean, .name_hint = "selector", .origin = .{ .parameter = 0 } },
        .{ .id = v_left_state, .function = f_probe, .type = .integer, .name_hint = "left_state", .origin = .{ .instruction_result = .{ .instruction = i_left_state, .index = 0 } } },
        .{ .id = v_right_state, .function = f_probe, .type = .integer, .name_hint = "right_state", .origin = .{ .instruction_result = .{ .instruction = i_right_state, .index = 0 } } },
        .{ .id = v_dispatch_state, .function = f_probe, .type = .integer, .name_hint = "state", .origin = .{ .block_parameter = .{ .block = b_dispatch, .index = 0 } } },
        .{ .id = v_one, .function = f_probe, .type = .integer, .name_hint = "step", .origin = .{ .instruction_result = .{ .instruction = i_one, .index = 0 } } },
        .{ .id = v_next_state, .function = f_probe, .type = .integer, .name_hint = "next_state", .origin = .{ .instruction_result = .{ .instruction = i_next_state, .index = 0 } } },
        .{ .id = v_eight, .function = f_probe, .type = .integer, .name_hint = "target_state", .origin = .{ .instruction_result = .{ .instruction = i_eight, .index = 0 } } },
        .{ .id = v_condition, .function = f_probe, .type = .boolean, .name_hint = "state_matches", .origin = .{ .instruction_result = .{ .instruction = i_condition, .index = 0 } } },
        .{ .id = v_true_result, .function = f_probe, .type = .string, .name_hint = "matched", .origin = .{ .instruction_result = .{ .instruction = i_true_result, .index = 0 } } },
        .{ .id = v_false_result, .function = f_probe, .type = .string, .name_hint = "other", .origin = .{ .instruction_result = .{ .instruction = i_false_result, .index = 0 } } },
    };

    pub const instructions = [_]ir.Instruction{
        .{ .id = i_export, .block = b_chunk, .operation = .{ .function_ref = f_probe }, .results = &.{v_export}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_left_state, .block = b_left, .operation = .{ .constant = .{ .integer = "7" } }, .results = &.{v_left_state}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_right_state, .block = b_right, .operation = .{ .constant = .{ .integer = "8" } }, .results = &.{v_right_state}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_one, .block = b_dispatch, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_one}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_next_state, .block = b_dispatch, .operation = .{ .binary = .{ .operator = .add, .left = v_dispatch_state, .right = v_one, .mode = .primitive } }, .results = &.{v_next_state}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_eight, .block = b_dispatch, .operation = .{ .constant = .{ .integer = "8" } }, .results = &.{v_eight}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_condition, .block = b_dispatch, .operation = .{ .binary = .{ .operator = .equal, .left = v_next_state, .right = v_eight, .mode = .primitive } }, .results = &.{v_condition}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_true_result, .block = b_true, .operation = .{ .constant = .{ .string = "matched" } }, .results = &.{v_true_result}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_false_result, .block = b_false, .operation = .{ .constant = .{ .string = "other" } }, .results = &.{v_false_result}, .effects = .pure, .evidence = &.{proof} },
    };

    pub const blocks = [_]ir.Block{
        .{ .id = b_chunk, .function = f_entry, .instructions = &.{i_export}, .terminator = .{ .return_values = &.{v_export} }, .evidence = &.{proof} },
        .{ .id = b_entry, .function = f_probe, .terminator = .{ .branch = .{ .condition = v_selector, .then_edge = .{ .target = b_left }, .else_edge = .{ .target = b_right } } }, .evidence = &.{proof} },
        .{ .id = b_left, .function = f_probe, .instructions = &.{i_left_state}, .terminator = .{ .jump = .{ .target = b_dispatch, .arguments = &.{v_left_state} } }, .evidence = &.{proof} },
        .{ .id = b_right, .function = f_probe, .instructions = &.{i_right_state}, .terminator = .{ .jump = .{ .target = b_dispatch, .arguments = &.{v_right_state} } }, .evidence = &.{proof} },
        .{ .id = b_dispatch, .function = f_probe, .parameters = &.{v_dispatch_state}, .instructions = &.{ i_one, i_next_state, i_eight, i_condition }, .terminator = .{ .branch = .{ .condition = v_condition, .then_edge = .{ .target = b_true }, .else_edge = .{ .target = b_false } } }, .evidence = &.{proof} },
        .{ .id = b_true, .function = f_probe, .instructions = &.{i_true_result}, .terminator = .{ .return_values = &.{v_true_result} }, .evidence = &.{proof} },
        .{ .id = b_false, .function = f_probe, .instructions = &.{i_false_result}, .terminator = .{ .return_values = &.{v_false_result} }, .evidence = &.{proof} },
    };

    pub const functions = [_]ir.Function{
        .{ .id = f_entry, .name_hint = "chunk", .blocks = &.{b_chunk}, .entry_block = b_chunk, .evidence = &.{proof} },
        .{ .id = f_probe, .name_hint = "relational_dispatch", .parameters = &.{v_selector}, .blocks = &.{ b_entry, b_left, b_right, b_dispatch, b_true, b_false }, .entry_block = b_entry, .evidence = &.{proof} },
    };

    pub const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-relational-dispatch",
    }};
    pub const solver_terms = [_]ir.SolverTerm{
        .{ .id = t_state, .sort = .{ .kind = .integer }, .operation = .{ .value = v_dispatch_state } },
        .{ .id = t_seven, .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "7" } },
        .{ .id = t_equal, .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = t_state, .right = t_seven } } },
        .{ .id = t_not_equal, .sort = .{ .kind = .boolean }, .operation = .{ .logical_not = t_equal } },
    };
    pub const constraints = [_]ir.Constraint{
        .{ .id = c_left, .predicate = t_equal, .evidence = &.{proof}, .scope = .{ .edge = .{ .source = b_left, .kind = .jump, .target = b_dispatch } } },
        .{ .id = c_right, .predicate = t_not_equal, .evidence = &.{proof}, .scope = .{ .edge = .{ .source = b_right, .kind = .jump, .target = b_dispatch } } },
    };

    pub const program: ir.Program = .{
        .program_id = "generic-relational-dispatch",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
        .solver_terms = &solver_terms,
        .constraints = &constraints,
    };
};

pub const variadic_identity_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_entry = ir.FunctionId.fromIndex(0);
    pub const f_identity = ir.FunctionId.fromIndex(1);
    pub const b_entry = ir.BlockId.fromIndex(0);
    pub const b_identity = ir.BlockId.fromIndex(1);
    pub const i_export = ir.InstructionId.fromIndex(0);
    pub const v_export = ir.ValueId.fromIndex(0);
    pub const p_varargs = ir.ValuePackId.fromIndex(0);

    pub const values = [_]ir.Value{.{
        .id = v_export,
        .function = f_entry,
        .type = .function,
        .name_hint = "identity",
        .origin = .{ .instruction_result = .{ .instruction = i_export, .index = 0 } },
    }};
    pub const value_packs = [_]ir.ValuePack{.{
        .id = p_varargs,
        .function = f_identity,
        .origin = .{ .varargs = f_identity },
        .evidence = &.{proof},
    }};
    pub const instructions = [_]ir.Instruction{.{
        .id = i_export,
        .block = b_entry,
        .operation = .{ .function_ref = f_identity },
        .results = &.{v_export},
        .effects = .pure,
        .evidence = &.{proof},
    }};
    pub const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f_entry, .instructions = &.{i_export}, .terminator = .{ .return_values = &.{v_export} }, .evidence = &.{proof} },
        .{ .id = b_identity, .function = f_identity, .terminator = .{ .return_pack = p_varargs }, .evidence = &.{proof} },
    };
    pub const functions = [_]ir.Function{
        .{ .id = f_entry, .name_hint = "chunk", .blocks = &.{b_entry}, .entry_block = b_entry, .evidence = &.{proof} },
        .{
            .id = f_identity,
            .name_hint = "identity",
            .blocks = &.{b_identity},
            .entry_block = b_identity,
            .is_variadic = true,
            .vararg_pack = p_varargs,
            .evidence = &.{proof},
        },
    };
    pub const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-variadic-identity-module",
    }};
    pub const program: ir.Program = .{
        .program_id = "generic-variadic-identity-module",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &value_packs,
        .evidence = &evidence,
    };
};

pub const open_pack_adjust_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_entry = ir.FunctionId.fromIndex(0);
    pub const b_entry = ir.BlockId.fromIndex(0);
    pub const i_get = ir.InstructionId.fromIndex(0);
    pub const i_call = ir.InstructionId.fromIndex(1);
    pub const i_adjust = ir.InstructionId.fromIndex(2);
    pub const v_callee = ir.ValueId.fromIndex(0);
    pub const v_first = ir.ValueId.fromIndex(1);
    pub const p_results = ir.ValuePackId.fromIndex(0);

    pub const values = [_]ir.Value{
        .{ .id = v_callee, .function = f_entry, .type = .function, .origin = .{ .instruction_result = .{ .instruction = i_get, .index = 0 } } },
        .{ .id = v_first, .function = f_entry, .origin = .{ .instruction_result = .{ .instruction = i_adjust, .index = 0 } } },
    };
    pub const value_packs = [_]ir.ValuePack{.{
        .id = p_results,
        .function = f_entry,
        .origin = .{ .instruction_result = i_call },
        .evidence = &.{proof},
    }};
    pub const instructions = [_]ir.Instruction{
        .{ .id = i_get, .block = b_entry, .operation = .{ .environment_get = .{ .target = .{ .ambient = {} }, .name = "produce" } }, .results = &.{v_callee}, .effects = .semantic_environment_read, .evidence = &.{proof} },
        .{ .id = i_call, .block = b_entry, .operation = .{ .call = .{
            .callee = v_callee,
            .arguments = &.{},
            .result_arity = .{ .variadic = {} },
        } }, .results = &.{}, .pack_result = p_results, .effects = .dynamic_call, .evidence = &.{proof} },
        .{ .id = i_adjust, .block = b_entry, .operation = .{ .adjust_pack = p_results }, .results = &.{v_first}, .effects = .pure, .evidence = &.{proof} },
    };
    pub const blocks = [_]ir.Block{.{
        .id = b_entry,
        .function = f_entry,
        .instructions = &.{ i_get, i_call, i_adjust },
        .terminator = .{ .return_values = &.{v_first} },
        .evidence = &.{proof},
    }};
    pub const functions = [_]ir.Function{.{
        .id = f_entry,
        .blocks = &.{b_entry},
        .entry_block = b_entry,
        .evidence = &.{proof},
    }};
    pub const evidence = [_]ir.Evidence{.{ .id = proof, .kind = .dynamic_fixture, .locator = "fixture:generic-open-result-pack" }};
    pub const program: ir.Program = .{
        .program_id = "generic-open-result-pack",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &value_packs,
        .evidence = &evidence,
    };
};

pub const ordered_table_vararg_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_entry = ir.FunctionId.fromIndex(0);
    pub const b_entry = ir.BlockId.fromIndex(0);
    pub const i_table = ir.InstructionId.fromIndex(0);
    pub const i_append = ir.InstructionId.fromIndex(1);
    pub const v_table = ir.ValueId.fromIndex(0);
    pub const p_varargs = ir.ValuePackId.fromIndex(0);

    pub const values = [_]ir.Value{.{
        .id = v_table,
        .function = f_entry,
        .type = .{ .kind = .table },
        .origin = .{ .instruction_result = .{ .instruction = i_table, .index = 0 } },
    }};
    pub const value_packs = [_]ir.ValuePack{.{
        .id = p_varargs,
        .function = f_entry,
        .origin = .{ .varargs = f_entry },
        .evidence = &.{proof},
    }};
    pub const instructions = [_]ir.Instruction{
        .{
            .id = i_table,
            .block = b_entry,
            .operation = .{ .make_table = {} },
            .results = &.{v_table},
            .effects = .table_constructor,
            .evidence = &.{proof},
        },
        .{
            .id = i_append,
            .block = b_entry,
            .operation = .{ .table_set_pack = .{ .table = v_table, .first_index = 2, .pack = p_varargs } },
            .results = &.{},
            .effects = .raw_table_write,
            .evidence = &.{proof},
        },
    };
    pub const blocks = [_]ir.Block{.{
        .id = b_entry,
        .function = f_entry,
        .instructions = &.{ i_table, i_append },
        .terminator = .{ .return_values = &.{v_table} },
        .evidence = &.{proof},
    }};
    pub const functions = [_]ir.Function{.{
        .id = f_entry,
        .blocks = &.{b_entry},
        .entry_block = b_entry,
        .is_variadic = true,
        .vararg_pack = p_varargs,
        .evidence = &.{proof},
    }};
    pub const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-ordered-table-varargs",
    }};
    pub const program: ir.Program = .{
        .program_id = "generic-ordered-table-varargs",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &value_packs,
        .evidence = &evidence,
    };
};

pub const absolute_value_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_entry = ir.FunctionId.fromIndex(0);
    pub const f_absolute = ir.FunctionId.fromIndex(1);
    pub const b_chunk = ir.BlockId.fromIndex(0);
    pub const b_entry = ir.BlockId.fromIndex(1);
    pub const b_negative = ir.BlockId.fromIndex(2);
    pub const b_nonnegative = ir.BlockId.fromIndex(3);
    pub const b_join = ir.BlockId.fromIndex(4);
    pub const i_export = ir.InstructionId.fromIndex(0);
    pub const i_zero = ir.InstructionId.fromIndex(1);
    pub const i_is_negative = ir.InstructionId.fromIndex(2);
    pub const i_negate = ir.InstructionId.fromIndex(3);
    pub const v_export = ir.ValueId.fromIndex(0);
    pub const v_input = ir.ValueId.fromIndex(1);
    pub const v_zero = ir.ValueId.fromIndex(2);
    pub const v_is_negative = ir.ValueId.fromIndex(3);
    pub const v_negated = ir.ValueId.fromIndex(4);
    pub const v_absolute = ir.ValueId.fromIndex(5);

    pub const values = [_]ir.Value{
        .{ .id = v_export, .function = f_entry, .type = .function, .name_hint = "absolute", .origin = .{ .instruction_result = .{ .instruction = i_export, .index = 0 } } },
        .{ .id = v_input, .function = f_absolute, .type = .number, .name_hint = "input", .origin = .{ .parameter = 0 } },
        .{ .id = v_zero, .function = f_absolute, .type = .number, .name_hint = "zero", .origin = .{ .instruction_result = .{ .instruction = i_zero, .index = 0 } } },
        .{ .id = v_is_negative, .function = f_absolute, .type = .boolean, .name_hint = "is_negative", .origin = .{ .instruction_result = .{ .instruction = i_is_negative, .index = 0 } } },
        .{ .id = v_negated, .function = f_absolute, .type = .number, .name_hint = "negated", .origin = .{ .instruction_result = .{ .instruction = i_negate, .index = 0 } } },
        .{ .id = v_absolute, .function = f_absolute, .type = .number, .name_hint = "absolute", .origin = .{ .block_parameter = .{ .block = b_join, .index = 0 } } },
    };

    pub const instructions = [_]ir.Instruction{
        .{ .id = i_export, .block = b_chunk, .operation = .{ .function_ref = f_absolute }, .results = &.{v_export}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_zero, .block = b_entry, .operation = .{ .constant = .{ .integer = "0" } }, .results = &.{v_zero}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_is_negative, .block = b_entry, .operation = .{ .binary = .{ .operator = .less, .left = v_input, .right = v_zero } }, .results = &.{v_is_negative}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_negate, .block = b_negative, .operation = .{ .unary = .{ .operator = .negate, .operand = v_input } }, .results = &.{v_negated}, .effects = .pure, .evidence = &.{proof} },
    };

    pub const blocks = [_]ir.Block{
        .{ .id = b_chunk, .function = f_entry, .instructions = &.{i_export}, .terminator = .{ .return_values = &.{v_export} }, .evidence = &.{proof} },
        .{ .id = b_entry, .function = f_absolute, .instructions = &.{ i_zero, i_is_negative }, .terminator = .{ .branch = .{
            .condition = v_is_negative,
            .then_edge = .{ .target = b_negative },
            .else_edge = .{ .target = b_nonnegative },
        } }, .evidence = &.{proof} },
        .{ .id = b_negative, .function = f_absolute, .instructions = &.{i_negate}, .terminator = .{ .jump = .{ .target = b_join, .arguments = &.{v_negated} } }, .evidence = &.{proof} },
        .{ .id = b_nonnegative, .function = f_absolute, .terminator = .{ .jump = .{ .target = b_join, .arguments = &.{v_input} } }, .evidence = &.{proof} },
        .{ .id = b_join, .function = f_absolute, .parameters = &.{v_absolute}, .terminator = .{ .return_values = &.{v_absolute} }, .evidence = &.{proof} },
    };

    pub const functions = [_]ir.Function{
        .{ .id = f_entry, .name_hint = "chunk", .blocks = &.{b_chunk}, .entry_block = b_chunk, .evidence = &.{proof} },
        .{ .id = f_absolute, .name_hint = "absolute", .parameters = &.{v_input}, .blocks = &.{ b_join, b_negative, b_entry, b_nonnegative }, .entry_block = b_entry, .evidence = &.{proof} },
    };

    pub const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-absolute-value-module",
    }};

    pub const program: ir.Program = .{
        .program_id = "generic-absolute-value-module",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };
};

/// A function that tests a boolean condition in its entry block and again in the block the entry's then arm
/// enters: the entry computes `matches` and branches to the re-test block when it holds and to a block that
/// returns "outer" otherwise, and the re-test block returns "again" when `matches` holds and "never" otherwise.
/// With `compares_remainder`, `matches` is `x % y == 1`; otherwise it is `x == 1` and the remainder is unused.
pub fn RetestModule(comptime compares_remainder: bool) type {
    return struct {
        pub const proof = ir.EvidenceId.fromIndex(0);
        pub const f_chunk = ir.FunctionId.fromIndex(0);
        pub const f_probe = ir.FunctionId.fromIndex(1);
        pub const b_chunk = ir.BlockId.fromIndex(0);
        pub const b_entry = ir.BlockId.fromIndex(1);
        pub const b_retest = ir.BlockId.fromIndex(2);
        pub const b_outer = ir.BlockId.fromIndex(3);
        pub const b_again = ir.BlockId.fromIndex(4);
        pub const b_never = ir.BlockId.fromIndex(5);
        pub const i_export = ir.InstructionId.fromIndex(0);
        pub const i_one = ir.InstructionId.fromIndex(1);
        pub const i_remainder = ir.InstructionId.fromIndex(2);
        pub const i_matches = ir.InstructionId.fromIndex(3);
        pub const i_outer = ir.InstructionId.fromIndex(4);
        pub const i_again = ir.InstructionId.fromIndex(5);
        pub const i_never = ir.InstructionId.fromIndex(6);
        pub const v_x = ir.ValueId.fromIndex(0);
        pub const v_y = ir.ValueId.fromIndex(1);
        pub const v_export = ir.ValueId.fromIndex(2);
        pub const v_one = ir.ValueId.fromIndex(3);
        pub const v_remainder = ir.ValueId.fromIndex(4);
        pub const v_matches = ir.ValueId.fromIndex(5);
        pub const v_outer = ir.ValueId.fromIndex(6);
        pub const v_again = ir.ValueId.fromIndex(7);
        pub const v_never = ir.ValueId.fromIndex(8);

        pub const values = [_]ir.Value{
            .{ .id = v_x, .function = f_probe, .type = .integer, .name_hint = "x", .origin = .{ .parameter = 0 } },
            .{ .id = v_y, .function = f_probe, .type = .integer, .name_hint = "y", .origin = .{ .parameter = 1 } },
            .{ .id = v_export, .function = f_chunk, .type = .function, .name_hint = "probe", .origin = .{ .instruction_result = .{ .instruction = i_export, .index = 0 } } },
            .{ .id = v_one, .function = f_probe, .type = .integer, .name_hint = "one", .origin = .{ .instruction_result = .{ .instruction = i_one, .index = 0 } } },
            .{ .id = v_remainder, .function = f_probe, .type = .integer, .name_hint = "remainder", .origin = .{ .instruction_result = .{ .instruction = i_remainder, .index = 0 } } },
            .{ .id = v_matches, .function = f_probe, .type = .boolean, .name_hint = "matches", .origin = .{ .instruction_result = .{ .instruction = i_matches, .index = 0 } } },
            .{ .id = v_outer, .function = f_probe, .type = .string, .name_hint = "outer_result", .origin = .{ .instruction_result = .{ .instruction = i_outer, .index = 0 } } },
            .{ .id = v_again, .function = f_probe, .type = .string, .name_hint = "again_result", .origin = .{ .instruction_result = .{ .instruction = i_again, .index = 0 } } },
            .{ .id = v_never, .function = f_probe, .type = .string, .name_hint = "never_result", .origin = .{ .instruction_result = .{ .instruction = i_never, .index = 0 } } },
        };

        pub const instructions = [_]ir.Instruction{
            .{ .id = i_export, .block = b_chunk, .operation = .{ .function_ref = f_probe }, .results = &.{v_export}, .effects = .pure, .evidence = &.{proof} },
            .{ .id = i_one, .block = b_entry, .operation = .{ .constant = .{ .integer = "1" } }, .results = &.{v_one}, .effects = .pure, .evidence = &.{proof} },
            .{ .id = i_remainder, .block = b_entry, .operation = .{ .binary = .{ .operator = .modulo, .left = v_x, .right = v_y } }, .results = &.{v_remainder}, .effects = .pure, .evidence = &.{proof} },
            .{ .id = i_matches, .block = b_entry, .operation = .{ .binary = .{ .operator = .equal, .left = if (compares_remainder) v_remainder else v_x, .right = v_one } }, .results = &.{v_matches}, .effects = .pure, .evidence = &.{proof} },
            .{ .id = i_outer, .block = b_outer, .operation = .{ .constant = .{ .string = "outer" } }, .results = &.{v_outer}, .effects = .pure, .evidence = &.{proof} },
            .{ .id = i_again, .block = b_again, .operation = .{ .constant = .{ .string = "again" } }, .results = &.{v_again}, .effects = .pure, .evidence = &.{proof} },
            .{ .id = i_never, .block = b_never, .operation = .{ .constant = .{ .string = "never" } }, .results = &.{v_never}, .effects = .pure, .evidence = &.{proof} },
        };

        pub const blocks = [_]ir.Block{
            .{ .id = b_chunk, .function = f_chunk, .instructions = &.{i_export}, .terminator = .{ .return_values = &.{v_export} }, .evidence = &.{proof} },
            .{ .id = b_entry, .function = f_probe, .instructions = &.{ i_one, i_remainder, i_matches }, .terminator = .{ .branch = .{
                .condition = v_matches,
                .then_edge = .{ .target = b_retest },
                .else_edge = .{ .target = b_outer },
            } }, .evidence = &.{proof} },
            .{ .id = b_retest, .function = f_probe, .terminator = .{ .branch = .{
                .condition = v_matches,
                .then_edge = .{ .target = b_again },
                .else_edge = .{ .target = b_never },
            } }, .evidence = &.{proof} },
            .{ .id = b_outer, .function = f_probe, .instructions = &.{i_outer}, .terminator = .{ .return_values = &.{v_outer} }, .evidence = &.{proof} },
            .{ .id = b_again, .function = f_probe, .instructions = &.{i_again}, .terminator = .{ .return_values = &.{v_again} }, .evidence = &.{proof} },
            .{ .id = b_never, .function = f_probe, .instructions = &.{i_never}, .terminator = .{ .return_values = &.{v_never} }, .evidence = &.{proof} },
        };

        pub const functions = [_]ir.Function{
            .{ .id = f_chunk, .name_hint = "chunk", .blocks = &.{b_chunk}, .entry_block = b_chunk, .evidence = &.{proof} },
            .{ .id = f_probe, .name_hint = "probe", .parameters = &.{ v_x, v_y }, .blocks = &.{ b_entry, b_retest, b_outer, b_again, b_never }, .entry_block = b_entry, .evidence = &.{proof} },
        };

        pub const evidence = [_]ir.Evidence{.{
            .id = proof,
            .kind = .dynamic_fixture,
            .locator = if (compares_remainder) "fixture:uncovered-guard-retest-module" else "fixture:relevant-retest-module",
        }};

        pub const program: ir.Program = .{
            .program_id = if (compares_remainder) "uncovered-guard-retest-module" else "relevant-retest-module",
            .entry_function = f_chunk,
            .functions = &functions,
            .blocks = &blocks,
            .instructions = &instructions,
            .values = &values,
            .evidence = &evidence,
        };
    };
}

pub const uncovered_guard_retest_module = RetestModule(true);
pub const relevant_retest_module = RetestModule(false);

/// `relevant_retest_module` with the entry's then arm reaching the re-test block through two forwarding
/// blocks that earlier rewrites folded away: the live then edge targets the re-test block, and the arm's
/// history starts at the first forwarding block, which jumps to the second, which jumps to the re-test block.
pub const forwarded_relevant_retest_module = struct {
    pub const base = relevant_retest_module;
    pub const b_first_forwarder = ir.BlockId.fromIndex(6);
    pub const b_second_forwarder = ir.BlockId.fromIndex(7);
    pub const r_first = ir.EdgeRewriteId.fromIndex(0);
    pub const r_second = ir.EdgeRewriteId.fromIndex(1);

    pub const blocks = base.blocks ++ [_]ir.Block{
        .{ .id = b_first_forwarder, .function = base.f_probe, .terminator = .{ .jump = .{ .target = b_second_forwarder } }, .evidence = &.{base.proof} },
        .{ .id = b_second_forwarder, .function = base.f_probe, .terminator = .{ .jump = .{ .target = base.b_retest } }, .evidence = &.{base.proof} },
    };

    pub const functions = [_]ir.Function{
        base.functions[0],
        .{ .id = base.f_probe, .name_hint = "probe", .parameters = &.{ base.v_x, base.v_y }, .blocks = &.{ base.b_entry, base.b_retest, base.b_outer, base.b_again, base.b_never, b_first_forwarder, b_second_forwarder }, .entry_block = base.b_entry, .evidence = &.{base.proof} },
    };

    pub const edge_rewrites = [_]ir.CfgEdgeRewrite{
        .{ .id = r_first, .source = base.b_entry, .kind = .branch_then, .from = .{ .target = b_first_forwarder }, .to = .{ .target = b_second_forwarder }, .rule = .forwarding_jump },
        .{ .id = r_second, .source = base.b_entry, .kind = .branch_then, .from = .{ .target = b_second_forwarder }, .to = .{ .target = base.b_retest }, .rule = .forwarding_jump },
    };

    pub const evidence = [_]ir.Evidence{.{
        .id = base.proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:forwarded-relevant-retest-module",
    }};

    pub const program: ir.Program = .{
        .program_id = "forwarded-relevant-retest-module",
        .entry_function = base.f_chunk,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &base.instructions,
        .values = &base.values,
        .evidence = &evidence,
        .edge_rewrites = &edge_rewrites,
    };
};

/// The same re-test over a boolean parameter `m`, beside two integer parameters `x` and `y`: the entry
/// branches on `m` to the re-test block or to the block that returns "outer", and the re-test block branches
/// on `m` again.
pub const leaf_retest_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_chunk = ir.FunctionId.fromIndex(0);
    pub const f_probe = ir.FunctionId.fromIndex(1);
    pub const b_chunk = ir.BlockId.fromIndex(0);
    pub const b_entry = ir.BlockId.fromIndex(1);
    pub const b_retest = ir.BlockId.fromIndex(2);
    pub const b_outer = ir.BlockId.fromIndex(3);
    pub const b_again = ir.BlockId.fromIndex(4);
    pub const b_never = ir.BlockId.fromIndex(5);
    pub const i_export = ir.InstructionId.fromIndex(0);
    pub const i_outer = ir.InstructionId.fromIndex(1);
    pub const i_again = ir.InstructionId.fromIndex(2);
    pub const i_never = ir.InstructionId.fromIndex(3);
    pub const v_condition = ir.ValueId.fromIndex(0);
    pub const v_x = ir.ValueId.fromIndex(1);
    pub const v_y = ir.ValueId.fromIndex(2);
    pub const v_export = ir.ValueId.fromIndex(3);
    pub const v_outer = ir.ValueId.fromIndex(4);
    pub const v_again = ir.ValueId.fromIndex(5);
    pub const v_never = ir.ValueId.fromIndex(6);

    pub const values = [_]ir.Value{
        .{ .id = v_condition, .function = f_probe, .type = .boolean, .name_hint = "m", .origin = .{ .parameter = 0 } },
        .{ .id = v_x, .function = f_probe, .type = .integer, .name_hint = "x", .origin = .{ .parameter = 1 } },
        .{ .id = v_y, .function = f_probe, .type = .integer, .name_hint = "y", .origin = .{ .parameter = 2 } },
        .{ .id = v_export, .function = f_chunk, .type = .function, .name_hint = "probe", .origin = .{ .instruction_result = .{ .instruction = i_export, .index = 0 } } },
        .{ .id = v_outer, .function = f_probe, .type = .string, .name_hint = "outer_result", .origin = .{ .instruction_result = .{ .instruction = i_outer, .index = 0 } } },
        .{ .id = v_again, .function = f_probe, .type = .string, .name_hint = "again_result", .origin = .{ .instruction_result = .{ .instruction = i_again, .index = 0 } } },
        .{ .id = v_never, .function = f_probe, .type = .string, .name_hint = "never_result", .origin = .{ .instruction_result = .{ .instruction = i_never, .index = 0 } } },
    };

    pub const instructions = [_]ir.Instruction{
        .{ .id = i_export, .block = b_chunk, .operation = .{ .function_ref = f_probe }, .results = &.{v_export}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_outer, .block = b_outer, .operation = .{ .constant = .{ .string = "outer" } }, .results = &.{v_outer}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_again, .block = b_again, .operation = .{ .constant = .{ .string = "again" } }, .results = &.{v_again}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_never, .block = b_never, .operation = .{ .constant = .{ .string = "never" } }, .results = &.{v_never}, .effects = .pure, .evidence = &.{proof} },
    };

    pub const blocks = [_]ir.Block{
        .{ .id = b_chunk, .function = f_chunk, .instructions = &.{i_export}, .terminator = .{ .return_values = &.{v_export} }, .evidence = &.{proof} },
        .{ .id = b_entry, .function = f_probe, .terminator = .{ .branch = .{
            .condition = v_condition,
            .then_edge = .{ .target = b_retest },
            .else_edge = .{ .target = b_outer },
        } }, .evidence = &.{proof} },
        .{ .id = b_retest, .function = f_probe, .terminator = .{ .branch = .{
            .condition = v_condition,
            .then_edge = .{ .target = b_again },
            .else_edge = .{ .target = b_never },
        } }, .evidence = &.{proof} },
        .{ .id = b_outer, .function = f_probe, .instructions = &.{i_outer}, .terminator = .{ .return_values = &.{v_outer} }, .evidence = &.{proof} },
        .{ .id = b_again, .function = f_probe, .instructions = &.{i_again}, .terminator = .{ .return_values = &.{v_again} }, .evidence = &.{proof} },
        .{ .id = b_never, .function = f_probe, .instructions = &.{i_never}, .terminator = .{ .return_values = &.{v_never} }, .evidence = &.{proof} },
    };

    pub const functions = [_]ir.Function{
        .{ .id = f_chunk, .name_hint = "chunk", .blocks = &.{b_chunk}, .entry_block = b_chunk, .evidence = &.{proof} },
        .{ .id = f_probe, .name_hint = "probe", .parameters = &.{ v_condition, v_x, v_y }, .blocks = &.{ b_entry, b_retest, b_outer, b_again, b_never }, .entry_block = b_entry, .evidence = &.{proof} },
    };

    pub const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:leaf-retest-module",
    }};

    pub const program: ir.Program = .{
        .program_id = "leaf-retest-module",
        .entry_function = f_chunk,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };
};

/// The terms of the integer fact `x % y == 1` under floor division, ids `first` to `first + 5`: `x`, `y`,
/// `y` being nonzero (the guard the remainder is defined by), the remainder, the literal 1 and the fact.
pub fn uncoveredFactTerms(first: usize, x: ir.ValueId, y: ir.ValueId) [6]ir.SolverTerm {
    const term = ir.SolverTermId.fromIndex;
    return .{
        .{ .id = term(first), .sort = .{ .kind = .integer }, .operation = .{ .value = x } },
        .{ .id = term(first + 1), .sort = .{ .kind = .integer }, .operation = .{ .value = y } },
        .{ .id = term(first + 2), .sort = .{ .kind = .boolean }, .operation = .{ .is_nonzero = term(first + 1) } },
        .{ .id = term(first + 3), .sort = .{ .kind = .integer }, .operation = .{ .remainder = .{
            .mode = .integer_floor,
            .left = term(first),
            .right = term(first + 1),
            .defined_by = term(first + 2),
        } } },
        .{ .id = term(first + 4), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "1" } },
        .{ .id = term(first + 5), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .equal, .left = term(first + 3), .right = term(first + 4) } } },
    };
}

/// The terms of the integer fact `y < 100` over the existing term `y_term`: the literal 100 at `first` and
/// the fact at `first + 1`.
pub fn irrelevantFactTerms(first: usize, y_term: ir.SolverTermId) [2]ir.SolverTerm {
    const term = ir.SolverTermId.fromIndex;
    return .{
        .{ .id = term(first), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "100" } },
        .{ .id = term(first + 1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{ .operator = .less, .left = y_term, .right = term(first) } } },
    };
}

pub const immutable_closure_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_entry = ir.FunctionId.fromIndex(0);
    pub const f_factory = ir.FunctionId.fromIndex(1);
    pub const f_adder = ir.FunctionId.fromIndex(2);
    pub const b_entry = ir.BlockId.fromIndex(0);
    pub const b_factory = ir.BlockId.fromIndex(1);
    pub const b_adder = ir.BlockId.fromIndex(2);
    pub const i_export = ir.InstructionId.fromIndex(0);
    pub const i_make_adder = ir.InstructionId.fromIndex(1);
    pub const i_add = ir.InstructionId.fromIndex(2);
    pub const v_export = ir.ValueId.fromIndex(0);
    pub const v_base = ir.ValueId.fromIndex(1);
    pub const v_adder = ir.ValueId.fromIndex(2);
    pub const v_captured_base = ir.ValueId.fromIndex(3);
    pub const v_delta = ir.ValueId.fromIndex(4);
    pub const v_sum = ir.ValueId.fromIndex(5);
    pub const c_base = ir.CaptureId.fromIndex(0);

    pub const values = [_]ir.Value{
        .{ .id = v_export, .function = f_entry, .type = .function, .name_hint = "factory", .origin = .{ .instruction_result = .{ .instruction = i_export, .index = 0 } } },
        .{ .id = v_base, .function = f_factory, .type = .integer, .name_hint = "base", .origin = .{ .parameter = 0 } },
        .{ .id = v_adder, .function = f_factory, .type = .function, .name_hint = "adder", .origin = .{ .instruction_result = .{ .instruction = i_make_adder, .index = 0 } } },
        .{ .id = v_captured_base, .function = f_adder, .type = .integer, .name_hint = "captured_base", .origin = .{ .capture = c_base } },
        .{ .id = v_delta, .function = f_adder, .type = .integer, .name_hint = "delta", .origin = .{ .parameter = 0 } },
        .{ .id = v_sum, .function = f_adder, .type = .integer, .name_hint = "sum", .origin = .{ .instruction_result = .{ .instruction = i_add, .index = 0 } } },
    };

    pub const captures = [_]ir.Capture{.{
        .id = c_base,
        .function = f_adder,
        .kind = .{ .immutable_value = v_captured_base },
        .evidence = &.{proof},
    }};

    pub const instructions = [_]ir.Instruction{
        .{ .id = i_export, .block = b_entry, .operation = .{ .function_ref = f_factory }, .results = &.{v_export}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_make_adder, .block = b_factory, .operation = .{ .make_closure = .{
            .function = f_adder,
            .bindings = &.{.{ .value = v_base }},
        } }, .results = &.{v_adder}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_add, .block = b_adder, .operation = .{ .binary = .{
            .operator = .add,
            .left = v_captured_base,
            .right = v_delta,
        } }, .results = &.{v_sum}, .effects = .pure, .evidence = &.{proof} },
    };

    pub const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f_entry, .instructions = &.{i_export}, .terminator = .{ .return_values = &.{v_export} }, .evidence = &.{proof} },
        .{ .id = b_factory, .function = f_factory, .instructions = &.{i_make_adder}, .terminator = .{ .return_values = &.{v_adder} }, .evidence = &.{proof} },
        .{ .id = b_adder, .function = f_adder, .instructions = &.{i_add}, .terminator = .{ .return_values = &.{v_sum} }, .evidence = &.{proof} },
    };

    pub const functions = [_]ir.Function{
        .{ .id = f_entry, .name_hint = "chunk", .blocks = &.{b_entry}, .entry_block = b_entry, .evidence = &.{proof} },
        .{ .id = f_factory, .name_hint = "make_adder", .parameters = &.{v_base}, .blocks = &.{b_factory}, .entry_block = b_factory, .evidence = &.{proof} },
        .{ .id = f_adder, .name_hint = "adder", .lexical_parent = f_factory, .parameters = &.{v_delta}, .captures = &.{c_base}, .blocks = &.{b_adder}, .entry_block = b_adder, .evidence = &.{proof} },
    };

    pub const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-immutable-closure-module",
    }};

    pub const program: ir.Program = .{
        .program_id = "generic-immutable-closure-module",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .captures = &captures,
        .evidence = &evidence,
    };
};

pub const shared_place_closure_module = struct {
    pub const proof = ir.EvidenceId.fromIndex(0);
    pub const f_entry = ir.FunctionId.fromIndex(0);
    pub const f_factory = ir.FunctionId.fromIndex(1);
    pub const f_counter = ir.FunctionId.fromIndex(2);
    pub const b_entry = ir.BlockId.fromIndex(0);
    pub const b_factory = ir.BlockId.fromIndex(1);
    pub const b_counter = ir.BlockId.fromIndex(2);
    pub const i_export = ir.InstructionId.fromIndex(0);
    pub const i_initialize = ir.InstructionId.fromIndex(1);
    pub const i_make_counter = ir.InstructionId.fromIndex(2);
    pub const i_read = ir.InstructionId.fromIndex(3);
    pub const i_add = ir.InstructionId.fromIndex(4);
    pub const i_write = ir.InstructionId.fromIndex(5);
    pub const v_export = ir.ValueId.fromIndex(0);
    pub const v_start = ir.ValueId.fromIndex(1);
    pub const v_counter = ir.ValueId.fromIndex(2);
    pub const v_delta = ir.ValueId.fromIndex(3);
    pub const v_current = ir.ValueId.fromIndex(4);
    pub const v_next = ir.ValueId.fromIndex(5);
    pub const p_state = ir.PlaceId.fromIndex(0);
    pub const p_captured_state = ir.PlaceId.fromIndex(1);
    pub const c_state = ir.CaptureId.fromIndex(0);

    pub const values = [_]ir.Value{
        .{ .id = v_export, .function = f_entry, .type = .function, .name_hint = "factory", .origin = .{ .instruction_result = .{ .instruction = i_export, .index = 0 } } },
        .{ .id = v_start, .function = f_factory, .type = .integer, .name_hint = "start", .origin = .{ .parameter = 0 } },
        .{ .id = v_counter, .function = f_factory, .type = .function, .name_hint = "counter", .origin = .{ .instruction_result = .{ .instruction = i_make_counter, .index = 0 } } },
        .{ .id = v_delta, .function = f_counter, .type = .integer, .name_hint = "delta", .origin = .{ .parameter = 0 } },
        .{ .id = v_current, .function = f_counter, .type = .integer, .name_hint = "current", .origin = .{ .instruction_result = .{ .instruction = i_read, .index = 0 } } },
        .{ .id = v_next, .function = f_counter, .type = .integer, .name_hint = "next", .origin = .{ .instruction_result = .{ .instruction = i_add, .index = 0 } } },
    };

    pub const places = [_]ir.Place{
        .{ .id = p_state, .function = f_factory, .type = .integer, .name_hint = "state", .origin = .{ .local = 0 }, .evidence = &.{proof} },
        .{ .id = p_captured_state, .function = f_counter, .type = .integer, .name_hint = "captured_state", .origin = .{ .capture = c_state }, .evidence = &.{proof} },
    };

    pub const captures = [_]ir.Capture{.{
        .id = c_state,
        .function = f_counter,
        .kind = .{ .shared_place = p_captured_state },
        .evidence = &.{proof},
    }};

    pub const instructions = [_]ir.Instruction{
        .{ .id = i_export, .block = b_entry, .operation = .{ .function_ref = f_factory }, .results = &.{v_export}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_initialize, .block = b_factory, .operation = .{ .place_write = .{ .place = p_state, .value = v_start } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
        .{ .id = i_make_counter, .block = b_factory, .operation = .{ .make_closure = .{
            .function = f_counter,
            .bindings = &.{.{ .place = p_state }},
        } }, .results = &.{v_counter}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_read, .block = b_counter, .operation = .{ .place_read = p_captured_state }, .results = &.{v_current}, .effects = .place_read, .evidence = &.{proof} },
        .{ .id = i_add, .block = b_counter, .operation = .{ .binary = .{
            .operator = .add,
            .left = v_current,
            .right = v_delta,
        } }, .results = &.{v_next}, .effects = .pure, .evidence = &.{proof} },
        .{ .id = i_write, .block = b_counter, .operation = .{ .place_write = .{ .place = p_captured_state, .value = v_next } }, .results = &.{}, .effects = .place_write, .evidence = &.{proof} },
    };

    pub const blocks = [_]ir.Block{
        .{ .id = b_entry, .function = f_entry, .instructions = &.{i_export}, .terminator = .{ .return_values = &.{v_export} }, .evidence = &.{proof} },
        .{ .id = b_factory, .function = f_factory, .instructions = &.{ i_initialize, i_make_counter }, .terminator = .{ .return_values = &.{v_counter} }, .evidence = &.{proof} },
        .{ .id = b_counter, .function = f_counter, .instructions = &.{ i_read, i_add, i_write }, .terminator = .{ .return_values = &.{v_next} }, .evidence = &.{proof} },
    };

    pub const functions = [_]ir.Function{
        .{ .id = f_entry, .name_hint = "chunk", .blocks = &.{b_entry}, .entry_block = b_entry, .evidence = &.{proof} },
        .{ .id = f_factory, .name_hint = "make_counter", .parameters = &.{v_start}, .local_places = &.{p_state}, .blocks = &.{b_factory}, .entry_block = b_factory, .evidence = &.{proof} },
        .{ .id = f_counter, .name_hint = "counter", .lexical_parent = f_factory, .parameters = &.{v_delta}, .captures = &.{c_state}, .blocks = &.{b_counter}, .entry_block = b_counter, .evidence = &.{proof} },
    };

    pub const evidence = [_]ir.Evidence{.{
        .id = proof,
        .kind = .dynamic_fixture,
        .locator = "fixture:generic-shared-place-closure-module",
    }};

    pub const program: ir.Program = .{
        .program_id = "generic-shared-place-closure-module",
        .entry_function = f_entry,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
        .captures = &captures,
        .evidence = &evidence,
    };
};
