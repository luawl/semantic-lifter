const std = @import("std");
const cfg = @import("cfg.zig");
const cfg_edge = @import("cfg_edge.zig");
const ir = @import("ir.zig");
const readable_scope = @import("readable_scope.zig");
const solver_equivalence = @import("solver_equivalence.zig");
const solver_promotion = @import("solver_promotion.zig");

const edge_kinds = [_]ir.CfgEdgeKind{ .jump, .branch_then, .branch_else };

pub fn messageMayIncludeSourceLocation(kind: ir.TypeKind) bool {
    return switch (kind) {
        .nil_value, .boolean, .table, .function, .thread, .userdata => false,
        .dynamic, .integer, .number, .string, .tuple => true,
    };
}

pub fn levelIsNumeric(kind: ir.TypeKind) bool {
    return kind == .integer or kind == .number;
}

pub fn deriveRequirements(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    terms: *std.ArrayList(ir.SolverTerm),
    queries: *std.ArrayList(ir.SolverQuery),
    obligations: *std.ArrayList(ir.Obligation),
) !void {
    const analyses = try allocator.alloc(?cfg.Analysis, program.functions.len);
    defer {
        for (analyses) |*maybe_analysis| if (maybe_analysis.*) |*analysis| analysis.deinit();
        allocator.free(analyses);
    }
    @memset(analyses, null);
    for (program.functions) |function| {
        if (function.id.index() >= analyses.len) continue;
        analyses[function.id.index()] = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
            error.InvalidCfg => continue,
            error.OutOfMemory => return error.OutOfMemory,
        };
    }

    for (program.blocks) |block| {
        if (block.function.index() >= analyses.len) continue;
        const analysis = if (analyses[block.function.index()]) |*value| value else continue;
        if (!scope.block(block.id) or !analysis.isReachable(block.id)) continue;
        const throw_error = switch (block.terminator) {
            .throw_error => |value| value,
            else => continue,
        };
        const level = throw_error.dynamic_level orelse continue;
        if (throw_error.value.index() >= program.values.len or level.index() >= program.values.len) continue;
        const requirement_value = requirementValue(program, scope, analysis, block, level) orelse continue;
        if (!messageMayIncludeSourceLocation(program.values[throw_error.value.index()].type.kind) or
            !levelIsNumeric(program.values[level.index()].type.kind))
        {
            continue;
        }

        var working = program.*;
        working.solver_terms = terms.items;
        const definition = try solver_promotion.ensureDefinition(allocator, &working, terms, requirement_value) orelse continue;
        working.solver_terms = terms.items;
        const sort = terms.items[definition.index()].sort;
        const zero_operation: ir.SolverTermOperation = switch (sort.kind) {
            .integer => .{ .integer_literal = "0" },
            .real => .{ .real_literal = .{ .numerator = "0", .denominator = "1" } },
            .bit_vector => .{ .bit_vector_literal = .{ .value = "0", .bit_width = sort.bit_width } },
            else => continue,
        };
        const zero = try solver_promotion.ensureCanonicalTerm(allocator, terms, sort, zero_operation);
        const predicate = try solver_promotion.ensureCanonicalTerm(allocator, terms, .{ .kind = .boolean }, .{ .binary = .{
            .operator = .less_equal,
            .left = definition,
            .right = zero,
        } });
        const query_id = try ensureQuery(allocator, queries, predicate);
        if (hasExactRequirement(obligations.items, block.id, query_id, predicate)) continue;

        try obligations.append(allocator, .{
            .id = ir.ObligationId.fromIndex(obligations.items.len),
            .kind = .numeric_domain,
            .subject = .{ .block = block.id },
            .status = .open,
            .blocks_profile = .readable_luau,
            .detail = "prove dynamic error level is nonpositive",
            .evidence = block.evidence,
            .requirement = .{ .kind = .prove_true, .predicate = predicate },
            .query = query_id,
        });
    }
}

pub fn hasNonpositiveRequirement(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    block_id: ir.BlockId,
    level: ir.ValueId,
) bool {
    const requirement_value = requirementValueForValidation(program, scope, block_id, level) orelse return false;
    for (program.obligations) |obligation| {
        if (obligation.kind != .numeric_domain or
            obligation.blocks_profile != .readable_luau or
            obligation.subject != .block or
            obligation.subject.block != block_id)
        {
            continue;
        }
        const requirement = obligation.requirement orelse continue;
        const query_id = obligation.query orelse continue;
        if (query_id.index() >= program.queries.len) continue;
        const query = program.queries[query_id.index()];
        if (query.id != query_id or query.kind != .prove_true or
            query.assumptions.len != 0 or query.path_rewrites.len != 0 or
            requirement.kind != query.kind or requirement.predicate != query.goal or
            !isNonpositivePredicate(program, query.goal, requirement_value))
        {
            continue;
        }
        return true;
    }
    return false;
}

fn requirementValue(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    analysis: *const cfg.Analysis,
    block: ir.Block,
    level: ir.ValueId,
) ?ir.ValueId {
    if (level.index() >= program.values.len) return null;
    const value = program.values[level.index()];
    if (value.id != level or value.function != block.function) return null;
    return switch (value.origin) {
        .instruction_result => blk: {
            const definition_block = instructionDefinitionBlock(program, level, block.function) orelse break :blk null;
            break :blk if (analysis.dominates(definition_block, block.id)) level else null;
        },
        .block_parameter => |origin| blk: {
            const incoming = commonReachableIncomingValue(program, scope, block, level, origin) orelse break :blk null;
            if (!incomingDefinitionsDominate(program, analysis, block, origin.index, incoming)) break :blk null;
            break :blk incoming;
        },
        .parameter, .capture => null,
    };
}

fn requirementValueForValidation(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    block_id: ir.BlockId,
    level: ir.ValueId,
) ?ir.ValueId {
    if (block_id.index() >= program.blocks.len or level.index() >= program.values.len) return null;
    const block = program.blocks[block_id.index()];
    const value = program.values[level.index()];
    if (block.id != block_id or value.id != level or value.function != block.function) return null;
    return switch (value.origin) {
        .instruction_result => if (instructionDefinitionBlock(program, level, block.function) != null) level else null,
        .block_parameter => |origin| commonReachableIncomingValue(program, scope, block, level, origin),
        .parameter, .capture => null,
    };
}

fn commonReachableIncomingValue(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    target: ir.Block,
    parameter: ir.ValueId,
    origin: @FieldType(ir.ValueOrigin, "block_parameter"),
) ?ir.ValueId {
    const parameter_index: usize = @intCast(origin.index);
    if (origin.block != target.id or parameter_index >= target.parameters.len or
        target.parameters[parameter_index] != parameter)
    {
        return null;
    }

    var common: ?ir.ValueId = null;
    var incoming_count: usize = 0;
    for (program.blocks) |source| {
        if (source.function != target.function or !scope.block(source.id)) continue;
        for (edge_kinds) |kind| {
            const edge = cfg_edge.value(program, .{ .source = source.id, .kind = kind, .target = target.id }) orelse continue;
            if (edge.target != target.id) continue;
            if (edge.arguments.len != target.parameters.len) return null;
            const argument = edge.arguments[parameter_index];
            if (argument.index() >= program.values.len) return null;
            const argument_value = program.values[argument.index()];
            if (argument_value.id != argument or argument_value.function != target.function) return null;
            if (common) |existing| {
                if (existing != argument) return null;
            } else {
                common = argument;
            }
            incoming_count += 1;
        }
    }
    return if (incoming_count != 0) common else null;
}

fn incomingDefinitionsDominate(
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    target: ir.Block,
    parameter_index: u32,
    incoming: ir.ValueId,
) bool {
    const definition_block = instructionDefinitionBlock(program, incoming, target.function) orelse return false;
    var incoming_count: usize = 0;
    for (program.blocks) |source| {
        if (source.function != target.function or !analysis.isReachable(source.id)) continue;
        for (edge_kinds) |kind| {
            const edge = cfg_edge.value(program, .{ .source = source.id, .kind = kind, .target = target.id }) orelse continue;
            if (edge.target != target.id) continue;
            if (parameter_index >= edge.arguments.len or edge.arguments[parameter_index] != incoming or
                !analysis.dominates(definition_block, source.id))
            {
                return false;
            }
            incoming_count += 1;
        }
    }
    return incoming_count != 0 and incoming_count == analysis.predecessorCount(target.id);
}

fn instructionDefinitionBlock(
    program: *const ir.Program,
    value_id: ir.ValueId,
    function_id: ir.FunctionId,
) ?ir.BlockId {
    if (value_id.index() >= program.values.len) return null;
    const value = program.values[value_id.index()];
    if (value.id != value_id or value.function != function_id) return null;
    const origin = switch (value.origin) {
        .instruction_result => |result| result,
        else => return null,
    };
    if (origin.instruction.index() >= program.instructions.len) return null;
    const instruction = program.instructions[origin.instruction.index()];
    if (instruction.id != origin.instruction or
        origin.index >= instruction.results.len or
        instruction.results[origin.index] != value_id or
        instruction.block.index() >= program.blocks.len)
    {
        return null;
    }
    const block = program.blocks[instruction.block.index()];
    if (block.id != instruction.block or block.function != function_id) return null;
    return block.id;
}

fn ensureQuery(
    allocator: std.mem.Allocator,
    queries: *std.ArrayList(ir.SolverQuery),
    predicate: ir.SolverTermId,
) !ir.QueryId {
    for (queries.items) |query| {
        if (query.kind == .prove_true and query.goal == predicate and
            query.assumptions.len == 0 and query.path_rewrites.len == 0)
        {
            return query.id;
        }
    }
    const id = ir.QueryId.fromIndex(queries.items.len);
    try queries.append(allocator, .{ .id = id, .kind = .prove_true, .goal = predicate });
    return id;
}

fn hasExactRequirement(
    obligations: []const ir.Obligation,
    block_id: ir.BlockId,
    query_id: ir.QueryId,
    predicate: ir.SolverTermId,
) bool {
    for (obligations) |obligation| {
        if (obligation.kind != .numeric_domain or
            obligation.blocks_profile != .readable_luau or
            obligation.subject != .block or
            obligation.subject.block != block_id or
            obligation.query == null or obligation.query.? != query_id)
        {
            continue;
        }
        const requirement = obligation.requirement orelse continue;
        if (requirement.kind == .prove_true and requirement.predicate == predicate) return true;
    }
    return false;
}

fn isNonpositivePredicate(program: *const ir.Program, predicate_id: ir.SolverTermId, level: ir.ValueId) bool {
    if (predicate_id.index() >= program.solver_terms.len or level.index() >= program.values.len) return false;
    const predicate = program.solver_terms[predicate_id.index()];
    if (predicate.sort.kind != .boolean) return false;
    const comparison = switch (predicate.operation) {
        .binary => |value| value,
        else => return false,
    };
    if (comparison.operator != .less_equal or
        comparison.left.index() >= program.solver_terms.len or
        comparison.right.index() >= program.solver_terms.len)
    {
        return false;
    }
    const left = program.solver_terms[comparison.left.index()];
    const right = program.solver_terms[comparison.right.index()];
    if (!sameSort(left.sort, right.sort) or
        !solver_equivalence.termRepresentsValue(program, comparison.left, level))
    {
        return false;
    }
    return switch (left.sort.kind) {
        .integer => switch (right.operation) {
            .integer_literal => |value| std.mem.eql(u8, value, "0"),
            else => false,
        },
        .real => switch (right.operation) {
            .real_literal => |value| std.mem.eql(u8, value.numerator, "0") and
                std.mem.eql(u8, value.denominator, "1"),
            else => false,
        },
        .bit_vector => switch (right.operation) {
            .bit_vector_literal => |value| value.bit_width == left.sort.bit_width and std.mem.eql(u8, value.value, "0"),
            else => false,
        },
        else => false,
    };
}

fn sameSort(left: ir.SolverSort, right: ir.SolverSort) bool {
    return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed;
}
