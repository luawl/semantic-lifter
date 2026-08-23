const std = @import("std");
const ir = @import("ir.zig");
const proof_effect_closure = @import("proof_effect_closure.zig");
const runtime_uses = @import("runtime_uses.zig");
const solver = @import("solver.zig");
const solver_term = @import("solver_term.zig");

pub const BuildError = error{InvalidClosureInput} || std.mem.Allocator.Error;

pub const Closure = struct {
    allocator: std.mem.Allocator,
    lexical_witness: bool,
    runtime_value_witness: bool,
    combined_runtime_witness: bool,
    functions: []bool,
    terms: []bool,
    values: []bool,
    value_packs: []bool,
    places: []bool,
    captures: []bool,
    instructions: []bool,
    blocks: []bool,
    evidence: []bool,
    edge_rewrites: []bool,

    pub fn init(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        query: ir.SolverQuery,
        seed_evidence: []const ir.EvidenceId,
        model: []const ir.SolverModelBinding,
    ) BuildError!Closure {
        return initWithExternalWitness(allocator, program, query, seed_evidence, model, true);
    }

    pub fn initForObligationSubject(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        query: ir.SolverQuery,
    ) BuildError!Closure {
        return initWithExternalWitness(allocator, program, query, &.{}, &.{}, false);
    }

    fn initWithExternalWitness(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        query: ir.SolverQuery,
        seed_evidence: []const ir.EvidenceId,
        model: []const ir.SolverModelBinding,
        include_external_witness: bool,
    ) BuildError!Closure {
        const functions = try allocator.alloc(bool, program.functions.len);
        errdefer allocator.free(functions);
        @memset(functions, false);
        const terms = try allocator.alloc(bool, program.solver_terms.len);
        errdefer allocator.free(terms);
        @memset(terms, false);
        const values = try allocator.alloc(bool, program.values.len);
        errdefer allocator.free(values);
        @memset(values, false);
        const value_packs = try allocator.alloc(bool, program.value_packs.len);
        errdefer allocator.free(value_packs);
        @memset(value_packs, false);
        const places = try allocator.alloc(bool, program.places.len);
        errdefer allocator.free(places);
        @memset(places, false);
        const captures = try allocator.alloc(bool, program.captures.len);
        errdefer allocator.free(captures);
        @memset(captures, false);
        const instructions = try allocator.alloc(bool, program.instructions.len);
        errdefer allocator.free(instructions);
        @memset(instructions, false);
        const blocks = try allocator.alloc(bool, program.blocks.len);
        errdefer allocator.free(blocks);
        @memset(blocks, false);
        const evidence = try allocator.alloc(bool, program.evidence.len);
        errdefer allocator.free(evidence);
        @memset(evidence, false);
        const edge_rewrites = try allocator.alloc(bool, program.edge_rewrites.len);
        errdefer allocator.free(edge_rewrites);
        @memset(edge_rewrites, false);

        var query_terms = solver_term.QueryTermSet.init(allocator, program, query) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.InvalidQueryReference, error.InvalidTermGraph => return error.InvalidClosureInput,
        };
        defer query_terms.deinit();

        try markTerm(terms, query.goal);
        try markEvidence(evidence, seed_evidence);
        for (query.assumptions) |constraint_id| {
            if (constraint_id.index() >= program.constraints.len) return error.InvalidClosureInput;
            const constraint = program.constraints[constraint_id.index()];
            try markTerm(terms, constraint.predicate);
            try markEvidence(evidence, constraint.evidence);
            switch (constraint.scope) {
                .edge => |edge| {
                    try markBlock(blocks, edge.target);
                },
                .explicit_only, .program, .function, .block => {},
            }
        }
        for (model) |binding| {
            if (!query_terms.contains(binding.term)) return error.InvalidClosureInput;
            try markTerm(terms, binding.term);
        }
        for (query.path_rewrites) |rewrite_id| {
            try markEdgeRewriteDependencies(
                program,
                rewrite_id,
                edge_rewrites,
                blocks,
                instructions,
                values,
                evidence,
            );
            const rewrite = program.edge_rewrites[rewrite_id.index()];
            if (rewrite.rule == .clone_fold) {
                const group = rewrite.node_split_group orelse return error.InvalidClosureInput;
                if (group.index() >= rewrite_id.index() or group.index() >= program.edge_rewrites.len) {
                    return error.InvalidClosureInput;
                }
                const root_id = ir.EdgeRewriteId.fromIndex(group.index());
                const root = program.edge_rewrites[group.index()];
                if (root.id != root_id or root.rule != .node_split or root.node_split_group != group) {
                    return error.InvalidClosureInput;
                }
                try markEdgeRewriteDependencies(
                    program,
                    root_id,
                    edge_rewrites,
                    blocks,
                    instructions,
                    values,
                    evidence,
                );
            }
        }

        var has_instruction_semantics = false;
        var term_offset: usize = program.solver_terms.len;
        while (term_offset != 0) {
            term_offset -= 1;
            if (!terms[term_offset]) continue;
            var dependencies = solver_term.dependencies(program.solver_terms[term_offset].operation);
            while (dependencies.next()) |operand| {
                if (operand.index() >= term_offset) return error.InvalidClosureInput;
                try markTerm(terms, operand);
            }
            switch (program.solver_terms[term_offset].operation) {
                .value => |value_id| {
                    if (value_id.index() >= values.len) return error.InvalidClosureInput;
                    values[value_id.index()] = true;
                },
                .value_definition => |definition| {
                    if (definition.value.index() >= values.len) return error.InvalidClosureInput;
                    values[definition.value.index()] = true;
                    const value = program.values[definition.value.index()];
                    const origin = switch (value.origin) {
                        .instruction_result => |origin| origin,
                        else => return error.InvalidClosureInput,
                    };
                    if (origin.instruction.index() >= instructions.len) return error.InvalidClosureInput;
                    instructions[origin.instruction.index()] = true;
                },
                .semantic_atom => |atom| {
                    const instruction_id = semanticAtomInstruction(atom);
                    try markInstructionSemanticDependencies(
                        program,
                        instruction_id,
                        values,
                        value_packs,
                        places,
                        instructions,
                    );
                    has_instruction_semantics = true;
                },
                else => {},
            }
        }

        const visited_values = try allocator.alloc(bool, program.values.len);
        defer allocator.free(visited_values);
        @memset(visited_values, false);
        const stack = try allocator.alloc(ir.ValueId, program.values.len);
        defer allocator.free(stack);
        var stack_len: usize = 0;
        for (values, 0..) |needed, value_index| if (needed) {
            stack[stack_len] = ir.ValueId.fromIndex(value_index);
            stack_len += 1;
        };
        while (stack_len != 0) {
            stack_len -= 1;
            const value_id = stack[stack_len];
            if (visited_values[value_id.index()]) continue;
            visited_values[value_id.index()] = true;
            const source = solver.normalizedValueSource(program, value_id) orelse continue;
            const instruction_id = switch (source) {
                .constant => |constant| constant.instruction,
                .copy => |copy| copy.instruction,
                .unary => |unary| unary.instruction,
                .binary => |binary| binary.instruction,
            };
            if (instruction_id.index() >= instructions.len) return error.InvalidClosureInput;
            instructions[instruction_id.index()] = true;
            switch (source) {
                .constant => {},
                .copy => |copy| {
                    if (copy.source.index() >= values.len) return error.InvalidClosureInput;
                    if (!values[copy.source.index()]) {
                        values[copy.source.index()] = true;
                        stack[stack_len] = copy.source;
                        stack_len += 1;
                    }
                },
                .unary => |unary| {
                    if (unary.operand.index() >= values.len) return error.InvalidClosureInput;
                    if (!values[unary.operand.index()]) {
                        values[unary.operand.index()] = true;
                        stack[stack_len] = unary.operand;
                        stack_len += 1;
                    }
                },
                .binary => |binary| {
                    if (binary.left.index() >= values.len or binary.right.index() >= values.len) return error.InvalidClosureInput;
                    if (!values[binary.left.index()]) {
                        values[binary.left.index()] = true;
                        stack[stack_len] = binary.left;
                        stack_len += 1;
                    }
                    if (!values[binary.right.index()]) {
                        values[binary.right.index()] = true;
                        stack[stack_len] = binary.right;
                        stack_len += 1;
                    }
                },
            }
        }

        for (blocks, 0..) |needed, block_index| {
            if (needed) try markValues(values, program.blocks[block_index].parameters);
        }

        const mandatory_external_witness = include_external_witness and requiresExternalWitness(program);
        const initial_runtime_effect_witness = needsRuntimeValueWitness(program, terms, values);
        if (mandatory_external_witness or initial_runtime_effect_witness or has_instruction_semantics) {
            try expandRuntimeValueDependencies(
                allocator,
                program,
                functions,
                values,
                value_packs,
                places,
                captures,
                instructions,
                blocks,
                evidence,
                mandatory_external_witness,
            );
        }
        var lexical_witness = mandatory_external_witness or hasMarked(captures);
        var capture_free_runtime_effect_witness = !lexical_witness and needsRuntimeValueWitness(program, terms, values);
        var runtime_value_witness = !lexical_witness and
            (capture_free_runtime_effect_witness or needsRuntimeIdentityWitness(value_packs, places));
        var combined_runtime_witness = lexical_witness and try needsRuntimeEffectWitness(program, terms, values);
        if (capture_free_runtime_effect_witness or combined_runtime_witness) {
            while (true) {
                const marked_before = dependencyMarkCount(functions, values, value_packs, places, captures, instructions, blocks);
                try proof_effect_closure.expand(
                    allocator,
                    program,
                    functions,
                    values,
                    instructions,
                    blocks,
                );
                try expandRuntimeValueDependencies(
                    allocator,
                    program,
                    functions,
                    values,
                    value_packs,
                    places,
                    captures,
                    instructions,
                    blocks,
                    evidence,
                    mandatory_external_witness,
                );
                if (dependencyMarkCount(functions, values, value_packs, places, captures, instructions, blocks) == marked_before) break;
            }
            lexical_witness = mandatory_external_witness or hasMarked(captures);
            capture_free_runtime_effect_witness = !lexical_witness and needsRuntimeValueWitness(program, terms, values);
            runtime_value_witness = !lexical_witness and
                (capture_free_runtime_effect_witness or needsRuntimeIdentityWitness(value_packs, places));
            combined_runtime_witness = lexical_witness and try needsRuntimeEffectWitness(program, terms, values);
        }

        for (instructions, 0..) |needed, instruction_index| {
            if (needed) {
                try markEvidence(evidence, program.instructions[instruction_index].evidence);
            }
        }
        for (blocks, 0..) |needed, block_index| {
            if (needed) {
                try markEvidence(evidence, program.blocks[block_index].evidence);
            }
        }
        for (functions, 0..) |needed, function_index| {
            if (needed) try markEvidence(evidence, program.functions[function_index].evidence);
        }
        for (value_packs, 0..) |needed, pack_index| {
            if (needed) try markEvidence(evidence, program.value_packs[pack_index].evidence);
        }
        for (places, 0..) |needed, place_index| {
            if (needed) try markEvidence(evidence, program.places[place_index].evidence);
        }
        for (captures, 0..) |needed, capture_index| {
            if (needed) try markEvidence(evidence, program.captures[capture_index].evidence);
        }
        return .{
            .allocator = allocator,
            .lexical_witness = lexical_witness,
            .runtime_value_witness = runtime_value_witness,
            .combined_runtime_witness = combined_runtime_witness,
            .functions = functions,
            .terms = terms,
            .values = values,
            .value_packs = value_packs,
            .places = places,
            .captures = captures,
            .instructions = instructions,
            .blocks = blocks,
            .evidence = evidence,
            .edge_rewrites = edge_rewrites,
        };
    }

    pub fn coversObligationSubject(self: *const Closure, program: *const ir.Program, subject: ir.ObligationSubject) bool {
        return switch (subject) {
            .program => true,
            .function => |function_id| self.usesFunction(program, function_id),
            .block => |block_id| self.usesBlock(program, block_id),
            .instruction => |instruction_id| isMarked(self.instructions, instruction_id),
            .value => |value_id| isMarked(self.values, value_id),
            .value_pack => |pack_id| isMarked(self.value_packs, pack_id),
            .place => |place_id| isMarked(self.places, place_id),
            .capture => |capture_id| isMarked(self.captures, capture_id),
            .external_binding => |binding_id| self.usesExternalBinding(program, binding_id),
            .control_branch => true,
        };
    }

    pub fn coversBlockThroughIncomingEdge(
        self: *const Closure,
        program: *const ir.Program,
        block_id: ir.BlockId,
        edge: ir.Edge,
    ) bool {
        if (block_id.index() >= program.blocks.len) return false;
        const block = program.blocks[block_id.index()];
        if (block.id != block_id) return false;
        for (block.parameters, 0..) |parameter, parameter_index| {
            if (!terminatorUsesValue(block.terminator, parameter)) continue;
            if (markedIncomingArgument(self.values, block, edge, parameter_index)) return true;
        }
        return false;
    }

    fn usesFunction(self: *const Closure, program: *const ir.Program, function_id: ir.FunctionId) bool {
        if (function_id.index() >= program.functions.len) return false;
        for (self.values, program.values) |needed, value| if (needed and value.function == function_id) return true;
        for (self.blocks, program.blocks) |needed, block| if (needed and block.function == function_id) return true;
        for (self.instructions, program.instructions) |needed, instruction| {
            if (!needed or instruction.block.index() >= program.blocks.len) continue;
            const block = program.blocks[instruction.block.index()];
            if (block.id == instruction.block and block.function == function_id) return true;
        }
        return false;
    }

    fn usesBlock(self: *const Closure, program: *const ir.Program, block_id: ir.BlockId) bool {
        if (block_id.index() >= program.blocks.len) return false;
        for (self.instructions, program.instructions) |needed, instruction| if (needed and instruction.block == block_id) return true;
        for (self.values, program.values) |needed, value| {
            if (!needed) continue;
            switch (value.origin) {
                .block_parameter => |origin| if (origin.block == block_id) return true,
                .instruction_result => |origin| {
                    if (origin.instruction.index() >= program.instructions.len) continue;
                    const instruction = program.instructions[origin.instruction.index()];
                    if (instruction.id == origin.instruction and instruction.block == block_id) return true;
                },
                .parameter, .capture => {},
            }
        }
        const block = program.blocks[block_id.index()];
        if (block.id != block_id) return false;
        var found = false;
        runtime_uses.visitTerminatorUses(block.terminator, SubjectUseVisitor{
            .values = self.values,
            .value_packs = self.value_packs,
            .found = &found,
        });
        if (found) return true;
        for (program.blocks) |source| switch (source.terminator) {
            .jump => |edge| if (self.coversBlockThroughIncomingEdge(program, block_id, edge)) return true,
            .branch => |branch| {
                if (self.coversBlockThroughIncomingEdge(program, block_id, branch.then_edge) or
                    self.coversBlockThroughIncomingEdge(program, block_id, branch.else_edge)) return true;
            },
            .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
        };
        return false;
    }

    fn usesExternalBinding(self: *const Closure, program: *const ir.Program, binding_id: ir.ExternalBindingId) bool {
        if (binding_id.index() >= program.external_bindings.len or program.entry_function.index() >= program.functions.len) return false;
        const entry = program.functions[program.entry_function.index()];
        for (program.entry_bindings, 0..) |candidate, index| {
            if (candidate != binding_id or index >= entry.captures.len) continue;
            return isMarked(self.captures, entry.captures[index]);
        }
        return false;
    }

    pub fn deinit(self: *Closure) void {
        self.allocator.free(self.functions);
        self.allocator.free(self.terms);
        self.allocator.free(self.values);
        self.allocator.free(self.value_packs);
        self.allocator.free(self.places);
        self.allocator.free(self.captures);
        self.allocator.free(self.instructions);
        self.allocator.free(self.blocks);
        self.allocator.free(self.evidence);
        self.allocator.free(self.edge_rewrites);
        self.* = undefined;
    }

    pub fn evidenceMatches(self: *const Closure, evidence_ids: []const ir.EvidenceId) bool {
        var evidence_offset: usize = 0;
        for (self.evidence, 0..) |needed, evidence_index| {
            if (!needed) continue;
            if (evidence_offset >= evidence_ids.len or evidence_ids[evidence_offset].index() != evidence_index) return false;
            evidence_offset += 1;
        }
        return evidence_offset == evidence_ids.len;
    }
};

const SubjectUseVisitor = struct {
    values: []const bool,
    value_packs: []const bool,
    found: *bool,

    pub fn value(self: SubjectUseVisitor, value_id: ir.ValueId) void {
        if (value_id.index() < self.values.len and self.values[value_id.index()]) self.found.* = true;
    }

    pub fn pack(self: SubjectUseVisitor, pack_id: ir.ValuePackId) void {
        if (pack_id.index() < self.value_packs.len and self.value_packs[pack_id.index()]) self.found.* = true;
    }

    pub fn place(_: SubjectUseVisitor, _: ir.PlaceId) void {}
};

const ExactValueUseVisitor = struct {
    expected: ir.ValueId,
    found: *bool,

    pub fn value(self: ExactValueUseVisitor, value_id: ir.ValueId) void {
        if (value_id == self.expected) self.found.* = true;
    }

    pub fn pack(_: ExactValueUseVisitor, _: ir.ValuePackId) void {}

    pub fn place(_: ExactValueUseVisitor, _: ir.PlaceId) void {}
};

fn terminatorUsesValue(terminator: ir.Terminator, value_id: ir.ValueId) bool {
    var found = false;
    runtime_uses.visitTerminatorUses(terminator, ExactValueUseVisitor{ .expected = value_id, .found = &found });
    return found;
}

fn markedIncomingArgument(values: []const bool, target: ir.Block, edge: ir.Edge, parameter_index: usize) bool {
    if (edge.target != target.id or edge.arguments.len != target.parameters.len or parameter_index >= edge.arguments.len) return false;
    const argument = edge.arguments[parameter_index];
    return argument.index() < values.len and values[argument.index()];
}

test "block coverage maps incoming values to the exact terminator parameter" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source_id = ir.BlockId.fromIndex(0);
    const target_id = ir.BlockId.fromIndex(1);
    const unrelated = ir.ValueId.fromIndex(0);
    const level_source = ir.ValueId.fromIndex(1);
    const message = ir.ValueId.fromIndex(2);
    const unused_parameter = ir.ValueId.fromIndex(3);
    const level_parameter = ir.ValueId.fromIndex(4);
    const values = [_]ir.Value{
        .{ .id = unrelated, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = level_source, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = message, .function = function_id, .type = .string, .origin = .{ .parameter = 2 } },
        .{ .id = unused_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_id, .index = 0 } } },
        .{ .id = level_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = target_id, .index = 1 } } },
    };
    const blocks = [_]ir.Block{
        .{ .id = source_id, .function = function_id, .terminator = .{ .jump = .{
            .target = target_id,
            .arguments = &.{ unrelated, level_source },
        } } },
        .{ .id = target_id, .function = function_id, .parameters = &.{ unused_parameter, level_parameter }, .terminator = .{ .throw_error = .{
            .value = message,
            .level = 0,
            .dynamic_level = level_parameter,
        } } },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ unrelated, level_source, message },
        .blocks = &.{ source_id, target_id },
        .entry_block = source_id,
    }};
    const program: ir.Program = .{
        .program_id = "proof-closure-exact-incoming-parameter",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
    };

    var function_marks = [_]bool{false};
    var term_marks: [0]bool = .{};
    var value_marks = [_]bool{false} ** values.len;
    var pack_marks: [0]bool = .{};
    var place_marks: [0]bool = .{};
    var capture_marks: [0]bool = .{};
    var instruction_marks: [0]bool = .{};
    var block_marks = [_]bool{false} ** blocks.len;
    var evidence_marks: [0]bool = .{};
    var rewrite_marks: [0]bool = .{};
    const closure: Closure = .{
        .allocator = std.testing.allocator,
        .lexical_witness = false,
        .runtime_value_witness = false,
        .combined_runtime_witness = false,
        .functions = &function_marks,
        .terms = &term_marks,
        .values = &value_marks,
        .value_packs = &pack_marks,
        .places = &place_marks,
        .captures = &capture_marks,
        .instructions = &instruction_marks,
        .blocks = &block_marks,
        .evidence = &evidence_marks,
        .edge_rewrites = &rewrite_marks,
    };

    value_marks[unrelated.index()] = true;
    try std.testing.expect(!closure.coversObligationSubject(&program, .{ .block = target_id }));
    value_marks[unrelated.index()] = false;
    value_marks[level_source.index()] = true;
    try std.testing.expect(closure.coversObligationSubject(&program, .{ .block = target_id }));
}

test "clone fold proof closure retains its node split root" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry = ir.BlockId.fromIndex(0);
    const original = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const root_id = ir.EdgeRewriteId.fromIndex(0);
    const fold_id = ir.EdgeRewriteId.fromIndex(1);
    const group = ir.NodeSplitGroupId.fromIndex(0);
    const term_id = ir.SolverTermId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = entry, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = original, .function = function_id, .terminator = .{ .unreachable_block = {} } },
        .{ .id = clone, .function = function_id, .terminator = .{ .unreachable_block = {} } },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{ entry, original, clone },
        .entry_block = entry,
    };
    const terms = [_]ir.SolverTerm{.{
        .id = term_id,
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{
        .{
            .id = root_id,
            .source = entry,
            .kind = .branch_then,
            .from = .{ .target = original },
            .to = .{ .target = clone },
            .rule = .node_split,
            .node_split_group = group,
        },
        .{
            .id = fold_id,
            .source = entry,
            .kind = .branch_then,
            .from = .{ .target = clone },
            .to = .{ .target = original },
            .rule = .clone_fold,
            .node_split_group = group,
        },
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = term_id,
        .path_rewrites = &.{fold_id},
    };
    const program = ir.Program{
        .program_id = "clone-fold-proof-closure",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &blocks,
        .instructions = &.{},
        .values = &.{},
        .evidence = &.{},
        .solver_terms = &terms,
        .edge_rewrites = &rewrites,
    };

    var closure = try Closure.initForObligationSubject(std.testing.allocator, &program, query);
    defer closure.deinit();
    try std.testing.expect(closure.edge_rewrites[root_id.index()]);
    try std.testing.expect(closure.edge_rewrites[fold_id.index()]);
    try std.testing.expect(closure.blocks[original.index()]);
    try std.testing.expect(closure.blocks[clone.index()]);
}

pub fn requiresExternalWitness(program: *const ir.Program) bool {
    return program.entry_bindings.len != 0 or program.external_bindings.len != 0;
}

fn needsRuntimeValueWitness(program: *const ir.Program, terms: []const bool, values: []const bool) bool {
    if (normalizedRealValueTermNeedsRuntimeWitness(program, terms)) return true;
    for (values, 0..) |needed, value_index| {
        if (!needed) continue;
        const value = program.values[value_index];
        switch (value.origin) {
            .parameter => {},
            .block_parameter, .capture => return true,
            .instruction_result => if (solver.normalizedValueSource(program, value.id) == null) return true,
        }
    }
    return false;
}

fn needsRuntimeIdentityWitness(value_packs: []const bool, places: []const bool) bool {
    return hasMarked(value_packs) or hasMarked(places);
}

fn needsRuntimeEffectWitness(program: *const ir.Program, terms: []const bool, values: []const bool) BuildError!bool {
    if (normalizedRealValueTermNeedsRuntimeWitness(program, terms)) return true;
    for (values, 0..) |needed, value_index| {
        if (!needed) continue;
        switch (program.values[value_index].origin) {
            .parameter, .capture => {},
            .block_parameter => return true,
            .instruction_result => |origin| {
                if (solver.normalizedValueSource(program, program.values[value_index].id) != null) continue;
                if (origin.instruction.index() >= program.instructions.len) return error.InvalidClosureInput;
                if (proof_effect_closure.hasObservableEffects(program.instructions[origin.instruction.index()].effects)) return true;
            },
        }
    }
    return false;
}

fn normalizedRealValueTermNeedsRuntimeWitness(program: *const ir.Program, terms: []const bool) bool {
    for (terms, 0..) |needed, term_index| {
        if (!needed or term_index >= program.solver_terms.len) continue;
        const term = program.solver_terms[term_index];
        if (term.sort.kind != .real) continue;
        const value_id = switch (term.operation) {
            .value => |value| value,
            else => continue,
        };
        if (solver.normalizedValueSource(program, value_id) != null) return true;
    }
    return false;
}

fn expandRuntimeValueDependencies(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    functions: []bool,
    values: []bool,
    value_packs: []bool,
    places: []bool,
    captures: []bool,
    instructions: []bool,
    blocks: []bool,
    evidence: []bool,
    include_external_witness: bool,
) BuildError!void {
    const processed_functions = try zeroedBools(allocator, functions.len);
    defer allocator.free(processed_functions);
    const processed_values = try zeroedBools(allocator, values.len);
    defer allocator.free(processed_values);
    const processed_packs = try zeroedBools(allocator, value_packs.len);
    defer allocator.free(processed_packs);
    const processed_places = try zeroedBools(allocator, places.len);
    defer allocator.free(processed_places);
    const processed_captures = try zeroedBools(allocator, captures.len);
    defer allocator.free(processed_captures);
    const processed_instructions = try zeroedBools(allocator, instructions.len);
    defer allocator.free(processed_instructions);

    if (include_external_witness and (program.entry_bindings.len != 0 or program.external_bindings.len != 0)) {
        try markEntity(functions, program.entry_function);
        const entry = program.functions[program.entry_function.index()];
        for (entry.captures) |capture_id| try markEntity(captures, capture_id);
        for (program.external_bindings) |binding| try markEvidence(evidence, binding.evidence);
    }

    var progressed = true;
    while (progressed) {
        progressed = false;

        for (values, 0..) |needed, value_index| {
            if (!needed or processed_values[value_index]) continue;
            processed_values[value_index] = true;
            progressed = true;
            const value = program.values[value_index];
            try markEntity(functions, value.function);
            switch (value.origin) {
                .parameter => {},
                .capture => |capture_id| try markEntity(captures, capture_id),
                .instruction_result => |origin| try markEntity(instructions, origin.instruction),
                .block_parameter => |origin| try markBlockParameterSources(
                    program,
                    values,
                    functions,
                    blocks,
                    value.id,
                    origin.block,
                    origin.index,
                ),
            }
        }

        for (instructions, 0..) |needed, instruction_index| {
            if (!needed or processed_instructions[instruction_index]) continue;
            processed_instructions[instruction_index] = true;
            progressed = true;
            const instruction = program.instructions[instruction_index];
            try markEntity(blocks, instruction.block);
            const block = program.blocks[instruction.block.index()];
            try markEntity(functions, block.function);
            try markValues(values, instruction.results);
            if (instruction.pack_result) |pack_id| try markEntity(value_packs, pack_id);

            var invalid_use = false;
            runtime_uses.visitOperationUses(instruction.operation, DependencyUseVisitor{
                .values = values,
                .value_packs = value_packs,
                .places = places,
                .invalid = &invalid_use,
            });
            if (invalid_use) return error.InvalidClosureInput;

            switch (instruction.operation) {
                .make_closure => |closure| {
                    try markEntity(functions, closure.function);
                    const target = program.functions[closure.function.index()];
                    for (target.captures) |capture_id| try markEntity(captures, capture_id);
                },
                .function_ref => |function_id| try markEntity(functions, function_id),
                else => {},
            }
        }

        for (value_packs, 0..) |needed, pack_index| {
            if (!needed or processed_packs[pack_index]) continue;
            processed_packs[pack_index] = true;
            progressed = true;
            const pack = program.value_packs[pack_index];
            try markEntity(functions, pack.function);
            switch (pack.origin) {
                .varargs => |function_id| try markEntity(functions, function_id),
                .instruction_result => |instruction_id| try markEntity(instructions, instruction_id),
            }
        }

        for (places, 0..) |needed, place_index| {
            if (!needed or processed_places[place_index]) continue;
            processed_places[place_index] = true;
            progressed = true;
            const place = program.places[place_index];
            try markEntity(functions, place.function);
            switch (place.origin) {
                .local => {},
                .instruction => |instruction_id| try markEntity(instructions, instruction_id),
                .capture => |capture_id| try markEntity(captures, capture_id),
            }
        }

        for (captures, 0..) |needed, capture_index| {
            if (!needed or processed_captures[capture_index]) continue;
            processed_captures[capture_index] = true;
            progressed = true;
            const capture = program.captures[capture_index];
            try markEntity(functions, capture.function);
            switch (capture.kind) {
                .immutable_value => |value_id| try markEntity(values, value_id),
                .shared_place => |place_id| try markEntity(places, place_id),
            }
            try markCaptureSources(program, values, places, instructions, capture);
        }

        for (functions, 0..) |needed, function_index| {
            if (!needed or processed_functions[function_index]) continue;
            processed_functions[function_index] = true;
            progressed = true;
            const function = program.functions[function_index];
            if (function.lexical_parent) |parent_id| try markEntity(functions, parent_id);
            if (function.vararg_pack) |pack_id| try markEntity(value_packs, pack_id);
        }
    }
}

fn markInstructionSemanticDependencies(
    program: *const ir.Program,
    instruction_id: ir.InstructionId,
    values: []bool,
    value_packs: []bool,
    places: []bool,
    instructions: []bool,
) BuildError!void {
    if (instruction_id.index() >= program.instructions.len or instruction_id.index() >= instructions.len) {
        return error.InvalidClosureInput;
    }
    const instruction = program.instructions[instruction_id.index()];
    if (instruction.id != instruction_id) return error.InvalidClosureInput;

    instructions[instruction_id.index()] = true;
    try markValues(values, instruction.results);
    if (instruction.pack_result) |pack_id| try markEntity(value_packs, pack_id);

    var invalid_use = false;
    runtime_uses.visitOperationUses(instruction.operation, DependencyUseVisitor{
        .values = values,
        .value_packs = value_packs,
        .places = places,
        .invalid = &invalid_use,
    });
    if (invalid_use) return error.InvalidClosureInput;
}

fn markBlockParameterSources(
    program: *const ir.Program,
    values: []bool,
    functions: []bool,
    blocks: []bool,
    value_id: ir.ValueId,
    target_id: ir.BlockId,
    parameter_index: u32,
) BuildError!void {
    try markEntity(blocks, target_id);
    const target = program.blocks[target_id.index()];
    if (parameter_index >= target.parameters.len or target.parameters[parameter_index] != value_id) return error.InvalidClosureInput;
    try markEntity(functions, target.function);

    for (program.blocks) |source| switch (source.terminator) {
        .jump => |edge| try markIncomingArgument(values, functions, blocks, source, edge, target_id, parameter_index),
        .branch => |branch| {
            try markIncomingArgument(values, functions, blocks, source, branch.then_edge, target_id, parameter_index);
            try markIncomingArgument(values, functions, blocks, source, branch.else_edge, target_id, parameter_index);
        },
        .return_values, .return_pack, .return_expanded, .throw_error, .unreachable_block => {},
    };
}

fn markIncomingArgument(
    values: []bool,
    functions: []bool,
    blocks: []bool,
    source: ir.Block,
    edge: ir.Edge,
    target_id: ir.BlockId,
    parameter_index: u32,
) BuildError!void {
    if (edge.target != target_id) return;
    if (parameter_index >= edge.arguments.len) return error.InvalidClosureInput;
    try markEntity(blocks, source.id);
    try markEntity(functions, source.function);
    try markEntity(values, edge.arguments[parameter_index]);
}

fn markCaptureSources(
    program: *const ir.Program,
    values: []bool,
    places: []bool,
    instructions: []bool,
    capture: ir.Capture,
) BuildError!void {
    if (capture.function.index() >= program.functions.len) return error.InvalidClosureInput;
    const function = program.functions[capture.function.index()];
    var capture_index: ?usize = null;
    for (function.captures, 0..) |candidate, index| {
        if (candidate == capture.id) {
            capture_index = index;
            break;
        }
    }
    const index = capture_index orelse return error.InvalidClosureInput;
    if (capture.function == program.entry_function) {
        if (index >= program.entry_bindings.len) return error.InvalidClosureInput;
        if (program.entry_bindings[index].index() >= program.external_bindings.len) return error.InvalidClosureInput;
        return;
    }

    for (program.instructions) |instruction| switch (instruction.operation) {
        .make_closure => |closure| {
            if (closure.function != capture.function) continue;
            if (index >= closure.bindings.len) return error.InvalidClosureInput;
            try markEntity(instructions, instruction.id);
            switch (closure.bindings[index]) {
                .value => |value_id| try markEntity(values, value_id),
                .place => |place_id| try markEntity(places, place_id),
            }
        },
        else => {},
    };
}

const DependencyUseVisitor = struct {
    values: []bool,
    value_packs: []bool,
    places: []bool,
    invalid: *bool,

    pub fn value(self: DependencyUseVisitor, value_id: ir.ValueId) void {
        markEntity(self.values, value_id) catch {
            self.invalid.* = true;
        };
    }

    pub fn pack(self: DependencyUseVisitor, pack_id: ir.ValuePackId) void {
        markEntity(self.value_packs, pack_id) catch {
            self.invalid.* = true;
        };
    }

    pub fn place(self: DependencyUseVisitor, place_id: ir.PlaceId) void {
        markEntity(self.places, place_id) catch {
            self.invalid.* = true;
        };
    }
};

fn zeroedBools(allocator: std.mem.Allocator, count: usize) std.mem.Allocator.Error![]bool {
    const values = try allocator.alloc(bool, count);
    @memset(values, false);
    return values;
}

fn dependencyMarkCount(
    functions: []const bool,
    values: []const bool,
    value_packs: []const bool,
    places: []const bool,
    captures: []const bool,
    instructions: []const bool,
    blocks: []const bool,
) usize {
    var count: usize = 0;
    for (functions) |marked| count += @intFromBool(marked);
    for (values) |marked| count += @intFromBool(marked);
    for (value_packs) |marked| count += @intFromBool(marked);
    for (places) |marked| count += @intFromBool(marked);
    for (captures) |marked| count += @intFromBool(marked);
    for (instructions) |marked| count += @intFromBool(marked);
    for (blocks) |marked| count += @intFromBool(marked);
    return count;
}

fn hasMarked(entities: []const bool) bool {
    for (entities) |marked| if (marked) return true;
    return false;
}

fn isMarked(entities: []const bool, id: anytype) bool {
    return id.index() < entities.len and entities[id.index()];
}

fn markEntity(entities: anytype, id: anytype) BuildError!void {
    if (id.index() >= entities.len) return error.InvalidClosureInput;
    entities[id.index()] = true;
}

fn markTerm(needed: []bool, term_id: ir.SolverTermId) BuildError!void {
    if (term_id.index() >= needed.len) return error.InvalidClosureInput;
    needed[term_id.index()] = true;
}

fn markBlock(needed: []bool, block_id: ir.BlockId) BuildError!void {
    if (block_id.index() >= needed.len) return error.InvalidClosureInput;
    needed[block_id.index()] = true;
}

fn markEdgeRewriteDependencies(
    program: *const ir.Program,
    rewrite_id: ir.EdgeRewriteId,
    edge_rewrites: []bool,
    blocks: []bool,
    instructions: []bool,
    values: []bool,
    evidence: []bool,
) BuildError!void {
    if (rewrite_id.index() >= program.edge_rewrites.len or rewrite_id.index() >= edge_rewrites.len) {
        return error.InvalidClosureInput;
    }
    const rewrite = program.edge_rewrites[rewrite_id.index()];
    if (rewrite.id != rewrite_id) return error.InvalidClosureInput;
    edge_rewrites[rewrite_id.index()] = true;
    try markBlock(blocks, rewrite.from.target);
    try markBlock(blocks, rewrite.to.target);
    if (rewrite.from.target.index() >= program.blocks.len) return error.InvalidClosureInput;
    for (program.blocks[rewrite.from.target.index()].instructions) |instruction_id| {
        if (instruction_id.index() >= instructions.len) return error.InvalidClosureInput;
        instructions[instruction_id.index()] = true;
        try markValues(values, program.instructions[instruction_id.index()].results);
    }
    try markValues(values, rewrite.from.arguments);
    try markValues(values, rewrite.to.arguments);
    if (rewrite.certificate) |certificate_id| {
        if (certificate_id.index() >= program.certificates.len) return error.InvalidClosureInput;
        try markEvidence(evidence, program.certificates[certificate_id.index()].evidence);
    } else if (rewrite.rule != .forwarding_jump and rewrite.rule != .node_split and rewrite.rule != .clone_fold) {
        return error.InvalidClosureInput;
    }
}

fn markEvidence(needed: []bool, evidence: []const ir.EvidenceId) BuildError!void {
    for (evidence) |evidence_id| {
        if (evidence_id.index() >= needed.len) return error.InvalidClosureInput;
        needed[evidence_id.index()] = true;
    }
}

fn markValues(needed: []bool, values: []const ir.ValueId) BuildError!void {
    for (values) |value_id| {
        if (value_id.index() >= needed.len) return error.InvalidClosureInput;
        needed[value_id.index()] = true;
    }
}

fn semanticAtomInstruction(atom: ir.SemanticAtom) ir.InstructionId {
    return switch (atom) {
        .instruction_effects => |instruction_id| instruction_id,
        .no_metamethod_dispatch => |instruction_id| instruction_id,
        .primitive_operator_domain => |instruction_id| instruction_id,
    };
}

test "instruction semantic closure follows direct capture operands" {
    const fixture = @import("fixtures.zig").immutable_closure_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .semantic_atom = .{ .primitive_operator_domain = fixture.i_add } },
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    var closure = try Closure.init(std.testing.allocator, &program, query, &.{fixture.proof}, &.{});
    defer closure.deinit();
    try std.testing.expect(closure.lexical_witness);
    try std.testing.expect(!closure.runtime_value_witness);
    try std.testing.expect(!closure.combined_runtime_witness);
    try std.testing.expect(closure.values[fixture.v_sum.index()]);
    try std.testing.expect(closure.values[fixture.v_captured_base.index()]);
    try std.testing.expect(closure.values[fixture.v_delta.index()]);
    try std.testing.expect(closure.values[fixture.v_base.index()]);
    try std.testing.expect(closure.captures[fixture.c_base.index()]);
    try std.testing.expect(closure.instructions[fixture.i_add.index()]);
    try std.testing.expect(closure.instructions[fixture.i_make_adder.index()]);
    try std.testing.expect(!closure.instructions[fixture.i_export.index()]);
    try std.testing.expect(closure.blocks[fixture.b_adder.index()]);
    try std.testing.expect(closure.blocks[fixture.b_factory.index()]);
    try std.testing.expect(!closure.blocks[fixture.b_entry.index()]);
}

test "instruction semantic closure follows direct pack identity" {
    const fixture = @import("fixtures.zig").open_pack_adjust_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .semantic_atom = .{ .instruction_effects = fixture.i_adjust } },
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    var closure = try Closure.init(std.testing.allocator, &program, query, &.{fixture.proof}, &.{});
    defer closure.deinit();
    try std.testing.expect(!closure.lexical_witness);
    try std.testing.expect(closure.runtime_value_witness);
    try std.testing.expect(!closure.combined_runtime_witness);
    try std.testing.expect(closure.value_packs[fixture.p_results.index()]);
    try std.testing.expect(closure.values[fixture.v_first.index()]);
    try std.testing.expect(closure.values[fixture.v_callee.index()]);
    try std.testing.expect(closure.instructions[fixture.i_adjust.index()]);
    try std.testing.expect(closure.instructions[fixture.i_call.index()]);
    try std.testing.expect(closure.instructions[fixture.i_get.index()]);
}

test "value proof closure includes normalized definitions and provenance" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_is_negative.index()].operation = .{ .constant = .{ .boolean = true } };
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = fixture.v_is_negative },
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    };
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;

    var closure = try Closure.init(std.testing.allocator, &program, query, &.{}, &.{});
    defer closure.deinit();
    try std.testing.expect(closure.terms[0]);
    try std.testing.expect(closure.values[fixture.v_is_negative.index()]);
    try std.testing.expect(closure.instructions[fixture.i_is_negative.index()]);
    try std.testing.expect(closure.evidence[fixture.proof.index()]);
}

test "real numeric constants retain runtime value proof witnesses" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var values = fixture.values;
    var instructions = fixture.instructions;
    const real: ir.SolverSort = .{ .kind = .real };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = real, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = real, .operation = .{ .real_literal = .{ .numerator = "7", .denominator = "1" } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .find_model, .goal = ir.SolverTermId.fromIndex(2) };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;

    values[fixture.v_factor.index()].type = .number;
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .number = 7.0 } };
    var number_closure = try Closure.init(std.testing.allocator, &program, query, &.{}, &.{});
    defer number_closure.deinit();
    try std.testing.expect(number_closure.runtime_value_witness);

    values[fixture.v_factor.index()].type = .dynamic;
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{ .integer = "7" } };
    var integer_closure = try Closure.init(std.testing.allocator, &program, query, &.{}, &.{});
    defer integer_closure.deinit();
    try std.testing.expect(integer_closure.runtime_value_witness);
}

test "lexical proof closure follows block transfers and every capture constructor" {
    const fixture = @import("fixtures.zig").immutable_closure_module;
    const factory_entry = ir.BlockId.fromIndex(fixture.blocks.len);
    const second_constructor = ir.InstructionId.fromIndex(fixture.instructions.len);
    const forwarded = ir.ValueId.fromIndex(fixture.values.len);
    const alternate = ir.ValueId.fromIndex(fixture.values.len + 1);
    const second_closure = ir.ValueId.fromIndex(fixture.values.len + 2);
    const values = fixture.values ++ [_]ir.Value{
        .{ .id = forwarded, .function = fixture.f_factory, .type = .integer, .origin = .{ .block_parameter = .{ .block = fixture.b_factory, .index = 0 } } },
        .{ .id = alternate, .function = fixture.f_factory, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = second_closure, .function = fixture.f_factory, .type = .function, .origin = .{ .instruction_result = .{ .instruction = second_constructor, .index = 0 } } },
    };
    var instructions = fixture.instructions ++ [_]ir.Instruction{.{
        .id = second_constructor,
        .block = fixture.b_factory,
        .operation = .{ .make_closure = .{
            .function = fixture.f_adder,
            .bindings = &.{.{ .value = alternate }},
        } },
        .results = &.{second_closure},
        .effects = .pure,
        .evidence = &.{fixture.proof},
    }};
    instructions[fixture.i_make_adder.index()].operation.make_closure.bindings = &.{.{ .value = forwarded }};
    var blocks = fixture.blocks ++ [_]ir.Block{.{
        .id = factory_entry,
        .function = fixture.f_factory,
        .terminator = .{ .jump = .{ .target = fixture.b_factory, .arguments = &.{fixture.v_base} } },
        .evidence = &.{fixture.proof},
    }};
    blocks[fixture.b_factory.index()].parameters = &.{forwarded};
    blocks[fixture.b_factory.index()].instructions = &.{ fixture.i_make_adder, second_constructor };
    var functions = fixture.functions;
    functions[fixture.f_factory.index()].parameters = &.{ fixture.v_base, alternate };
    functions[fixture.f_factory.index()].blocks = &.{ factory_entry, fixture.b_factory };
    functions[fixture.f_factory.index()].entry_block = factory_entry;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_captured_base } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
    };
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(2),
        .evidence = &.{fixture.proof},
        .scope = .{ .edge = .{ .source = factory_entry, .kind = .jump, .target = fixture.b_factory } },
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(1),
    };
    var program = fixture.program;
    program.functions = &functions;
    program.blocks = &blocks;
    program.instructions = &instructions;
    program.values = &values;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    var closure = try Closure.init(std.testing.allocator, &program, query, &.{fixture.proof}, &.{});
    defer closure.deinit();
    try std.testing.expect(closure.functions[fixture.f_factory.index()]);
    try std.testing.expect(closure.functions[fixture.f_adder.index()]);
    try std.testing.expect(!closure.functions[fixture.f_entry.index()]);
    try std.testing.expect(closure.captures[fixture.c_base.index()]);
    try std.testing.expect(closure.values[fixture.v_captured_base.index()]);
    try std.testing.expect(closure.values[fixture.v_base.index()]);
    try std.testing.expect(closure.values[forwarded.index()]);
    try std.testing.expect(closure.values[alternate.index()]);
    try std.testing.expect(closure.instructions[fixture.i_make_adder.index()]);
    try std.testing.expect(closure.instructions[second_constructor.index()]);
    try std.testing.expect(!closure.instructions[fixture.i_export.index()]);
    try std.testing.expect(!closure.instructions[fixture.i_add.index()]);
    try std.testing.expect(closure.blocks[factory_entry.index()]);
    try std.testing.expect(closure.blocks[fixture.b_factory.index()]);

    const edge_query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(1),
        .kind = .prove_true,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(2),
    };
    var edge_closure = try Closure.init(std.testing.allocator, &program, edge_query, &.{fixture.proof}, &.{});
    defer edge_closure.deinit();
    try std.testing.expect(edge_closure.values[forwarded.index()]);
    try std.testing.expect(edge_closure.values[fixture.v_base.index()]);
    try std.testing.expect(!edge_closure.captures[fixture.c_base.index()]);
    try std.testing.expect(!edge_closure.instructions[fixture.i_make_adder.index()]);
}

test "lexical proof closure follows shared place captures" {
    const fixture = @import("fixtures.zig").shared_place_closure_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_current } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(1),
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    var closure = try Closure.init(std.testing.allocator, &program, query, &.{fixture.proof}, &.{});
    defer closure.deinit();
    try std.testing.expect(closure.functions[fixture.f_factory.index()]);
    try std.testing.expect(closure.functions[fixture.f_counter.index()]);
    try std.testing.expect(!closure.functions[fixture.f_entry.index()]);
    try std.testing.expect(closure.captures[fixture.c_state.index()]);
    try std.testing.expect(closure.places[fixture.p_state.index()]);
    try std.testing.expect(closure.places[fixture.p_captured_state.index()]);
    try std.testing.expect(closure.instructions[fixture.i_make_counter.index()]);
    try std.testing.expect(closure.instructions[fixture.i_read.index()]);
    try std.testing.expect(closure.combined_runtime_witness);
    try std.testing.expect(closure.instructions[fixture.i_initialize.index()]);
    try std.testing.expect(!closure.instructions[fixture.i_write.index()]);
}

test "lexical proof closure refuses an omitted constructor binding" {
    const fixture = @import("fixtures.zig").immutable_closure_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_make_adder.index()].operation.make_closure.bindings = &.{};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_captured_base } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(1),
    };
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;

    try std.testing.expectError(
        error.InvalidClosureInput,
        Closure.init(std.testing.allocator, &program, query, &.{fixture.proof}, &.{}),
    );
}

test "runtime value proof closure tracks capture-free places" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const write_before_id = ir.InstructionId.fromIndex(0);
    const read_id = ir.InstructionId.fromIndex(1);
    const write_after_id = ir.InstructionId.fromIndex(2);
    const selected_place = ir.PlaceId.fromIndex(0);
    const unrelated_place = ir.PlaceId.fromIndex(1);
    const initial_value = ir.ValueId.fromIndex(0);
    const later_value = ir.ValueId.fromIndex(1);
    const result_value = ir.ValueId.fromIndex(2);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = initial_value, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = later_value, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{
            .id = result_value,
            .function = function_id,
            .type = .integer,
            .origin = .{ .instruction_result = .{ .instruction = read_id, .index = 0 } },
        },
    };
    const places = [_]ir.Place{
        .{ .id = selected_place, .function = function_id, .type = .integer, .origin = .{ .local = 0 }, .evidence = &.{evidence_id} },
        .{ .id = unrelated_place, .function = function_id, .type = .integer, .origin = .{ .local = 1 }, .evidence = &.{evidence_id} },
    };
    const instructions = [_]ir.Instruction{
        .{
            .id = write_before_id,
            .block = block_id,
            .operation = .{ .place_write = .{ .place = selected_place, .value = initial_value } },
            .results = &.{},
            .effects = .place_write,
            .evidence = &.{evidence_id},
        },
        .{
            .id = read_id,
            .block = block_id,
            .operation = .{ .place_read = selected_place },
            .results = &.{result_value},
            .effects = .place_read,
            .evidence = &.{evidence_id},
        },
        .{
            .id = write_after_id,
            .block = block_id,
            .operation = .{ .place_write = .{ .place = selected_place, .value = later_value } },
            .results = &.{},
            .effects = .place_write,
            .evidence = &.{evidence_id},
        },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ write_before_id, read_id, write_after_id },
        .terminator = .{ .return_values = &.{result_value} },
        .evidence = &.{evidence_id},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ initial_value, later_value },
        .local_places = &.{ selected_place, unrelated_place },
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .dynamic_fixture, .locator = "fixture:capture-free-place-proof" }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = result_value } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(1) };
    const program: ir.Program = .{
        .program_id = "capture-free-place-proof",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .places = &places,
        .evidence = &evidence,
        .solver_terms = &terms,
    };

    var closure = try Closure.init(std.testing.allocator, &program, query, &.{evidence_id}, &.{});
    defer closure.deinit();
    try std.testing.expect(closure.runtime_value_witness);
    try std.testing.expect(closure.places[selected_place.index()]);
    try std.testing.expect(!closure.places[unrelated_place.index()]);
    try std.testing.expect(closure.instructions[write_before_id.index()]);
    try std.testing.expect(closure.instructions[read_id.index()]);
    try std.testing.expect(!closure.instructions[write_after_id.index()]);
    try std.testing.expect(closure.values[initial_value.index()]);
    try std.testing.expect(!closure.values[later_value.index()]);
}
