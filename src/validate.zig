const std = @import("std");
const ir = @import("ir.zig");
const proof_validation = @import("validate_proofs.zig");
const diagnostics = @import("diagnostics.zig");
const cfg_validation = @import("validate_cfg.zig");
const pack_validation = @import("validate_packs.zig");
const closure_validation = @import("validate_closures.zig");
const type_validation = @import("validate_types.zig");
const call_validation = @import("validate_calls.zig");
const operation_validation = @import("validate_operations.zig");
const register_validation = @import("validate_luau_registers.zig");
const readable_scope = @import("readable_scope.zig");
const luau_runtime = @import("luau_runtime.zig");

pub const DiagnosticCode = diagnostics.Code;
pub const Diagnostic = diagnostics.Diagnostic;
pub const Report = diagnostics.Report;

/// Emission layout the readable-Luau register budget models. `automatic`
/// is the default admission; `dispatcher` mirrors the emitter's forced layout.
pub const EmissionStrategy = register_validation.EmissionStrategy;

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}

fn validateEvidenceList(report: *Report, program: *const ir.Program, evidence: []const ir.EvidenceId, entity_index: usize) !void {
    for (evidence) |evidence_id| {
        if (!validId(evidence_id, program.evidence.len)) try report.add(.invalid_evidence_reference, entity_index);
    }
}

pub fn validate(allocator: std.mem.Allocator, program: *const ir.Program, profile: ir.AdmissionProfile) !Report {
    return validateForTarget(allocator, program, profile, .standard_luau);
}

pub fn validateForTarget(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    profile: ir.AdmissionProfile,
    target: luau_runtime.Target,
) !Report {
    return validateForTargetWithStrategy(allocator, program, profile, target, .automatic);
}

pub fn validateForTargetWithStrategy(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    profile: ir.AdmissionProfile,
    target: luau_runtime.Target,
    strategy: EmissionStrategy,
) !Report {
    var report = Report.init(allocator);
    errdefer report.deinit();

    if (program.program_id.len == 0) try report.add(.empty_program_id, null);
    if (program.functions.len == 0) try report.add(.missing_function, null);
    if (!validId(program.entry_function, program.functions.len)) try report.add(.invalid_entry_function, program.entry_function.index());

    try validateCanonicalIds(&report, program);
    try type_validation.validateDescriptors(&report, program);

    const defined_values = try allocator.alloc(bool, program.values.len);
    defer allocator.free(defined_values);
    @memset(defined_values, false);

    const defined_places = try allocator.alloc(bool, program.places.len);
    defer allocator.free(defined_places);
    @memset(defined_places, false);

    const block_memberships = try allocator.alloc(u32, program.blocks.len);
    defer allocator.free(block_memberships);
    @memset(block_memberships, 0);

    const instruction_memberships = try allocator.alloc(u32, program.instructions.len);
    defer allocator.free(instruction_memberships);
    @memset(instruction_memberships, 0);

    const capture_memberships = try allocator.alloc(u32, program.captures.len);
    defer allocator.free(capture_memberships);
    @memset(capture_memberships, 0);

    try validateFunctions(&report, program, defined_values, defined_places, block_memberships, capture_memberships);
    try closure_validation.validateTopology(&report, program);
    try closure_validation.validateCaptures(&report, program, defined_values, defined_places);
    try closure_validation.validateEntryBindings(&report, program);
    try type_validation.validateEntryBindings(&report, program);
    try validateBlocks(&report, program, defined_values, instruction_memberships);
    for (block_memberships, 0..) |count, index| {
        if (count == 0) try report.add(.unlisted_function_block, index);
        if (count > 1) try report.add(.duplicate_function_block, index);
    }
    for (instruction_memberships, 0..) |count, index| {
        if (count == 0) try report.add(.unlisted_block_instruction, index);
        if (count > 1) try report.add(.duplicate_block_instruction, index);
    }
    for (capture_memberships, 0..) |count, index| {
        if (count == 0) try report.add(.unlisted_function_capture, index);
        if (count > 1) try report.add(.duplicate_function_capture, index);
    }
    var maybe_scope: ?readable_scope.Scope = if (profile == .readable_luau)
        try readable_scope.Scope.init(allocator, program)
    else
        null;
    defer if (maybe_scope) |*scope| scope.deinit();
    const scope = if (maybe_scope) |*value| value else null;

    try validateInstructions(&report, program, profile, scope, defined_values);
    if (profile == .readable_luau) {
        for (program.functions, 0..) |function, index| {
            if (function.evidence.len == 0) try report.add(.missing_emission_evidence, index);
        }
        for (program.blocks, 0..) |block, index| {
            if ((scope == null or scope.?.block(block.id)) and block.evidence.len == 0) try report.add(.missing_emission_evidence, index);
        }
        for (program.places, 0..) |place, index| {
            if (place.evidence.len == 0) try report.add(.missing_emission_evidence, index);
        }
        for (program.captures, 0..) |capture, index| {
            if (capture.evidence.len == 0) try report.add(.missing_emission_evidence, index);
        }
        for (program.external_bindings, 0..) |binding, index| {
            if (binding.evidence.len == 0) try report.add(.missing_emission_evidence, index);
        }
    }
    try validateValues(&report, program, defined_values);
    try closure_validation.validatePlaces(&report, program, defined_places);
    try pack_validation.validate(allocator, &report, program, profile, scope);
    try cfg_validation.validate(allocator, &report, program, profile, block_memberships, instruction_memberships);
    try call_validation.validate(allocator, &report, program);
    try proof_validation.validate(&report, program, profile, scope);
    if (profile == .readable_luau) try operation_validation.validateReadableCapabilities(&report, program, scope.?);
    if (profile == .readable_luau and report.isClean()) {
        try register_validation.validateWithStrategy(allocator, &report, program, scope.?, target, strategy);
    }

    return report;
}

fn validateCanonicalIds(report: *Report, program: *const ir.Program) !void {
    for (program.functions, 0..) |function, index| if (function.id.index() != index) try report.add(.noncanonical_function_id, index);
    for (program.blocks, 0..) |block, index| if (block.id.index() != index) try report.add(.noncanonical_block_id, index);
    for (program.instructions, 0..) |instruction, index| if (instruction.id.index() != index) try report.add(.noncanonical_instruction_id, index);
    for (program.values, 0..) |value, index| if (value.id.index() != index) try report.add(.noncanonical_value_id, index);
    for (program.places, 0..) |place, index| if (place.id.index() != index) try report.add(.noncanonical_place_id, index);
    for (program.captures, 0..) |capture, index| if (capture.id.index() != index) try report.add(.noncanonical_capture_id, index);
    for (program.external_bindings, 0..) |binding, index| if (binding.id.index() != index) try report.add(.noncanonical_external_binding_id, index);
    for (program.evidence, 0..) |evidence, index| if (evidence.id.index() != index) try report.add(.noncanonical_evidence_id, index);
    for (program.evidence, 0..) |evidence, index| {
        if (evidence.locator.len == 0 or (evidence.digest != null and evidence.digest.?.len == 0)) try report.add(.invalid_evidence_record, index);
    }
    for (program.solver_terms, 0..) |term, index| if (term.id.index() != index) try report.add(.noncanonical_solver_term_id, index);
    for (program.constraints, 0..) |constraint, index| if (constraint.id.index() != index) try report.add(.noncanonical_constraint_id, index);
    for (program.queries, 0..) |query, index| if (query.id.index() != index) try report.add(.noncanonical_query_id, index);
    for (program.solver_models, 0..) |model, index| if (model.id.index() != index) try report.add(.noncanonical_solver_model_id, index);
    for (program.unsat_cores, 0..) |core, index| if (core.id.index() != index) try report.add(.noncanonical_unsat_core_id, index);
    for (program.certificates, 0..) |certificate, index| if (certificate.id.index() != index) try report.add(.noncanonical_certificate_id, index);
    for (program.edge_rewrites, 0..) |rewrite, index| if (rewrite.id.index() != index) try report.add(.noncanonical_edge_rewrite_id, index);
    for (program.claims, 0..) |claim, index| if (claim.id.index() != index) try report.add(.noncanonical_claim_id, index);
    for (program.obligations, 0..) |obligation, index| if (obligation.id.index() != index) try report.add(.noncanonical_obligation_id, index);
}

fn validateFunctions(
    report: *Report,
    program: *const ir.Program,
    defined_values: []bool,
    defined_places: []bool,
    block_memberships: []u32,
    capture_memberships: []u32,
) !void {
    for (program.functions, 0..) |function, function_index| {
        try validateEvidenceList(report, program, function.evidence, function_index);
        if (function.lexical_parent) |parent| {
            if (!validId(parent, program.functions.len) or parent == function.id) {
                try report.add(.invalid_function_lexical_parent, function_index);
            }
        } else if (function.captures.len != 0 and function.id != program.entry_function) {
            try report.add(.capture_without_lexical_parent, function_index);
        }
        var entry_found = false;
        for (function.blocks) |block_id| {
            if (!validId(block_id, program.blocks.len)) {
                try report.add(.invalid_function_block, function_index);
                continue;
            }
            if (block_memberships[block_id.index()] != std.math.maxInt(u32)) block_memberships[block_id.index()] += 1;
            if (program.blocks[block_id.index()].function != function.id) try report.add(.function_block_owner_mismatch, function_index);
            if (block_id == function.entry_block) entry_found = true;
        }
        if (!entry_found) try report.add(.missing_function_entry_block, function_index);
        if (validId(function.entry_block, program.blocks.len) and program.blocks[function.entry_block.index()].parameters.len != 0) {
            try report.add(.entry_block_has_parameters, function_index);
        }

        for (function.parameters, 0..) |value_id, parameter_index| {
            if (!validId(value_id, program.values.len)) {
                try report.add(.invalid_function_parameter, function_index);
                continue;
            }
            const value = program.values[value_id.index()];
            const origin_matches = switch (value.origin) {
                .parameter => |index| index == parameter_index,
                else => false,
            };
            if (value.function != function.id or !origin_matches) try report.add(.function_parameter_origin_mismatch, value_id.index());
            try markDefinition(report, defined_values, value_id);
        }

        for (function.captures) |capture_id| {
            if (!validId(capture_id, program.captures.len)) {
                try report.add(.invalid_function_capture, function_index);
                continue;
            }
            if (capture_memberships[capture_id.index()] != std.math.maxInt(u32)) capture_memberships[capture_id.index()] += 1;
            if (program.captures[capture_id.index()].function != function.id) {
                try report.add(.function_capture_origin_mismatch, capture_id.index());
            }
        }

        for (function.local_places, 0..) |place_id, place_index| {
            if (!validId(place_id, program.places.len)) {
                try report.add(.invalid_function_local_place, function_index);
                continue;
            }
            const place = program.places[place_id.index()];
            const origin_matches = switch (place.origin) {
                .local => |index| index == place_index,
                .instruction => |instruction_id| blk: {
                    if (!validId(instruction_id, program.instructions.len)) break :blk false;
                    const instruction = program.instructions[instruction_id.index()];
                    if (!validId(instruction.block, program.blocks.len) or program.blocks[instruction.block.index()].function != function.id) {
                        break :blk false;
                    }
                    break :blk switch (instruction.operation) {
                        .place_write => |write| write.place == place.id,
                        else => false,
                    };
                },
                else => false,
            };
            if (place.function != function.id or !origin_matches) {
                try report.add(.function_local_place_origin_mismatch, place_id.index());
            }
            try closure_validation.markPlaceDefinition(report, defined_places, place_id);
        }
    }
}

fn validateBlocks(report: *Report, program: *const ir.Program, defined_values: []bool, instruction_memberships: []u32) !void {
    for (program.blocks, 0..) |block, block_index| {
        try validateEvidenceList(report, program, block.evidence, block_index);
        if (!validId(block.function, program.functions.len)) try report.add(.invalid_block_function, block_index);

        for (block.parameters, 0..) |value_id, parameter_index| {
            if (!validId(value_id, program.values.len)) {
                try report.add(.invalid_block_parameter, block_index);
                continue;
            }
            const value = program.values[value_id.index()];
            const origin_matches = switch (value.origin) {
                .block_parameter => |parameter| parameter.block == block.id and parameter.index == parameter_index,
                else => false,
            };
            if (value.function != block.function or !origin_matches) try report.add(.block_parameter_origin_mismatch, value_id.index());
            try markDefinition(report, defined_values, value_id);
        }

        for (block.instructions) |instruction_id| {
            if (!validId(instruction_id, program.instructions.len)) {
                try report.add(.invalid_block_instruction, block_index);
                continue;
            }
            if (instruction_memberships[instruction_id.index()] != std.math.maxInt(u32)) instruction_memberships[instruction_id.index()] += 1;
            if (program.instructions[instruction_id.index()].block != block.id) try report.add(.block_instruction_owner_mismatch, instruction_id.index());
        }

        try validateTerminator(report, program, block);
    }
}

fn validateInstructions(
    report: *Report,
    program: *const ir.Program,
    profile: ir.AdmissionProfile,
    scope: ?*const readable_scope.Scope,
    defined_values: []bool,
) !void {
    for (program.instructions, 0..) |instruction, instruction_index| {
        try validateEvidenceList(report, program, instruction.evidence, instruction_index);
        if (!validId(instruction.block, program.blocks.len)) {
            try report.add(.invalid_instruction_block, instruction_index);
            continue;
        }
        const function_id = program.blocks[instruction.block.index()].function;

        for (instruction.results, 0..) |value_id, result_index| {
            if (!validId(value_id, program.values.len)) {
                try report.add(.invalid_instruction_result, instruction_index);
                continue;
            }
            const value = program.values[value_id.index()];
            const origin_matches = switch (value.origin) {
                .instruction_result => |result| result.instruction == instruction.id and result.index == result_index,
                else => false,
            };
            if (value.function != function_id or !origin_matches) try report.add(.instruction_result_origin_mismatch, value_id.index());
            try markDefinition(report, defined_values, value_id);
        }

        const readable = profile == .readable_luau and (scope == null or scope.?.instruction(instruction.id));
        try operation_validation.validate(report, program, instruction, function_id, if (readable) .readable_luau else .core);
        try type_validation.validateOperationResult(report, program, instruction);
        for (instruction.claims, 0..) |claim_id, claim_position| {
            if (!validId(claim_id, program.claims.len)) {
                try report.add(.invalid_instruction_claim, instruction_index);
            } else {
                const subject_matches = switch (program.claims[claim_id.index()].subject) {
                    .instruction => |subject_id| subject_id == instruction.id,
                    else => false,
                };
                if (!subject_matches) try report.add(.instruction_claim_subject_mismatch, instruction_index);
            }
            for (instruction.claims[0..claim_position]) |prior_id| {
                if (prior_id == claim_id) {
                    try report.add(.duplicate_instruction_claim, instruction_index);
                    break;
                }
            }
        }
        if (readable and instruction.effects.precision == .unknown) try report.add(.unknown_effects, instruction_index);
        if (readable and instruction.evidence.len == 0) try report.add(.missing_emission_evidence, instruction_index);
    }
}

fn markDefinition(report: *Report, defined_values: []bool, value_id: ir.ValueId) !void {
    if (!validId(value_id, defined_values.len)) return;
    if (defined_values[value_id.index()]) try report.add(.duplicate_value_definition, value_id.index());
    defined_values[value_id.index()] = true;
}

fn validateValues(report: *Report, program: *const ir.Program, defined_values: []const bool) !void {
    for (program.values, 0..) |value, value_index| {
        if (!validId(value.function, program.functions.len)) try report.add(.invalid_value_function, value_index);
        if (!defined_values[value_index]) try report.add(.missing_value_definition, value_index);

        switch (value.origin) {
            .parameter => {},
            .block_parameter => |parameter| if (!validId(parameter.block, program.blocks.len)) try report.add(.invalid_value_origin, value_index),
            .instruction_result => |result| if (!validId(result.instruction, program.instructions.len)) try report.add(.invalid_value_origin, value_index),
            .capture => |capture_id| if (!validId(capture_id, program.captures.len)) try report.add(.invalid_value_origin, value_index),
        }
    }
}

fn validateTerminator(report: *Report, program: *const ir.Program, block: ir.Block) !void {
    switch (block.terminator) {
        .jump => |edge| try validateEdge(report, program, block, edge),
        .branch => |branch| {
            try operation_validation.validateOperand(report, program, branch.condition, block.function, block.id.index());
            if (validId(branch.condition, program.values.len)) {
                const value_type = program.values[branch.condition.index()].type;
                if (value_type.kind != .boolean and value_type.kind != .dynamic and value_type.knownLuauTruthiness() == null) {
                    try report.add(.invalid_branch_condition, block.id.index());
                }
            }
            try validateEdge(report, program, block, branch.then_edge);
            try validateEdge(report, program, block, branch.else_edge);
        },
        .return_values => |values| for (values) |value| try validateTerminatorValue(report, program, block, value),
        .return_pack => {},
        .return_expanded => |expanded| for (expanded.values) |value| try validateTerminatorValue(report, program, block, value),
        .throw_error => |throw_error| {
            try validateTerminatorValue(report, program, block, throw_error.value);
            if (throw_error.dynamic_level) |level| {
                try validateTerminatorValue(report, program, block, level);
                if (throw_error.level != 0) try report.add(.conflicting_error_levels, block.id.index());
            }
        },
        .unreachable_block => {},
    }
}

fn validateTerminatorValue(report: *Report, program: *const ir.Program, block: ir.Block, value_id: ir.ValueId) !void {
    if (!validId(value_id, program.values.len)) {
        try report.add(.invalid_terminator_value, block.id.index());
        return;
    }
    if (program.values[value_id.index()].function != block.function) try report.add(.cross_function_operand, block.id.index());
}

fn validateEdge(report: *Report, program: *const ir.Program, source: ir.Block, edge: ir.Edge) !void {
    if (!validId(edge.target, program.blocks.len)) {
        try report.add(.invalid_edge_target, source.id.index());
        return;
    }
    const target = program.blocks[edge.target.index()];
    if (target.function != source.function) try report.add(.cross_function_edge, source.id.index());
    if (target.parameters.len != edge.arguments.len) try report.add(.edge_argument_arity_mismatch, source.id.index());
    for (edge.arguments) |argument| try operation_validation.validateOperand(report, program, argument, source.function, source.id.index());
    const pair_count = @min(target.parameters.len, edge.arguments.len);
    for (0..pair_count) |index| {
        const parameter_id = target.parameters[index];
        const argument_id = edge.arguments[index];
        if (!validId(parameter_id, program.values.len) or !validId(argument_id, program.values.len)) continue;
        if (!type_validation.isAssignable(program.values[parameter_id.index()].type, program.values[argument_id.index()].type)) {
            try report.add(.edge_argument_type_mismatch, source.id.index());
        }
    }
}
