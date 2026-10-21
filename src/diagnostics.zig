const std = @import("std");
const ir = @import("ir.zig");
const solver_backend = @import("solver_backend.zig");

pub const Code = enum {
    empty_program_id,
    missing_function,
    noncanonical_function_id,
    noncanonical_block_id,
    noncanonical_instruction_id,
    noncanonical_value_id,
    noncanonical_value_pack_id,
    noncanonical_place_id,
    noncanonical_capture_id,
    noncanonical_external_binding_id,
    noncanonical_evidence_id,
    noncanonical_solver_term_id,
    noncanonical_constraint_id,
    noncanonical_query_id,
    noncanonical_solver_model_id,
    noncanonical_unsat_core_id,
    noncanonical_certificate_id,
    noncanonical_edge_rewrite_id,
    noncanonical_claim_id,
    noncanonical_obligation_id,
    invalid_entry_function,
    invalid_entry_function_parent,
    invalid_function_lexical_parent,
    cyclic_function_lexical_parent,
    capture_without_lexical_parent,
    entry_capture_binding_arity_mismatch,
    invalid_entry_capture_binding,
    entry_capture_binding_kind_mismatch,
    entry_capture_binding_type_mismatch,
    unlisted_external_binding,
    invalid_function_block,
    function_block_owner_mismatch,
    missing_function_entry_block,
    invalid_function_parameter,
    function_parameter_origin_mismatch,
    invalid_function_capture,
    function_capture_origin_mismatch,
    duplicate_function_capture,
    unlisted_function_capture,
    invalid_function_local_place,
    function_local_place_origin_mismatch,
    invalid_function_vararg_pack,
    function_vararg_pack_origin_mismatch,
    invalid_block_function,
    invalid_block_parameter,
    block_parameter_origin_mismatch,
    invalid_block_instruction,
    block_instruction_owner_mismatch,
    invalid_instruction_block,
    invalid_instruction_result,
    instruction_result_origin_mismatch,
    operation_result_type_mismatch,
    invalid_instruction_pack_result,
    instruction_pack_result_origin_mismatch,
    duplicate_value_definition,
    missing_value_definition,
    duplicate_value_pack_definition,
    missing_value_pack_definition,
    duplicate_place_definition,
    missing_place_definition,
    invalid_value_function,
    invalid_value_type,
    invalid_value_origin,
    invalid_value_pack_function,
    invalid_value_pack_origin,
    invalid_value_pack_shape,
    empty_pack_values,
    pack_values_evidence_mismatch,
    pack_adjustment_type_mismatch,
    invalid_place_function,
    invalid_place_origin,
    invalid_place_allocation,
    place_used_before_allocation,
    non_dominating_place_allocation,
    invalid_capture_function,
    invalid_capture_value,
    invalid_capture_place,
    capture_slot_origin_mismatch,
    invalid_external_binding_type,
    invalid_operand,
    cross_function_operand,
    invalid_value_pack_operand,
    cross_function_value_pack,
    invalid_place_operand,
    invalid_place_type,
    cross_function_place,
    invalid_pack_adjustment_effects,
    invalid_pack_values_effects,
    invalid_place_read_effects,
    invalid_place_write_effects,
    place_value_type_mismatch,
    understated_table_get_effects,
    understated_table_set_effects,
    invalid_table_set_pack_effects,
    invalid_ambient_environment_mode,
    understated_environment_get_effects,
    understated_environment_set_effects,
    invalid_protected_call_effects,
    invalid_coroutine_create_effects,
    invalid_coroutine_resume_effects,
    invalid_coroutine_yield_effects,
    invalid_numeric_for_next_effects,
    invalid_generic_for_next_effects,
    invalid_table_constructor_effects,
    invalid_string_interpolation_effects,
    invalid_string_interpolation_shape,
    invalid_namecall_effects,
    invalid_iteration_initial_type,
    invalid_iteration_variable_count,
    missing_status_result,
    invalid_status_result_type,
    invalid_coroutine_value_type,
    invalid_result_arity,
    missing_shift_behavior,
    unexpected_shift_behavior,
    invalid_function_reference,
    closure_lexical_parent_mismatch,
    closure_binding_arity_mismatch,
    closure_binding_kind_mismatch,
    closure_binding_type_mismatch,
    call_argument_type_mismatch,
    call_result_type_mismatch,
    call_pack_shape_mismatch,
    invalid_edge_target,
    cross_function_edge,
    edge_argument_arity_mismatch,
    edge_argument_type_mismatch,
    invalid_branch_condition,
    invalid_terminator_value,
    conflicting_error_levels,
    invalid_instruction_claim,
    duplicate_instruction_claim,
    instruction_claim_subject_mismatch,
    unlisted_instruction_claim,
    invalid_evidence_reference,
    invalid_evidence_record,
    missing_emission_evidence,
    invalid_solver_term_reference,
    invalid_solver_value_definition,
    invalid_dynamic_truthiness_operand,
    invalid_dynamic_number_operand,
    invalid_semantic_atom_reference,
    solver_term_not_topological,
    invalid_solver_sort,
    solver_sort_mismatch,
    invalid_constraint_predicate,
    invalid_constraint_scope,
    invalid_constraint_path_rewrite,
    invalid_structural_derivation,
    scoped_constraint_without_evidence,
    invalid_query_reference,
    duplicate_query_assumption,
    solver_precondition_not_assumed,
    invalid_query_path_rewrite,
    solver_unknown,
    invalid_solver_model_reference,
    irrelevant_solver_model_term,
    invalid_solver_model_value,
    duplicate_solver_model_term,
    contradictory_solver_model,
    incomplete_solver_model,
    noncanonical_solver_model_evidence,
    invalid_unsat_core_reference,
    invalid_unsat_core_constraint,
    unsat_core_constraint_without_evidence,
    duplicate_unsat_core_constraint,
    contradictory_unsat_core,
    incomplete_unsat_core,
    noncanonical_unsat_core_evidence,
    invalid_certificate_reference,
    certificate_artifact_mismatch,
    certificate_without_artifact,
    certificate_without_proof,
    noncanonical_certificate_evidence,
    certificate_digest_mismatch,
    certificate_replay_mismatch,
    certificate_resolution_mismatch,
    claim_certificate_evidence_mismatch,
    invalid_edge_rewrite,
    contradictory_solver_proof,
    invalid_claim_reference,
    invalid_claim_query_reference,
    proved_claim_without_proof,
    claim_purpose_subject_mismatch,
    claim_predicate_purpose_mismatch,
    claim_effect_summary_mismatch,
    understated_call_effects,
    understated_operator_effects,
    unproved_primitive_operator_domain,
    required_claim_unproved,
    invalid_obligation_reference,
    invalid_control_branch_witness,
    invalid_obligation_requirement_reference,
    invalid_obligation_query_reference,
    obligation_query_requirement_mismatch,
    obligation_query_subject_mismatch,
    invalid_obligation_certificate_reference,
    obligation_certificate_resolution_mismatch,
    obligation_certificate_evidence_mismatch,
    discharged_obligation_without_proof,
    open_profile_obligation,
    unknown_effects,
    variadic_result_arity,
    unsupported_readable_result_arity,
    unsupported_readable_return_count,
    unsupported_readable_syntax_depth,
    unsupported_readable_register_pressure,
    unsupported_readable_temporary_register_pressure,
    unsupported_readable_upvalue_pressure,
    unsupported_readable_child_prototype_count,
    unsupported_readable_jump_distance,
    invalid_integer_literal,
    invalid_number_literal,
    inexact_luau_integer_literal,
    invalid_solver_numeral,
    unsupported_readable_control_flow,
    irreducible_control_entry,
    irreducible_entry_has_instructions,
    irreducible_entry_parameter_contract,
    irreducible_entry_edge_contract,
    irreducible_entry_nonprimary_successor,
    loop_local_value_requires_transfer,
    duplicate_function_block,
    unlisted_function_block,
    duplicate_block_instruction,
    unlisted_block_instruction,
    value_used_before_definition,
    non_dominating_value_use,
    value_pack_used_before_definition,
    non_dominating_value_pack_use,
    entry_block_has_parameters,
    unsupported_readable_terminator,
    unsupported_readable_error_location,
    unsupported_readable_bit_operation,
    unsupported_readable_pack_operation,
    unsupported_readable_iteration_protocol,
    unsupported_readable_namecall,
};

pub const Detail = union(enum) {
    none,
    solver_unknown: struct {
        engine: ir.SolverEngine,
        phase: SolverUnknownPhase,
        reason: solver_backend.UnknownReason,
    },
};

pub const SolverUnknownPhase = enum {
    query_resolution,
    unsat_core_replay,
};

pub const Diagnostic = struct {
    code: Code,
    entity_index: ?u32 = null,
    detail: Detail = .none,
};

pub const Report = struct {
    allocator: std.mem.Allocator,
    diagnostics: std.ArrayList(Diagnostic) = .empty,

    pub fn init(allocator: std.mem.Allocator) Report {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Report) void {
        self.diagnostics.deinit(self.allocator);
    }

    pub fn isClean(self: *const Report) bool {
        for (self.diagnostics.items) |diagnostic| {
            if (diagnostic.code != .solver_unknown) return false;
        }
        return true;
    }

    pub fn contains(self: *const Report, code: Code) bool {
        for (self.diagnostics.items) |diagnostic| {
            if (diagnostic.code == code) return true;
        }
        return false;
    }

    pub fn add(self: *Report, code: Code, entity_index: ?usize) !void {
        std.debug.assert(code != .solver_unknown);
        try self.diagnostics.append(self.allocator, .{
            .code = code,
            .entity_index = if (entity_index) |index| @intCast(index) else null,
        });
    }

    pub fn addSolverUnknown(
        self: *Report,
        query: ir.QueryId,
        engine: ir.SolverEngine,
        reason: solver_backend.UnknownReason,
    ) !void {
        return self.addSolverUnknownForPhase(query, engine, .query_resolution, reason);
    }

    pub fn addSolverUnknownForPhase(
        self: *Report,
        query: ir.QueryId,
        engine: ir.SolverEngine,
        phase: SolverUnknownPhase,
        reason: solver_backend.UnknownReason,
    ) !void {
        try self.diagnostics.append(self.allocator, .{
            .code = .solver_unknown,
            .entity_index = @intCast(query.index()),
            .detail = .{ .solver_unknown = .{
                .engine = engine,
                .phase = phase,
                .reason = reason,
            } },
        });
    }

    pub fn append(self: *Report, other: *const Report) !void {
        try self.diagnostics.appendSlice(self.allocator, other.diagnostics.items);
    }
};

test "solver unknown diagnostics are typed and non-blocking" {
    var report = Report.init(std.testing.allocator);
    defer report.deinit();
    try report.addSolverUnknown(
        ir.QueryId.fromIndex(3),
        .internal_facts,
        .bounded_internal_incompleteness,
    );

    try std.testing.expect(report.isClean());
    try std.testing.expect(report.contains(.solver_unknown));
    try std.testing.expectEqual(@as(?u32, 3), report.diagnostics.items[0].entity_index);
    try std.testing.expectEqual(SolverUnknownPhase.query_resolution, report.diagnostics.items[0].detail.solver_unknown.phase);
    try std.testing.expectEqual(
        solver_backend.UnknownReason.bounded_internal_incompleteness,
        report.diagnostics.items[0].detail.solver_unknown.reason,
    );
}
