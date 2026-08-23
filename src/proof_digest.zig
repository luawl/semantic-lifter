const std = @import("std");
const ir = @import("ir.zig");
const proof_closure = @import("proof_closure.zig");
const edge_path = @import("edge_path.zig");

pub const prefix = "sha256:lifter-proof-v2:";
pub const external_binding_prefix = "sha256:lifter-proof-v3:";
pub const lexical_binding_prefix = "sha256:lifter-proof-v4:";
pub const runtime_value_prefix = "sha256:lifter-proof-v5:";
pub const combined_runtime_prefix = "sha256:lifter-proof-v6:";
pub const legacy_control_branch_prefix = "sha256:lifter-proof-v7:";
pub const obligation_prefix = "sha256:lifter-proof-v8:";
pub const control_branch_prefix = "sha256:lifter-proof-v9:";
pub const legacy_prefix = "sha256:lifter-proof-v1:";

const EdgeSourceWitness = struct {
    source: ir.BlockId,
    function: ir.FunctionId,
    kind: ir.CfgEdgeKind,
    parameters: []const ir.ValueId,
    instructions: []const ir.InstructionId,
    branch_condition: ?ir.ValueId,
    evidence: []const ir.EvidenceId,
};

const DigestRecord = struct {
    contract: []const u8 = "lifter-proof-v2",
    schema_version: ir.SchemaVersion,
    program_id: []const u8,
    values: []const ir.Value,
    instructions: []const ir.Instruction,
    blocks: []const ir.Block,
    evidence_records: []const ir.Evidence,
    solver_terms: []const ir.SolverTerm,
    constraints: []const ir.Constraint,
    edge_sources: []const EdgeSourceWitness,
    edge_rewrites: []const ir.CfgEdgeRewrite,
    rewrite_certificates: []const ir.SolverCertificate,
    query: ir.SolverQuery,
    engine: ir.SolverEngine,
    resolution: ir.SolverResolution,
    proof_evidence: []const ir.EvidenceId,
    model: []const ir.SolverModelBinding,
    unsat_core: []const ir.ConstraintId,
};

const LexicalBindingWitness = struct {
    entry_function: ir.FunctionId,
    entry_bindings: []const ir.ExternalBindingId,
    external_bindings: []const ir.ExternalBinding,
    functions: []const ir.Function,
    capture_values: []const ir.Value,
    value_packs: []const ir.ValuePack,
    places: []const ir.Place,
    captures: []const ir.Capture,
    closure_instructions: []const ir.Instruction,
    evidence_records: []const ir.Evidence,
};

const LexicalDigestRecord = struct {
    contract: []const u8 = "lifter-proof-v4-lexical-bindings",
    schema_version: ir.SchemaVersion,
    program_id: []const u8,
    lexical_binding_witness: LexicalBindingWitness,
    values: []const ir.Value,
    instructions: []const ir.Instruction,
    blocks: []const ir.Block,
    evidence_records: []const ir.Evidence,
    solver_terms: []const ir.SolverTerm,
    constraints: []const ir.Constraint,
    edge_sources: []const EdgeSourceWitness,
    edge_rewrites: []const ir.CfgEdgeRewrite,
    rewrite_certificates: []const ir.SolverCertificate,
    query: ir.SolverQuery,
    engine: ir.SolverEngine,
    resolution: ir.SolverResolution,
    proof_evidence: []const ir.EvidenceId,
    model: []const ir.SolverModelBinding,
    unsat_core: []const ir.ConstraintId,
};

const RuntimeValueDigestRecord = struct {
    contract: []const u8 = "lifter-proof-v5-runtime-values",
    schema_version: ir.SchemaVersion,
    program_id: []const u8,
    runtime_value_witness: LexicalBindingWitness,
    values: []const ir.Value,
    instructions: []const ir.Instruction,
    blocks: []const ir.Block,
    evidence_records: []const ir.Evidence,
    solver_terms: []const ir.SolverTerm,
    constraints: []const ir.Constraint,
    edge_sources: []const EdgeSourceWitness,
    edge_rewrites: []const ir.CfgEdgeRewrite,
    rewrite_certificates: []const ir.SolverCertificate,
    query: ir.SolverQuery,
    engine: ir.SolverEngine,
    resolution: ir.SolverResolution,
    proof_evidence: []const ir.EvidenceId,
    model: []const ir.SolverModelBinding,
    unsat_core: []const ir.ConstraintId,
};

const CombinedRuntimeDigestRecord = struct {
    contract: []const u8 = "lifter-proof-v6-lexical-runtime-values",
    schema_version: ir.SchemaVersion,
    program_id: []const u8,
    combined_runtime_witness: LexicalBindingWitness,
    values: []const ir.Value,
    instructions: []const ir.Instruction,
    blocks: []const ir.Block,
    evidence_records: []const ir.Evidence,
    solver_terms: []const ir.SolverTerm,
    constraints: []const ir.Constraint,
    edge_sources: []const EdgeSourceWitness,
    edge_rewrites: []const ir.CfgEdgeRewrite,
    rewrite_certificates: []const ir.SolverCertificate,
    query: ir.SolverQuery,
    engine: ir.SolverEngine,
    resolution: ir.SolverResolution,
    proof_evidence: []const ir.EvidenceId,
    model: []const ir.SolverModelBinding,
    unsat_core: []const ir.ConstraintId,
};

const ControlBranchSubjectWitness = struct {
    subject: ir.ControlBranchSubject,
    block: ir.Block,
};

const ObligationSubjectWitness = union(enum) {
    program: void,
    function: ir.Function,
    block: ir.Block,
    instruction: ir.Instruction,
    value: ir.Value,
    value_pack: ir.ValuePack,
    place: ir.Place,
    capture: ir.Capture,
    external_binding: ir.ExternalBinding,
    control_branch: ControlBranchSubjectWitness,
};

const ObligationProofWitness = struct {
    id: ir.ObligationId,
    kind: ir.ObligationKind,
    subject: ObligationSubjectWitness,
    blocks_profile: ir.AdmissionProfile,
    evidence: []const ir.EvidenceId,
    requirement: ir.ObligationRequirement,
    query: ir.QueryId,
};

const DependencyWitnessKind = enum {
    none,
    lexical_bindings,
    runtime_values,
    combined_runtime,
};

const ObligationDigestRecord = struct {
    contract: []const u8,
    proof: DigestRecord,
    dependency_kind: DependencyWitnessKind,
    dependency_witness: LexicalBindingWitness,
    obligations: []const ObligationProofWitness,
};

pub fn computeAlloc(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    query: ir.SolverQuery,
    engine: ir.SolverEngine,
    resolution: ir.SolverResolution,
    proof_evidence: []const ir.EvidenceId,
    model: []const ir.SolverModelBinding,
    unsat_core: []const ir.ConstraintId,
) (error{InvalidDigestInput} || std.mem.Allocator.Error)![]u8 {
    var closure = proof_closure.Closure.init(allocator, program, query, proof_evidence, model) catch |err| switch (err) {
        error.InvalidClosureInput => return error.InvalidDigestInput,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer closure.deinit();

    var obligation_witnesses: std.ArrayList(ObligationProofWitness) = .empty;
    defer obligation_witnesses.deinit(allocator);
    var has_control_branch_obligation = false;
    for (program.obligations) |obligation| {
        if (obligation.query == null or obligation.query.? != query.id) continue;
        const requirement = obligation.requirement orelse return error.InvalidDigestInput;
        if (requirement.kind != query.kind or requirement.predicate != query.goal or
            !evidenceCovers(proof_evidence, obligation.evidence)) return error.InvalidDigestInput;
        for (obligation.evidence) |evidence_id| {
            if (evidence_id.index() >= program.evidence.len) return error.InvalidDigestInput;
            closure.evidence[evidence_id.index()] = true;
        }
        const subject = try obligationSubjectWitness(program, obligation.subject);
        try markSubjectEvidence(program, &closure, subject);
        switch (subject) {
            .control_branch => has_control_branch_obligation = true,
            else => {},
        }
        try obligation_witnesses.append(allocator, .{
            .id = obligation.id,
            .kind = obligation.kind,
            .subject = subject,
            .blocks_profile = obligation.blocks_profile,
            .evidence = obligation.evidence,
            .requirement = requirement,
            .query = query.id,
        });
    }

    var constraints: std.ArrayList(ir.Constraint) = .empty;
    defer constraints.deinit(allocator);
    for (query.assumptions) |constraint_id| {
        if (constraint_id.index() >= program.constraints.len) return error.InvalidDigestInput;
        try constraints.append(allocator, program.constraints[constraint_id.index()]);
    }

    var edge_sources: std.ArrayList(EdgeSourceWitness) = .empty;
    defer edge_sources.deinit(allocator);
    for (constraints.items) |constraint| switch (constraint.scope) {
        .edge => |edge| try appendEdgeSourceWitness(allocator, &edge_sources, program, edge.source, edge.kind),
        .explicit_only, .program, .function, .block => {},
    };
    for (query.path_rewrites) |rewrite_id| {
        if (rewrite_id.index() >= program.edge_rewrites.len) return error.InvalidDigestInput;
        const rewrite = program.edge_rewrites[rewrite_id.index()];
        if (rewrite.id != rewrite_id) return error.InvalidDigestInput;
        try appendEdgeSourceWitness(allocator, &edge_sources, program, rewrite.source, rewrite.kind);
    }

    var values: std.ArrayList(ir.Value) = .empty;
    defer values.deinit(allocator);
    for (program.values, 0..) |value, value_index| {
        if (closure.values[value_index]) try values.append(allocator, value);
    }
    var instructions: std.ArrayList(ir.Instruction) = .empty;
    defer instructions.deinit(allocator);
    for (program.instructions, 0..) |instruction, instruction_index| {
        if (closure.instructions[instruction_index]) try instructions.append(allocator, instruction);
    }
    var blocks: std.ArrayList(ir.Block) = .empty;
    defer blocks.deinit(allocator);
    for (program.blocks, 0..) |block, block_index| {
        if (closure.blocks[block_index]) try blocks.append(allocator, block);
    }
    var evidence_records: std.ArrayList(ir.Evidence) = .empty;
    defer evidence_records.deinit(allocator);
    for (program.evidence, 0..) |evidence, evidence_index| {
        if (closure.evidence[evidence_index] or edgeSourcesUseEvidence(edge_sources.items, evidence.id)) {
            try evidence_records.append(allocator, evidence);
        }
    }
    var solver_terms: std.ArrayList(ir.SolverTerm) = .empty;
    defer solver_terms.deinit(allocator);
    for (program.solver_terms, 0..) |term, term_index| {
        if (closure.terms[term_index]) try solver_terms.append(allocator, term);
    }
    var edge_rewrites: std.ArrayList(ir.CfgEdgeRewrite) = .empty;
    defer edge_rewrites.deinit(allocator);
    var rewrite_certificates: std.ArrayList(ir.SolverCertificate) = .empty;
    defer rewrite_certificates.deinit(allocator);
    for (program.edge_rewrites, 0..) |rewrite, rewrite_index| {
        if (!closure.edge_rewrites[rewrite_index]) continue;
        try edge_rewrites.append(allocator, rewrite);
        const certificate_id = rewrite.certificate orelse {
            if (rewrite.rule != .forwarding_jump and rewrite.rule != .node_split and rewrite.rule != .clone_fold) return error.InvalidDigestInput;
            continue;
        };
        if (certificate_id.index() >= program.certificates.len) return error.InvalidDigestInput;
        var has_certificate = false;
        for (rewrite_certificates.items) |existing| {
            if (existing.id == certificate_id) {
                has_certificate = true;
                break;
            }
        }
        if (!has_certificate) try rewrite_certificates.append(allocator, program.certificates[certificate_id.index()]);
    }

    const uses_lexical_bindings = closure.lexical_witness;
    const uses_runtime_values = closure.runtime_value_witness;
    const uses_combined_runtime = closure.combined_runtime_witness;
    const uses_dependency_witness = uses_lexical_bindings or uses_runtime_values or uses_combined_runtime;
    var functions: std.ArrayList(ir.Function) = .empty;
    defer functions.deinit(allocator);
    var capture_values: std.ArrayList(ir.Value) = .empty;
    defer capture_values.deinit(allocator);
    var value_packs: std.ArrayList(ir.ValuePack) = .empty;
    defer value_packs.deinit(allocator);
    var places: std.ArrayList(ir.Place) = .empty;
    defer places.deinit(allocator);
    var captures: std.ArrayList(ir.Capture) = .empty;
    defer captures.deinit(allocator);
    var closure_instructions: std.ArrayList(ir.Instruction) = .empty;
    defer closure_instructions.deinit(allocator);
    if (uses_dependency_witness or obligation_witnesses.items.len != 0) {
        for (program.functions, 0..) |function, function_index| {
            if (closure.functions[function_index]) try functions.append(allocator, function);
        }
        for (program.value_packs, 0..) |pack, pack_index| {
            if (closure.value_packs[pack_index]) try value_packs.append(allocator, pack);
        }
        for (program.places, 0..) |place, place_index| {
            if (closure.places[place_index]) try places.append(allocator, place);
        }
        for (program.captures, 0..) |capture, capture_index| {
            if (!closure.captures[capture_index]) continue;
            try captures.append(allocator, capture);
            switch (capture.kind) {
                .immutable_value => |value_id| {
                    if (value_id.index() >= program.values.len) return error.InvalidDigestInput;
                    try capture_values.append(allocator, program.values[value_id.index()]);
                },
                .shared_place => |place_id| if (place_id.index() >= program.places.len) return error.InvalidDigestInput,
            }
        }
        for (program.instructions, 0..) |instruction, instruction_index| {
            if (closure.instructions[instruction_index] and instruction.operation == .make_closure) {
                try closure_instructions.append(allocator, instruction);
            }
        }
    }

    const dependency_witness: LexicalBindingWitness = .{
        .entry_function = program.entry_function,
        .entry_bindings = program.entry_bindings,
        .external_bindings = program.external_bindings,
        .functions = functions.items,
        .capture_values = capture_values.items,
        .value_packs = value_packs.items,
        .places = places.items,
        .captures = captures.items,
        .closure_instructions = closure_instructions.items,
        .evidence_records = evidence_records.items,
    };

    const base_record: DigestRecord = .{
        .schema_version = program.schema_version,
        .program_id = program.program_id,
        .values = values.items,
        .instructions = instructions.items,
        .blocks = blocks.items,
        .evidence_records = evidence_records.items,
        .solver_terms = solver_terms.items,
        .constraints = constraints.items,
        .edge_sources = edge_sources.items,
        .edge_rewrites = edge_rewrites.items,
        .rewrite_certificates = rewrite_certificates.items,
        .query = query,
        .engine = engine,
        .resolution = resolution,
        .proof_evidence = proof_evidence,
        .model = model,
        .unsat_core = unsat_core,
    };
    const dependency_kind: DependencyWitnessKind = if (uses_combined_runtime)
        .combined_runtime
    else if (uses_lexical_bindings)
        .lexical_bindings
    else if (uses_runtime_values)
        .runtime_values
    else
        .none;

    const encoded = if (obligation_witnesses.items.len != 0)
        try std.json.Stringify.valueAlloc(allocator, ObligationDigestRecord{
            .contract = if (has_control_branch_obligation)
                "lifter-proof-v9-control-branch-obligations"
            else
                "lifter-proof-v8-obligations",
            .proof = base_record,
            .dependency_kind = dependency_kind,
            .dependency_witness = dependency_witness,
            .obligations = obligation_witnesses.items,
        }, .{})
    else if (uses_combined_runtime)
        try std.json.Stringify.valueAlloc(allocator, CombinedRuntimeDigestRecord{
            .schema_version = program.schema_version,
            .program_id = program.program_id,
            .combined_runtime_witness = dependency_witness,
            .values = values.items,
            .instructions = instructions.items,
            .blocks = blocks.items,
            .evidence_records = evidence_records.items,
            .solver_terms = solver_terms.items,
            .constraints = constraints.items,
            .edge_sources = edge_sources.items,
            .edge_rewrites = edge_rewrites.items,
            .rewrite_certificates = rewrite_certificates.items,
            .query = query,
            .engine = engine,
            .resolution = resolution,
            .proof_evidence = proof_evidence,
            .model = model,
            .unsat_core = unsat_core,
        }, .{})
    else if (uses_lexical_bindings)
        try std.json.Stringify.valueAlloc(allocator, LexicalDigestRecord{
            .schema_version = program.schema_version,
            .program_id = program.program_id,
            .lexical_binding_witness = dependency_witness,
            .values = values.items,
            .instructions = instructions.items,
            .blocks = blocks.items,
            .evidence_records = evidence_records.items,
            .solver_terms = solver_terms.items,
            .constraints = constraints.items,
            .edge_sources = edge_sources.items,
            .edge_rewrites = edge_rewrites.items,
            .rewrite_certificates = rewrite_certificates.items,
            .query = query,
            .engine = engine,
            .resolution = resolution,
            .proof_evidence = proof_evidence,
            .model = model,
            .unsat_core = unsat_core,
        }, .{})
    else if (uses_runtime_values)
        try std.json.Stringify.valueAlloc(allocator, RuntimeValueDigestRecord{
            .schema_version = program.schema_version,
            .program_id = program.program_id,
            .runtime_value_witness = dependency_witness,
            .values = values.items,
            .instructions = instructions.items,
            .blocks = blocks.items,
            .evidence_records = evidence_records.items,
            .solver_terms = solver_terms.items,
            .constraints = constraints.items,
            .edge_sources = edge_sources.items,
            .edge_rewrites = edge_rewrites.items,
            .rewrite_certificates = rewrite_certificates.items,
            .query = query,
            .engine = engine,
            .resolution = resolution,
            .proof_evidence = proof_evidence,
            .model = model,
            .unsat_core = unsat_core,
        }, .{})
    else
        try std.json.Stringify.valueAlloc(allocator, DigestRecord{
            .schema_version = program.schema_version,
            .program_id = program.program_id,
            .values = values.items,
            .instructions = instructions.items,
            .blocks = blocks.items,
            .evidence_records = evidence_records.items,
            .solver_terms = solver_terms.items,
            .constraints = constraints.items,
            .edge_sources = edge_sources.items,
            .edge_rewrites = edge_rewrites.items,
            .rewrite_certificates = rewrite_certificates.items,
            .query = query,
            .engine = engine,
            .resolution = resolution,
            .proof_evidence = proof_evidence,
            .model = model,
            .unsat_core = unsat_core,
        }, .{});
    defer allocator.free(encoded);

    var digest: [std.crypto.hash.sha2.Sha256.digest_length]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(encoded, &digest, .{});
    const hex = std.fmt.bytesToHex(digest, .lower);
    const selected_prefix = if (has_control_branch_obligation)
        control_branch_prefix
    else if (obligation_witnesses.items.len != 0)
        obligation_prefix
    else if (uses_combined_runtime)
        combined_runtime_prefix
    else if (uses_lexical_bindings)
        lexical_binding_prefix
    else if (uses_runtime_values)
        runtime_value_prefix
    else
        prefix;
    return std.fmt.allocPrint(allocator, "{s}{s}", .{ selected_prefix, hex });
}

fn obligationSubjectWitness(program: *const ir.Program, subject: ir.ObligationSubject) error{InvalidDigestInput}!ObligationSubjectWitness {
    return switch (subject) {
        .program => .{ .program = {} },
        .function => |id| if (id.index() < program.functions.len and program.functions[id.index()].id == id)
            .{ .function = program.functions[id.index()] }
        else
            error.InvalidDigestInput,
        .block => |id| if (id.index() < program.blocks.len and program.blocks[id.index()].id == id)
            .{ .block = program.blocks[id.index()] }
        else
            error.InvalidDigestInput,
        .instruction => |id| if (id.index() < program.instructions.len and program.instructions[id.index()].id == id)
            .{ .instruction = program.instructions[id.index()] }
        else
            error.InvalidDigestInput,
        .value => |id| if (id.index() < program.values.len and program.values[id.index()].id == id)
            .{ .value = program.values[id.index()] }
        else
            error.InvalidDigestInput,
        .value_pack => |id| if (id.index() < program.value_packs.len and program.value_packs[id.index()].id == id)
            .{ .value_pack = program.value_packs[id.index()] }
        else
            error.InvalidDigestInput,
        .place => |id| if (id.index() < program.places.len and program.places[id.index()].id == id)
            .{ .place = program.places[id.index()] }
        else
            error.InvalidDigestInput,
        .capture => |id| if (id.index() < program.captures.len and program.captures[id.index()].id == id)
            .{ .capture = program.captures[id.index()] }
        else
            error.InvalidDigestInput,
        .external_binding => |id| if (id.index() < program.external_bindings.len and program.external_bindings[id.index()].id == id)
            .{ .external_binding = program.external_bindings[id.index()] }
        else
            error.InvalidDigestInput,
        .control_branch => |value| blk: {
            try validateControlBranchSubject(program, value);
            break :blk .{ .control_branch = .{
                .subject = value,
                .block = program.blocks[value.block.index()],
            } };
        },
    };
}

fn markSubjectEvidence(
    program: *const ir.Program,
    closure: *proof_closure.Closure,
    subject: ObligationSubjectWitness,
) error{InvalidDigestInput}!void {
    const evidence: []const ir.EvidenceId = switch (subject) {
        .program, .value => &.{},
        .function => |record| record.evidence,
        .block => |record| record.evidence,
        .instruction => |record| record.evidence,
        .value_pack => |record| record.evidence,
        .place => |record| record.evidence,
        .capture => |record| record.evidence,
        .external_binding => |record| record.evidence,
        .control_branch => |record| record.block.evidence,
    };
    for (evidence) |evidence_id| {
        if (evidence_id.index() >= program.evidence.len) return error.InvalidDigestInput;
        closure.evidence[evidence_id.index()] = true;
    }
}

fn evidenceCovers(available: []const ir.EvidenceId, required: []const ir.EvidenceId) bool {
    for (required) |required_id| {
        var found = false;
        for (available) |available_id| {
            if (available_id == required_id) {
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}

fn validateControlBranchSubject(program: *const ir.Program, subject: ir.ControlBranchSubject) error{InvalidDigestInput}!void {
    if (subject.block.index() >= program.blocks.len or subject.branch.condition.index() >= program.values.len) {
        return error.InvalidDigestInput;
    }
    inline for (.{ subject.branch.then_edge, subject.branch.else_edge }) |edge| {
        if (edge.target.index() >= program.blocks.len) return error.InvalidDigestInput;
        for (edge.arguments) |argument| if (argument.index() >= program.values.len) return error.InvalidDigestInput;
    }
}

fn appendEdgeSourceWitness(
    allocator: std.mem.Allocator,
    witnesses: *std.ArrayList(EdgeSourceWitness),
    program: *const ir.Program,
    source_id: ir.BlockId,
    kind: ir.CfgEdgeKind,
) (error{InvalidDigestInput} || std.mem.Allocator.Error)!void {
    for (witnesses.items) |witness| {
        if (witness.source == source_id and witness.kind == kind) return;
    }
    if (source_id.index() >= program.blocks.len) return error.InvalidDigestInput;
    const source = program.blocks[source_id.index()];
    if (source.id != source_id) return error.InvalidDigestInput;
    if (source.function.index() >= program.functions.len) return error.InvalidDigestInput;
    for (source.parameters) |parameter_id| if (parameter_id.index() >= program.values.len) return error.InvalidDigestInput;
    for (source.instructions) |instruction_id| if (instruction_id.index() >= program.instructions.len) return error.InvalidDigestInput;
    for (source.evidence) |evidence_id| if (evidence_id.index() >= program.evidence.len) return error.InvalidDigestInput;
    const condition: ?ir.ValueId = switch (kind) {
        .jump => switch (source.terminator) {
            .jump => null,
            else => return error.InvalidDigestInput,
        },
        .branch_then, .branch_else => switch (source.terminator) {
            .branch => |branch| branch.condition,
            .jump => edge_path.witnessedBranchCondition(program, source_id) orelse return error.InvalidDigestInput,
            else => return error.InvalidDigestInput,
        },
    };
    if (condition) |value_id| if (value_id.index() >= program.values.len) return error.InvalidDigestInput;
    try witnesses.append(allocator, .{
        .source = source.id,
        .function = source.function,
        .kind = kind,
        .parameters = source.parameters,
        .instructions = source.instructions,
        .branch_condition = condition,
        .evidence = source.evidence,
    });
}

fn edgeSourcesUseEvidence(witnesses: []const EdgeSourceWitness, evidence_id: ir.EvidenceId) bool {
    for (witnesses) |witness| {
        for (witness.evidence) |candidate| if (candidate == evidence_id) return true;
    }
    return false;
}

pub fn isFrameworkDigest(value: []const u8) bool {
    return std.mem.startsWith(u8, value, prefix) or
        std.mem.startsWith(u8, value, external_binding_prefix) or
        std.mem.startsWith(u8, value, lexical_binding_prefix) or
        std.mem.startsWith(u8, value, runtime_value_prefix) or
        std.mem.startsWith(u8, value, combined_runtime_prefix) or
        std.mem.startsWith(u8, value, legacy_control_branch_prefix) or
        std.mem.startsWith(u8, value, obligation_prefix) or
        std.mem.startsWith(u8, value, control_branch_prefix);
}

pub fn isControlBranchDigest(value: []const u8) bool {
    return std.mem.startsWith(u8, value, legacy_control_branch_prefix) or
        std.mem.startsWith(u8, value, control_branch_prefix);
}

pub fn isLegacyFrameworkDigest(value: []const u8) bool {
    return std.mem.startsWith(u8, value, legacy_prefix);
}

test "lexical binding proof digests preserve v2 and bind external identity" {
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    };

    var capture_free_program = @import("fixtures.zig").arithmetic_module.program;
    capture_free_program.solver_terms = &terms;
    const v2 = try computeAlloc(std.testing.allocator, &capture_free_program, query, .internal_facts, .proved, &.{}, &.{}, &.{});
    defer std.testing.allocator.free(v2);
    try std.testing.expect(std.mem.startsWith(u8, v2, prefix));
    try std.testing.expect(!std.mem.startsWith(u8, v2, external_binding_prefix));
    try std.testing.expect(!std.mem.startsWith(u8, v2, lexical_binding_prefix));

    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const binding_first = ir.ExternalBindingId.fromIndex(0);
    const binding_second = ir.ExternalBindingId.fromIndex(1);
    const value_first = ir.ValueId.fromIndex(0);
    const value_second = ir.ValueId.fromIndex(1);
    const value_third = ir.ValueId.fromIndex(2);
    const value_fourth = ir.ValueId.fromIndex(3);
    const capture_first = ir.CaptureId.fromIndex(0);
    const capture_second = ir.CaptureId.fromIndex(1);
    const capture_third = ir.CaptureId.fromIndex(2);
    const capture_fourth = ir.CaptureId.fromIndex(3);
    const values = [_]ir.Value{
        .{ .id = value_first, .function = function_id, .type = .integer, .origin = .{ .capture = capture_first } },
        .{ .id = value_second, .function = function_id, .type = .integer, .origin = .{ .capture = capture_second } },
        .{ .id = value_third, .function = function_id, .type = .integer, .origin = .{ .capture = capture_third } },
        .{ .id = value_fourth, .function = function_id, .type = .integer, .origin = .{ .capture = capture_fourth } },
    };
    const captures = [_]ir.Capture{
        .{ .id = capture_first, .function = function_id, .kind = .{ .immutable_value = value_first }, .evidence = &.{evidence_id} },
        .{ .id = capture_second, .function = function_id, .kind = .{ .immutable_value = value_second }, .evidence = &.{evidence_id} },
        .{ .id = capture_third, .function = function_id, .kind = .{ .immutable_value = value_third }, .evidence = &.{evidence_id} },
        .{ .id = capture_fourth, .function = function_id, .kind = .{ .immutable_value = value_fourth }, .evidence = &.{evidence_id} },
    };
    const external_bindings = [_]ir.ExternalBinding{
        .{ .id = binding_first, .kind = .immutable_value, .type = .integer, .evidence = &.{evidence_id} },
        .{ .id = binding_second, .kind = .immutable_value, .type = .integer, .evidence = &.{evidence_id} },
    };
    const entry_bindings = [_]ir.ExternalBindingId{ binding_first, binding_first, binding_second, binding_second };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .terminator = .{ .return_values = &.{ value_first, value_second, value_third, value_fourth } },
        .evidence = &.{evidence_id},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .captures = &.{ capture_first, capture_second, capture_third, capture_fourth },
        .blocks = &.{block_id},
        .entry_block = block_id,
        .evidence = &.{evidence_id},
    }};
    var evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .frontend_proof,
        .locator = "fixture:external-binding-digest",
    }};
    var program: ir.Program = .{
        .program_id = "external-binding-digest",
        .entry_function = function_id,
        .entry_bindings = &entry_bindings,
        .external_bindings = &external_bindings,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .captures = &captures,
        .evidence = &evidence,
        .solver_terms = &terms,
    };

    const v4 = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{}, &.{}, &.{});
    defer std.testing.allocator.free(v4);
    try std.testing.expect(std.mem.startsWith(u8, v4, lexical_binding_prefix));
    try std.testing.expect(isFrameworkDigest(v4));

    const swapped_entry_bindings = [_]ir.ExternalBindingId{ binding_second, binding_second, binding_first, binding_first };
    program.entry_bindings = &swapped_entry_bindings;
    const swapped = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{}, &.{}, &.{});
    defer std.testing.allocator.free(swapped);
    try std.testing.expect(!std.mem.eql(u8, v4, swapped));

    program.entry_bindings = &entry_bindings;
    evidence[0].locator = "fixture:external-binding-digest-changed";
    const changed_evidence = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{}, &.{}, &.{});
    defer std.testing.allocator.free(changed_evidence);
    try std.testing.expect(!std.mem.eql(u8, v4, changed_evidence));

    const join_id = ir.BlockId.fromIndex(1);
    const joined_value = ir.ValueId.fromIndex(values.len);
    const combined_values = values ++ [_]ir.Value{.{
        .id = joined_value,
        .function = function_id,
        .type = .integer,
        .origin = .{ .block_parameter = .{ .block = join_id, .index = 0 } },
    }};
    const combined_blocks = [_]ir.Block{
        .{
            .id = block_id,
            .function = function_id,
            .terminator = .{ .jump = .{ .target = join_id, .arguments = &.{value_first} } },
            .evidence = &.{evidence_id},
        },
        .{
            .id = join_id,
            .function = function_id,
            .parameters = &.{joined_value},
            .terminator = .{ .return_values = &.{joined_value} },
            .evidence = &.{evidence_id},
        },
    };
    const combined_functions = [_]ir.Function{.{
        .id = function_id,
        .captures = &.{ capture_first, capture_second, capture_third, capture_fourth },
        .blocks = &.{ block_id, join_id },
        .entry_block = block_id,
        .evidence = &.{evidence_id},
    }};
    const combined_terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = joined_value } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const combined_query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(1),
    };
    var combined_program = program;
    combined_program.entry_bindings = &entry_bindings;
    combined_program.functions = &combined_functions;
    combined_program.blocks = &combined_blocks;
    combined_program.values = &combined_values;
    combined_program.solver_terms = &combined_terms;
    const combined = try computeAlloc(std.testing.allocator, &combined_program, combined_query, .internal_facts, .proved, &.{}, &.{}, &.{});
    defer std.testing.allocator.free(combined);
    try std.testing.expect(std.mem.startsWith(u8, combined, combined_runtime_prefix));

    combined_program.entry_bindings = &swapped_entry_bindings;
    const remapped_combined = try computeAlloc(std.testing.allocator, &combined_program, combined_query, .internal_facts, .proved, &.{}, &.{}, &.{});
    defer std.testing.allocator.free(remapped_combined);
    try std.testing.expect(!std.mem.eql(u8, combined, remapped_combined));
}

test "lexical proof digests bind capture sources without unrelated graph records" {
    const fixture = @import("fixtures.zig").immutable_closure_module;
    const alternate = ir.ValueId.fromIndex(fixture.values.len);
    const unrelated_evidence = ir.EvidenceId.fromIndex(fixture.evidence.len);
    const values = fixture.values ++ [_]ir.Value{.{
        .id = alternate,
        .function = fixture.f_factory,
        .type = .integer,
        .origin = .{ .parameter = 1 },
    }};
    var functions = fixture.functions;
    functions[fixture.f_factory.index()].parameters = &.{ fixture.v_base, alternate };
    var evidence = fixture.evidence ++ [_]ir.Evidence{.{
        .id = unrelated_evidence,
        .kind = .dynamic_fixture,
        .locator = "fixture:unrelated-lexical-evidence",
    }};
    var instructions = fixture.instructions;
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
    program.functions = &functions;
    program.instructions = &instructions;
    program.values = &values;
    program.evidence = &evidence;
    program.solver_terms = &terms;

    const first = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    try std.testing.expect(std.mem.startsWith(u8, first, lexical_binding_prefix));

    instructions[fixture.i_make_adder.index()].operation.make_closure.bindings = &.{.{ .value = alternate }};
    const changed_source = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(changed_source);
    try std.testing.expect(!std.mem.eql(u8, first, changed_source));

    instructions = fixture.instructions;
    functions[fixture.f_entry.index()].name_hint = "unrelated_entry";
    evidence[unrelated_evidence.index()].locator = "fixture:changed-unrelated-lexical-evidence";
    const unrelated_change = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(unrelated_change);
    try std.testing.expectEqualStrings(first, unrelated_change);
}

test "unrelated captures retain capture-free proof contracts" {
    const fixture = @import("fixtures.zig").immutable_closure_module;
    var functions = fixture.functions;
    const literal_terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .boolean_literal = true },
    }};
    const literal_query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    };
    var program = fixture.program;
    program.functions = &functions;
    program.solver_terms = &literal_terms;

    const literal = try computeAlloc(std.testing.allocator, &program, literal_query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(literal);
    try std.testing.expect(std.mem.startsWith(u8, literal, prefix));
    functions[fixture.f_adder.index()].name_hint = "unrelated_adder";
    const changed_literal = try computeAlloc(std.testing.allocator, &program, literal_query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(changed_literal);
    try std.testing.expectEqualStrings(literal, changed_literal);

    const runtime_terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = fixture.v_export } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const runtime_query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(1),
    };
    program.solver_terms = &runtime_terms;
    const runtime = try computeAlloc(std.testing.allocator, &program, runtime_query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(runtime);
    try std.testing.expect(std.mem.startsWith(u8, runtime, runtime_value_prefix));
    functions[fixture.f_adder.index()].name_hint = "still_unrelated_adder";
    const changed_runtime = try computeAlloc(std.testing.allocator, &program, runtime_query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(changed_runtime);
    try std.testing.expectEqualStrings(runtime, changed_runtime);
}

test "model bindings cannot enlarge the owning query closure" {
    const fixture = @import("fixtures.zig").immutable_closure_module;
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = fixture.v_captured_base } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(0),
        } } },
    };
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(2),
        .evidence = &.{fixture.proof},
    }};
    const model = [_]ir.SolverModelBinding{.{
        .term = ir.SolverTermId.fromIndex(0),
        .value = .{ .integer = "0" },
    }};
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .goal = ir.SolverTermId.fromIndex(1),
    };
    const clean = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(clean);
    try std.testing.expect(std.mem.startsWith(u8, clean, prefix));
    try std.testing.expectError(
        error.InvalidDigestInput,
        computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{fixture.proof}, &model, &.{}),
    );

    const assumed_query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .find_model,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(1),
    };
    const assumed = try computeAlloc(std.testing.allocator, &program, assumed_query, .z3, .proved, &.{fixture.proof}, &model, &.{});
    defer std.testing.allocator.free(assumed);
    try std.testing.expect(std.mem.startsWith(u8, assumed, lexical_binding_prefix));
}

test "instruction semantic proof digests bind direct capture operands" {
    const fixture = @import("fixtures.zig").immutable_closure_module;
    const alternate = ir.ValueId.fromIndex(fixture.values.len);
    const values = fixture.values ++ [_]ir.Value{.{
        .id = alternate,
        .function = fixture.f_factory,
        .type = .integer,
        .origin = .{ .parameter = 1 },
    }};
    var functions = fixture.functions;
    functions[fixture.f_factory.index()].parameters = &.{ fixture.v_base, alternate };
    var instructions = fixture.instructions;
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
    program.functions = &functions;
    program.instructions = &instructions;
    program.values = &values;
    program.solver_terms = &terms;

    const first = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    try std.testing.expect(std.mem.startsWith(u8, first, lexical_binding_prefix));

    var changed_values = values;
    changed_values[fixture.v_captured_base.index()].type = .dynamic;
    program.values = &changed_values;
    const changed_type = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(changed_type);
    try std.testing.expect(!std.mem.eql(u8, first, changed_type));

    program.values = &values;
    instructions[fixture.i_make_adder.index()].operation.make_closure.bindings = &.{.{ .value = alternate }};
    const changed_source = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(changed_source);
    try std.testing.expect(!std.mem.eql(u8, first, changed_source));

    instructions = fixture.instructions;
    var unrelated_functions = functions;
    unrelated_functions[fixture.f_entry.index()].name_hint = "unrelated_entry";
    program.functions = &unrelated_functions;
    const unrelated_change = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(unrelated_change);
    try std.testing.expectEqualStrings(first, unrelated_change);
}

test "instruction semantic proof digests bind direct pack and result shape" {
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

    const first = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    try std.testing.expect(std.mem.startsWith(u8, first, runtime_value_prefix));

    var packs = fixture.value_packs;
    packs[fixture.p_results.index()].shape = .{ .prefix = &.{ir.ValueType.integer}, .tail = .open };
    program.value_packs = &packs;
    const changed_pack = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(changed_pack);
    try std.testing.expect(!std.mem.eql(u8, first, changed_pack));

    program.value_packs = &fixture.value_packs;
    var values = fixture.values;
    values[fixture.v_first.index()].type = .integer;
    program.values = &values;
    const changed_result = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(changed_result);
    try std.testing.expect(!std.mem.eql(u8, first, changed_result));
}

test "zero-result instruction semantics bind local place identity without unrelated captures" {
    const fixture = @import("fixtures.zig").shared_place_closure_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .semantic_atom = .{ .instruction_effects = fixture.i_initialize } },
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(0),
    };
    var instructions = fixture.instructions;
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;

    const first = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    try std.testing.expect(std.mem.startsWith(u8, first, runtime_value_prefix));

    var places = fixture.places;
    places[fixture.p_state.index()].type = .number;
    program.places = &places;
    const changed_place = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(changed_place);
    try std.testing.expect(!std.mem.eql(u8, first, changed_place));

    program.places = &fixture.places;
    instructions[fixture.i_write.index()].operation.place_write.value = fixture.v_current;
    const unrelated_child_write = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(unrelated_child_write);
    try std.testing.expectEqualStrings(first, unrelated_child_write);
}

test "lexical proof digests bind shared place capture sources" {
    const fixture = @import("fixtures.zig").shared_place_closure_module;
    const alternate_place = ir.PlaceId.fromIndex(fixture.places.len);
    const alternate_value = ir.ValueId.fromIndex(fixture.values.len);
    const values = fixture.values ++ [_]ir.Value{.{
        .id = alternate_value,
        .function = fixture.f_factory,
        .type = .integer,
        .origin = .{ .parameter = 1 },
    }};
    const places = fixture.places ++ [_]ir.Place{.{
        .id = alternate_place,
        .function = fixture.f_factory,
        .type = .integer,
        .origin = .{ .local = 1 },
        .evidence = &.{fixture.proof},
    }};
    var functions = fixture.functions;
    functions[fixture.f_factory.index()].parameters = &.{ fixture.v_start, alternate_value };
    functions[fixture.f_factory.index()].local_places = &.{ fixture.p_state, alternate_place };
    var instructions = fixture.instructions;
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
    program.functions = &functions;
    program.instructions = &instructions;
    program.values = &values;
    program.places = &places;
    program.solver_terms = &terms;

    const first = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    try std.testing.expect(std.mem.startsWith(u8, first, combined_runtime_prefix));
    instructions[fixture.i_make_counter.index()].operation.make_closure.bindings = &.{.{ .place = alternate_place }};
    const changed_source = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(changed_source);
    try std.testing.expect(!std.mem.eql(u8, first, changed_source));

    instructions = fixture.instructions;
    instructions[fixture.i_initialize.index()].operation.place_write.value = alternate_value;
    const changed_effect = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(changed_effect);
    try std.testing.expect(!std.mem.eql(u8, first, changed_effect));

    instructions = fixture.instructions;
    instructions[fixture.i_write.index()].operation.place_write.value = fixture.v_current;
    const later_effect = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(later_effect);
    try std.testing.expectEqualStrings(first, later_effect);
}

test "capture-free runtime value proofs bind non-normalized definitions" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const effect_id = ir.InstructionId.fromIndex(0);
    const call_id = ir.InstructionId.fromIndex(1);
    const later_effect_id = ir.InstructionId.fromIndex(2);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const first_callee = ir.ValueId.fromIndex(0);
    const second_callee = ir.ValueId.fromIndex(1);
    const first_state = ir.ValueId.fromIndex(2);
    const second_state = ir.ValueId.fromIndex(3);
    const result_value = ir.ValueId.fromIndex(4);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = first_callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = second_callee, .function = function_id, .type = .function, .origin = .{ .parameter = 1 } },
        .{ .id = first_state, .function = function_id, .type = .integer, .origin = .{ .parameter = 2 } },
        .{ .id = second_state, .function = function_id, .type = .integer, .origin = .{ .parameter = 3 } },
        .{ .id = result_value, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = call_id, .index = 0 } } },
    };
    var value_packs = [_]ir.ValuePack{.{
        .id = pack_id,
        .function = function_id,
        .origin = .{ .varargs = function_id },
        .evidence = &.{evidence_id},
    }};
    var instructions = [_]ir.Instruction{
        .{
            .id = effect_id,
            .block = block_id,
            .operation = .{ .environment_set = .{
                .target = .{ .ambient = {} },
                .name = "state",
                .value = first_state,
            } },
            .results = &.{},
            .effects = .semantic_environment_write,
            .evidence = &.{evidence_id},
        },
        .{
            .id = call_id,
            .block = block_id,
            .operation = .{ .call = .{
                .callee = first_callee,
                .arguments = &.{},
                .argument_pack = pack_id,
                .result_arity = .{ .fixed = 1 },
            } },
            .results = &.{result_value},
            .effects = .dynamic_call,
            .evidence = &.{evidence_id},
        },
        .{
            .id = later_effect_id,
            .block = block_id,
            .operation = .{ .environment_set = .{
                .target = .{ .ambient = {} },
                .name = "later_state",
                .value = first_state,
            } },
            .results = &.{},
            .effects = .semantic_environment_write,
            .evidence = &.{evidence_id},
        },
    };
    const blocks = [_]ir.Block{.{
        .id = block_id,
        .function = function_id,
        .instructions = &.{ effect_id, call_id, later_effect_id },
        .terminator = .{ .return_values = &.{result_value} },
        .evidence = &.{evidence_id},
    }};
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ first_callee, second_callee, first_state, second_state },
        .blocks = &.{block_id},
        .entry_block = block_id,
        .is_variadic = true,
        .vararg_pack = pack_id,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .dynamic_fixture,
        .locator = "fixture:capture-free-runtime-value-proof",
    }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .dynamic_value }, .operation = .{ .value = result_value } },
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
    const program: ir.Program = .{
        .program_id = "capture-free-runtime-value-proof",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .value_packs = &value_packs,
        .evidence = &evidence,
        .solver_terms = &terms,
    };

    const first = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{evidence_id}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    try std.testing.expect(std.mem.startsWith(u8, first, runtime_value_prefix));
    instructions[call_id.index()].operation.call.callee = second_callee;
    const changed = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{evidence_id}, &.{}, &.{});
    defer std.testing.allocator.free(changed);
    try std.testing.expect(!std.mem.eql(u8, first, changed));

    instructions[call_id.index()].operation.call.callee = first_callee;
    value_packs[pack_id.index()].shape = .{ .prefix = &.{ir.ValueType.integer} };
    const changed_pack = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{evidence_id}, &.{}, &.{});
    defer std.testing.allocator.free(changed_pack);
    try std.testing.expect(!std.mem.eql(u8, first, changed_pack));

    value_packs[pack_id.index()].shape = .open_unknown;
    instructions[effect_id.index()].operation.environment_set.value = second_state;
    const changed_effect = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{evidence_id}, &.{}, &.{});
    defer std.testing.allocator.free(changed_effect);
    try std.testing.expect(!std.mem.eql(u8, first, changed_effect));

    instructions[effect_id.index()].operation.environment_set.value = first_state;
    instructions[later_effect_id.index()].operation.environment_set.value = second_state;
    const later_effect = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{evidence_id}, &.{}, &.{});
    defer std.testing.allocator.free(later_effect);
    try std.testing.expectEqualStrings(first, later_effect);
}

test "capture-free runtime value proofs bind incoming block arguments" {
    const function_id = ir.FunctionId.fromIndex(0);
    const entry_id = ir.BlockId.fromIndex(0);
    const join_id = ir.BlockId.fromIndex(1);
    const effect_id = ir.InstructionId.fromIndex(0);
    const left = ir.ValueId.fromIndex(0);
    const right = ir.ValueId.fromIndex(1);
    const joined = ir.ValueId.fromIndex(2);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    var values = [_]ir.Value{
        .{ .id = left, .function = function_id, .type = .integer, .origin = .{ .parameter = 0 } },
        .{ .id = right, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = joined, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = join_id, .index = 0 } } },
    };
    var instructions = [_]ir.Instruction{.{
        .id = effect_id,
        .block = entry_id,
        .operation = .{ .environment_set = .{
            .target = .{ .ambient = {} },
            .name = "incoming",
            .value = left,
        } },
        .results = &.{},
        .effects = .semantic_environment_write,
        .evidence = &.{evidence_id},
    }};
    var blocks = [_]ir.Block{
        .{
            .id = entry_id,
            .function = function_id,
            .instructions = &.{effect_id},
            .terminator = .{ .jump = .{ .target = join_id, .arguments = &.{left} } },
            .evidence = &.{evidence_id},
        },
        .{
            .id = join_id,
            .function = function_id,
            .parameters = &.{joined},
            .terminator = .{ .return_values = &.{joined} },
            .evidence = &.{evidence_id},
        },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ left, right },
        .blocks = &.{ entry_id, join_id },
        .entry_block = entry_id,
        .evidence = &.{evidence_id},
    }};
    const evidence = [_]ir.Evidence{.{
        .id = evidence_id,
        .kind = .dynamic_fixture,
        .locator = "fixture:capture-free-block-argument-proof",
    }};
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .integer }, .operation = .{ .value = joined } },
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
    const program: ir.Program = .{
        .program_id = "capture-free-block-argument-proof",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
        .solver_terms = &terms,
    };

    const first = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{evidence_id}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    try std.testing.expect(std.mem.startsWith(u8, first, runtime_value_prefix));
    blocks[entry_id.index()].terminator.jump.arguments = &.{right};
    const changed_edge = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{evidence_id}, &.{}, &.{});
    defer std.testing.allocator.free(changed_edge);
    try std.testing.expect(!std.mem.eql(u8, first, changed_edge));

    blocks[entry_id.index()].terminator.jump.arguments = &.{left};
    values[right.index()].name_hint = "unrelated_right";
    const unrelated = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{evidence_id}, &.{}, &.{});
    defer std.testing.allocator.free(unrelated);
    try std.testing.expectEqualStrings(first, unrelated);

    values[right.index()].name_hint = null;
    instructions[effect_id.index()].operation.environment_set.value = right;
    const changed_effect = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{evidence_id}, &.{}, &.{});
    defer std.testing.allocator.free(changed_effect);
    try std.testing.expect(!std.mem.eql(u8, first, changed_effect));
}

test "wide normalized constants remain inside proof dependency digests" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var values = fixture.values;
    values[fixture.v_factor.index()].type = .{ .kind = .integer, .bit_width = 128, .signed = false };
    var instructions = fixture.instructions;
    instructions[fixture.i_factor.index()].operation = .{ .constant = .{
        .integer = "340282366920938463463374607431768211455",
    } };
    const bv128: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 128 };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv128, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv128, .operation = .{ .bit_vector_literal = .{
            .value = "340282366920938463463374607431768211455",
            .bit_width = 128,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
    };
    const query: ir.SolverQuery = .{ .id = ir.QueryId.fromIndex(0), .kind = .prove_true, .goal = ir.SolverTermId.fromIndex(2) };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;

    const first = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    instructions[fixture.i_factor.index()].operation.constant.integer = "340282366920938463463374607431768211454";
    const second = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{}, &.{}, &.{});
    defer std.testing.allocator.free(second);
    try std.testing.expect(!std.mem.eql(u8, first, second));
}

test "conditional proof digests bind both selection arms" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = .{ .kind = .boolean }, .operation = .{ .boolean_literal = true } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "11" } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "12" } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .integer }, .operation = .{ .if_then_else = .{
            .condition = ir.SolverTermId.fromIndex(0),
            .then_term = ir.SolverTermId.fromIndex(1),
            .else_term = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = .{ .kind = .integer }, .operation = .{ .integer_literal = "11" } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(3),
            .right = ir.SolverTermId.fromIndex(4),
        } } },
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .goal = ir.SolverTermId.fromIndex(5),
    };
    var program = fixture.program;
    program.solver_terms = &terms;

    const first = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    terms[2].operation.integer_literal = "13";
    const second = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{}, &.{}, &.{});
    defer std.testing.allocator.free(second);
    try std.testing.expect(!std.mem.eql(u8, first, second));
}

test "value-definition proof digests bind the originating instruction" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .modulo,
        .left = fixture.v_sum,
        .right = fixture.v_factor,
    } };
    const integer: ir.SolverSort = .{ .kind = .integer };
    const terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = integer, .operation = .{ .value = fixture.v_sum } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = integer, .operation = .{ .value = fixture.v_factor } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = .{ .kind = .boolean }, .operation = .{ .is_nonzero = ir.SolverTermId.fromIndex(1) } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = integer, .operation = .{ .remainder = .{
            .mode = .integer_floor,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
            .defined_by = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = integer, .operation = .{ .value_definition = .{
            .value = fixture.v_result,
            .expression = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = integer, .operation = .{ .integer_literal = "0" } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(4),
            .right = ir.SolverTermId.fromIndex(5),
        } } },
    };
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(2),
        .evidence = &.{fixture.proof},
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(6),
    };
    var program = fixture.program;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    const first = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    instructions[fixture.i_result.index()].operation.binary.operator = .floor_divide;
    const second = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(second);
    try std.testing.expect(!std.mem.eql(u8, first, second));
}

test "value-definition proof digests bind the selected semantic guard" {
    const fixture = @import("fixtures.zig").arithmetic_module;
    const u32_type: ir.ValueType = .{ .kind = .integer, .bit_width = 32 };
    const bv32: ir.SolverSort = .{ .kind = .bit_vector, .bit_width = 32 };
    var values = fixture.values;
    values[fixture.v_right.index()].type = u32_type;
    values[fixture.v_sum.index()].type = u32_type;
    values[fixture.v_result.index()].type = u32_type;
    var instructions = fixture.instructions;
    instructions[fixture.i_result.index()].operation = .{ .binary = .{
        .operator = .shift_left,
        .left = fixture.v_sum,
        .right = fixture.v_right,
        .mode = .primitive,
        .shift_behavior = .luau_bit32,
    } };
    var terms = [_]ir.SolverTerm{
        .{ .id = ir.SolverTermId.fromIndex(0), .sort = bv32, .operation = .{ .value = fixture.v_sum } },
        .{ .id = ir.SolverTermId.fromIndex(1), .sort = bv32, .operation = .{ .value = fixture.v_right } },
        .{ .id = ir.SolverTermId.fromIndex(2), .sort = bv32, .operation = .{ .bit_vector_literal = .{
            .value = "32",
            .bit_width = 32,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(3), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .less,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(2),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(4), .sort = bv32, .operation = .{ .bit_vector_literal = .{
            .value = "31",
            .bit_width = 32,
        } } },
        .{ .id = ir.SolverTermId.fromIndex(5), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .less_equal,
            .left = ir.SolverTermId.fromIndex(1),
            .right = ir.SolverTermId.fromIndex(4),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(6), .sort = bv32, .operation = .{ .binary = .{
            .operator = .shift_left,
            .left = ir.SolverTermId.fromIndex(0),
            .right = ir.SolverTermId.fromIndex(1),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(7), .sort = bv32, .operation = .{ .value_definition = .{
            .value = fixture.v_result,
            .expression = ir.SolverTermId.fromIndex(6),
            .valid_when = ir.SolverTermId.fromIndex(3),
        } } },
        .{ .id = ir.SolverTermId.fromIndex(8), .sort = .{ .kind = .boolean }, .operation = .{ .binary = .{
            .operator = .equal,
            .left = ir.SolverTermId.fromIndex(7),
            .right = ir.SolverTermId.fromIndex(6),
        } } },
    };
    const constraints = [_]ir.Constraint{
        .{ .id = ir.ConstraintId.fromIndex(0), .predicate = ir.SolverTermId.fromIndex(3), .evidence = &.{fixture.proof} },
        .{ .id = ir.ConstraintId.fromIndex(1), .predicate = ir.SolverTermId.fromIndex(5), .evidence = &.{fixture.proof} },
    };
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{ ir.ConstraintId.fromIndex(0), ir.ConstraintId.fromIndex(1) },
        .goal = ir.SolverTermId.fromIndex(8),
    };
    var program = fixture.program;
    program.values = &values;
    program.instructions = &instructions;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    const first = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    terms[7].operation.value_definition.valid_when = ir.SolverTermId.fromIndex(5);
    const second = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(second);
    try std.testing.expect(!std.mem.eql(u8, first, second));

    terms[7].operation.value_definition.valid_when = ir.SolverTermId.fromIndex(3);
    instructions[fixture.i_result.index()].operation.binary.shift_behavior = .zero_saturating;
    const changed_behavior = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(changed_behavior);
    try std.testing.expect(!std.mem.eql(u8, first, changed_behavior));
}

test "edge-scoped proof digests bind the original target block topology" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = fixture.v_is_negative },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{fixture.proof},
        .scope = .{ .edge = .{
            .source = fixture.b_entry,
            .kind = .branch_then,
            .target = fixture.b_negative,
        } },
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(0),
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;

    const first = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    var blocks = fixture.blocks;
    blocks[fixture.b_negative.index()].terminator = .{ .return_values = &.{fixture.v_negated} };
    program.blocks = &blocks;
    const second = try computeAlloc(std.testing.allocator, &program, query, .internal_facts, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(second);
    try std.testing.expect(!std.mem.eql(u8, first, second));
}

test "path proof digests bind structurally forwarded block instructions" {
    const fixture = @import("fixtures.zig").absolute_value_module;
    const terms = [_]ir.SolverTerm{.{
        .id = ir.SolverTermId.fromIndex(0),
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = fixture.v_is_negative },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = ir.ConstraintId.fromIndex(0),
        .predicate = ir.SolverTermId.fromIndex(0),
        .evidence = &.{fixture.proof},
        .scope = .{ .edge = .{
            .source = fixture.b_entry,
            .kind = .branch_then,
            .target = fixture.b_negative,
        } },
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = ir.EdgeRewriteId.fromIndex(0),
        .source = fixture.b_entry,
        .kind = .branch_then,
        .from = .{ .target = fixture.b_negative },
        .to = .{ .target = fixture.b_join },
        .rule = .forwarding_jump,
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{ir.ConstraintId.fromIndex(0)},
        .path_rewrites = &.{ir.EdgeRewriteId.fromIndex(0)},
        .goal = ir.SolverTermId.fromIndex(0),
    };
    var program = fixture.program;
    program.solver_terms = &terms;
    program.constraints = &constraints;
    program.edge_rewrites = &rewrites;

    const first = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    var instructions = fixture.instructions;
    instructions[fixture.i_negate.index()].effects.may_throw = !instructions[fixture.i_negate.index()].effects.may_throw;
    program.instructions = &instructions;
    const second = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(second);
    try std.testing.expect(!std.mem.eql(u8, first, second));

    var source_blocks = fixture.blocks;
    source_blocks[fixture.b_entry.index()].terminator.branch.condition = fixture.v_input;
    program.instructions = &fixture.instructions;
    program.blocks = &source_blocks;
    const source_changed = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{fixture.proof}, &.{}, &.{});
    defer std.testing.allocator.free(source_changed);
    try std.testing.expect(!std.mem.eql(u8, first, source_changed));
}

test "node split path digests bind cloned parameter mappings" {
    const function_id = ir.FunctionId.fromIndex(0);
    const source = ir.BlockId.fromIndex(0);
    const original = ir.BlockId.fromIndex(1);
    const clone = ir.BlockId.fromIndex(2);
    const exit = ir.BlockId.fromIndex(3);
    const condition = ir.ValueId.fromIndex(0);
    const incoming = ir.ValueId.fromIndex(1);
    const original_parameter = ir.ValueId.fromIndex(2);
    const clone_parameter = ir.ValueId.fromIndex(3);
    const exit_parameter = ir.ValueId.fromIndex(4);
    const evidence_id = ir.EvidenceId.fromIndex(0);
    const term_id = ir.SolverTermId.fromIndex(0);
    const constraint_id = ir.ConstraintId.fromIndex(0);
    const rewrite_id = ir.EdgeRewriteId.fromIndex(0);
    const blocks = [_]ir.Block{
        .{ .id = source, .function = function_id, .terminator = .{ .branch = .{
            .condition = condition,
            .then_edge = .{ .target = clone, .arguments = &.{incoming} },
            .else_edge = .{ .target = exit, .arguments = &.{incoming} },
        } }, .evidence = &.{evidence_id} },
        .{ .id = original, .function = function_id, .parameters = &.{original_parameter}, .terminator = .{ .jump = .{
            .target = exit,
            .arguments = &.{original_parameter},
        } }, .evidence = &.{evidence_id} },
        .{ .id = clone, .function = function_id, .parameters = &.{clone_parameter}, .terminator = .{ .jump = .{
            .target = exit,
            .arguments = &.{clone_parameter},
        } }, .evidence = &.{evidence_id} },
        .{ .id = exit, .function = function_id, .parameters = &.{exit_parameter}, .terminator = .{ .return_values = &.{exit_parameter} }, .evidence = &.{evidence_id} },
    };
    const functions = [_]ir.Function{.{
        .id = function_id,
        .parameters = &.{ condition, incoming },
        .blocks = &.{ source, original, clone, exit },
        .entry_block = source,
        .evidence = &.{evidence_id},
    }};
    const values = [_]ir.Value{
        .{ .id = condition, .function = function_id, .type = .boolean, .origin = .{ .parameter = 0 } },
        .{ .id = incoming, .function = function_id, .type = .integer, .origin = .{ .parameter = 1 } },
        .{ .id = original_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = original, .index = 0 } } },
        .{ .id = clone_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = clone, .index = 0 } } },
        .{ .id = exit_parameter, .function = function_id, .type = .integer, .origin = .{ .block_parameter = .{ .block = exit, .index = 0 } } },
    };
    const evidence = [_]ir.Evidence{.{ .id = evidence_id, .kind = .structural_derivation, .locator = "fixture:node-split-path-digest" }};
    const terms = [_]ir.SolverTerm{.{
        .id = term_id,
        .sort = .{ .kind = .boolean },
        .operation = .{ .value = condition },
    }};
    const constraints = [_]ir.Constraint{.{
        .id = constraint_id,
        .predicate = term_id,
        .evidence = &.{evidence_id},
        .scope = .{ .edge = .{ .source = source, .kind = .branch_then, .target = original } },
    }};
    const rewrites = [_]ir.CfgEdgeRewrite{.{
        .id = rewrite_id,
        .source = source,
        .kind = .branch_then,
        .from = .{ .target = original, .arguments = &.{incoming} },
        .to = .{ .target = clone, .arguments = &.{incoming} },
        .rule = .node_split,
    }};
    const query: ir.SolverQuery = .{
        .id = ir.QueryId.fromIndex(0),
        .kind = .prove_true,
        .assumptions = &.{constraint_id},
        .path_rewrites = &.{rewrite_id},
        .goal = term_id,
    };
    var program: ir.Program = .{
        .program_id = "node-split-path-digest",
        .entry_function = function_id,
        .functions = &functions,
        .blocks = &blocks,
        .instructions = &.{},
        .values = &values,
        .evidence = &evidence,
        .solver_terms = &terms,
        .constraints = &constraints,
        .edge_rewrites = &rewrites,
    };

    const first = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{evidence_id}, &.{}, &.{});
    defer std.testing.allocator.free(first);
    var changed_values = values;
    changed_values[clone_parameter.index()].type = .number;
    program.values = &changed_values;
    const changed_mapping = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{evidence_id}, &.{}, &.{});
    defer std.testing.allocator.free(changed_mapping);
    try std.testing.expect(!std.mem.eql(u8, first, changed_mapping));

    program.values = &values;
    var changed_blocks = blocks;
    changed_blocks[clone.index()].terminator.jump.arguments = &.{original_parameter};
    program.blocks = &changed_blocks;
    const changed_terminator = try computeAlloc(std.testing.allocator, &program, query, .z3, .proved, &.{evidence_id}, &.{}, &.{});
    defer std.testing.allocator.free(changed_terminator);
    try std.testing.expect(!std.mem.eql(u8, first, changed_terminator));
}
