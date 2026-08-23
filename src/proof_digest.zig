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

pub fn isControlBranchDigest(value: []const u8) bool {
    return std.mem.startsWith(u8, value, legacy_control_branch_prefix) or
        std.mem.startsWith(u8, value, control_branch_prefix);
}

pub fn isLegacyFrameworkDigest(value: []const u8) bool {
    return std.mem.startsWith(u8, value, legacy_prefix);
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
