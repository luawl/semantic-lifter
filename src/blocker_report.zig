const std = @import("std");
const ir = @import("ir.zig");
const place_flow = @import("place_flow.zig");

pub const ProducerClass = union(enum) {
    invalid_instruction: void,
    parameter: void,
    block_parameter: void,
    capture: void,
    constant: std.meta.Tag(ir.Literal),
    operation: std.meta.Tag(ir.Operation),

    pub fn label(self: ProducerClass) []const u8 {
        return switch (self) {
            .invalid_instruction => "invalid_instruction",
            .parameter => "parameter",
            .block_parameter => "block_parameter",
            .capture => "capture",
            .constant => |literal| switch (literal) {
                .nil_value => "constant.nil_value",
                .boolean => "constant.boolean",
                .integer => "constant.integer",
                .number => "constant.number",
                .special_number => "constant.special_number",
                .string => "constant.string",
            },
            .operation => |operation| @tagName(operation),
        };
    }
};

pub const InvocationTarget = struct {
    value: ir.ValueId,
    value_type: ir.TypeKind,
    producer: ProducerClass,
    producer_instruction: ?ir.InstructionId,
    evidence: ?ir.EvidenceId,
};

pub const PackResultProjection = struct {
    adjustment: ir.InstructionId,
    result_index: u32,
    pack: ir.ValuePackId,
    producer: ir.InstructionId,
    producer_operation: std.meta.Tag(ir.Operation),
    evidence: ?ir.EvidenceId,
};

pub const PlaceFlowClass = union(enum) {
    none: void,
    unavailable: void,
    entry: void,
    entry_and_writes: void,
    multiple: void,
    unique: ProducerClass,
    pack_projection: struct {
        producer_operation: std.meta.Tag(ir.Operation),
        result_index: u32,
    },
};

pub const ObligationProofLinks = enum {
    none,
    requirement,
    query,
    certificate,
    requirement_query,
    requirement_certificate,
    query_certificate,
    requirement_query_certificate,
};

pub fn obligationProofLinks(obligation: ir.Obligation) ObligationProofLinks {
    const requirement: u3 = if (obligation.requirement != null) 1 else 0;
    const query: u3 = if (obligation.query != null) 2 else 0;
    const certificate: u3 = if (obligation.certificate != null) 4 else 0;
    return switch (requirement | query | certificate) {
        0 => .none,
        1 => .requirement,
        2 => .query,
        3 => .requirement_query,
        4 => .certificate,
        5 => .requirement_certificate,
        6 => .query_certificate,
        7 => .requirement_query_certificate,
    };
}

pub fn obligationProofLinksMatch(obligation: ir.Obligation, expected: []const u8) bool {
    return std.mem.eql(u8, @tagName(obligationProofLinks(obligation)), expected);
}

pub fn placeOriginLabel(origin: ir.PlaceOrigin) []const u8 {
    return switch (origin) {
        .local => "local",
        .instruction => "instruction",
        .capture => "capture",
    };
}

pub fn subjectOperation(program: *const ir.Program, subject: ir.ObligationSubject) []const u8 {
    return switch (subject) {
        .instruction => |instruction_id| if (instruction_id.index() < program.instructions.len)
            @tagName(program.instructions[instruction_id.index()].operation)
        else
            "invalid",
        .block => |block_id| if (block_id.index() < program.blocks.len)
            @tagName(program.blocks[block_id.index()].terminator)
        else
            "invalid",
        .control_branch => "branch",
        else => "none",
    };
}

pub fn subjectIndex(subject: ir.ObligationSubject) ?usize {
    return switch (subject) {
        .program => null,
        .function => |id| id.index(),
        .block => |id| id.index(),
        .instruction => |id| id.index(),
        .value => |id| id.index(),
        .value_pack => |id| id.index(),
        .place => |id| id.index(),
        .capture => |id| id.index(),
        .external_binding => |id| id.index(),
        .control_branch => |control| control.block.index(),
    };
}

pub fn preferredEvidence(program: *const ir.Program, evidence: []const ir.EvidenceId) ?ir.EvidenceId {
    var fallback: ?ir.EvidenceId = null;
    for (evidence) |evidence_id| {
        if (evidence_id.index() >= program.evidence.len) continue;
        if (fallback == null) fallback = evidence_id;
        if (program.evidence[evidence_id.index()].kind == .source_span) return evidence_id;
    }
    return fallback;
}

pub fn invocationTarget(program: *const ir.Program, subject: ir.ObligationSubject) ?InvocationTarget {
    const subject_instruction_id = switch (subject) {
        .instruction => |instruction_id| instruction_id,
        else => return null,
    };
    if (subject_instruction_id.index() >= program.instructions.len) return null;
    const subject_instruction = program.instructions[subject_instruction_id.index()];
    const target_id = switch (subject_instruction.operation) {
        .call => |call| call.callee,
        .namecall => |namecall| namecall.receiver,
        else => return null,
    };
    return valueProducer(program, target_id);
}

pub fn valueProducer(program: *const ir.Program, target_id: ir.ValueId) ?InvocationTarget {
    if (target_id.index() >= program.values.len) return null;

    const target = program.values[target_id.index()];
    return switch (target.origin) {
        .instruction_result => |origin| blk: {
            if (origin.instruction.index() >= program.instructions.len) {
                break :blk .{
                    .value = target_id,
                    .value_type = target.type.kind,
                    .producer = .{ .invalid_instruction = {} },
                    .producer_instruction = origin.instruction,
                    .evidence = null,
                };
            }
            const producer = program.instructions[origin.instruction.index()];
            const producer_class: ProducerClass = switch (producer.operation) {
                .constant => |literal| .{ .constant = std.meta.activeTag(literal) },
                else => .{ .operation = std.meta.activeTag(producer.operation) },
            };
            break :blk .{
                .value = target_id,
                .value_type = target.type.kind,
                .producer = producer_class,
                .producer_instruction = origin.instruction,
                .evidence = preferredEvidence(program, producer.evidence),
            };
        },
        .parameter => .{
            .value = target_id,
            .value_type = target.type.kind,
            .producer = .{ .parameter = {} },
            .producer_instruction = null,
            .evidence = null,
        },
        .block_parameter => .{
            .value = target_id,
            .value_type = target.type.kind,
            .producer = .{ .block_parameter = {} },
            .producer_instruction = null,
            .evidence = null,
        },
        .capture => .{
            .value = target_id,
            .value_type = target.type.kind,
            .producer = .{ .capture = {} },
            .producer_instruction = null,
            .evidence = null,
        },
    };
}

pub fn packResultProjection(program: *const ir.Program, value_id: ir.ValueId) ?PackResultProjection {
    if (value_id.index() >= program.values.len) return null;
    const origin = switch (program.values[value_id.index()].origin) {
        .instruction_result => |value| value,
        else => return null,
    };
    if (origin.instruction.index() >= program.instructions.len) return null;
    const adjustment = program.instructions[origin.instruction.index()];
    const pack_id = switch (adjustment.operation) {
        .adjust_pack => |value| value,
        else => return null,
    };
    const result_index = std.math.cast(usize, origin.index) orelse return null;
    if (result_index >= adjustment.results.len or adjustment.results[result_index] != value_id or
        pack_id.index() >= program.value_packs.len) return null;

    const producer_id = switch (program.value_packs[pack_id.index()].origin) {
        .instruction_result => |instruction_id| instruction_id,
        .varargs => return null,
    };
    if (producer_id.index() >= program.instructions.len) return null;
    const producer = program.instructions[producer_id.index()];
    if (producer.pack_result == null or producer.pack_result.? != pack_id) return null;
    return .{
        .adjustment = adjustment.id,
        .result_index = origin.index,
        .pack = pack_id,
        .producer = producer_id,
        .producer_operation = std.meta.activeTag(producer.operation),
        .evidence = preferredEvidence(program, producer.evidence),
    };
}

pub fn placeFlowClass(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    target: InvocationTarget,
) !PlaceFlowClass {
    const read_id = switch (target.producer) {
        .operation => |operation| if (operation == .place_read) target.producer_instruction else null,
        else => null,
    } orelse return .{ .none = {} };
    var flow = (try place_flow.analyzeDirectReachingWrites(allocator, program, read_id)) orelse
        return .{ .unavailable = {} };
    defer flow.deinit();
    if (flow.reaches_entry) return if (flow.writes.len == 0)
        .{ .entry = {} }
    else
        .{ .entry_and_writes = {} };
    if (flow.writes.len == 0) return .{ .unavailable = {} };
    if (flow.writes.len != 1) return .{ .multiple = {} };

    const write_id = flow.writes[0];
    if (write_id.index() >= program.instructions.len) return .{ .unavailable = {} };
    const value_id = switch (program.instructions[write_id.index()].operation) {
        .place_write => |write| write.value,
        else => return .{ .unavailable = {} },
    };
    const value = valueProducer(program, value_id) orelse return .{ .unavailable = {} };
    if (packResultProjection(program, value_id)) |projection| return .{ .pack_projection = .{
        .producer_operation = projection.producer_operation,
        .result_index = projection.result_index,
    } };
    return .{ .unique = value.producer };
}

pub fn placeFlowClassMatches(class: PlaceFlowClass, expected: []const u8) bool {
    return switch (class) {
        .none => std.mem.eql(u8, expected, "none"),
        .unavailable => std.mem.eql(u8, expected, "unavailable"),
        .entry => std.mem.eql(u8, expected, "entry"),
        .entry_and_writes => std.mem.eql(u8, expected, "entry_and_writes"),
        .multiple => std.mem.eql(u8, expected, "multiple"),
        .unique => |producer| std.mem.startsWith(u8, expected, "unique.") and
            std.mem.eql(u8, expected["unique.".len..], producer.label()),
        .pack_projection => |projection| blk: {
            const prefix = "unique.pack.";
            if (!std.mem.startsWith(u8, expected, prefix)) break :blk false;
            const detail = expected[prefix.len..];
            const separator = std.mem.lastIndexOfScalar(u8, detail, '.') orelse break :blk false;
            const result_index = std.fmt.parseInt(u32, detail[separator + 1 ..], 10) catch break :blk false;
            break :blk std.mem.eql(u8, detail[0..separator], @tagName(projection.producer_operation)) and
                result_index == projection.result_index;
        },
    };
}

const TestProgram = struct {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const source_span = ir.EvidenceId.fromIndex(0);
    const fallback = ir.EvidenceId.fromIndex(1);

    const nil_producer = ir.InstructionId.fromIndex(0);
    const nil_call = ir.InstructionId.fromIndex(1);
    const false_producer = ir.InstructionId.fromIndex(2);
    const false_call = ir.InstructionId.fromIndex(3);
    const dynamic_read = ir.InstructionId.fromIndex(4);
    const dynamic_call = ir.InstructionId.fromIndex(5);
    const nil_read = ir.InstructionId.fromIndex(6);
    const nil_namecall = ir.InstructionId.fromIndex(7);

    const nil_value = ir.ValueId.fromIndex(0);
    const false_value = ir.ValueId.fromIndex(1);
    const dynamic_place_value = ir.ValueId.fromIndex(2);
    const nil_place_value = ir.ValueId.fromIndex(3);

    const values = [_]ir.Value{
        .{ .id = nil_value, .function = function_id, .type = .{ .kind = .nil_value }, .origin = .{ .instruction_result = .{ .instruction = nil_producer, .index = 0 } } },
        .{ .id = false_value, .function = function_id, .type = .boolean, .origin = .{ .instruction_result = .{ .instruction = false_producer, .index = 0 } } },
        .{ .id = dynamic_place_value, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = dynamic_read, .index = 0 } } },
        .{ .id = nil_place_value, .function = function_id, .type = .{ .kind = .nil_value }, .origin = .{ .instruction_result = .{ .instruction = nil_read, .index = 0 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = nil_producer, .block = block_id, .operation = .{ .constant = .{ .nil_value = {} } }, .results = &.{nil_value}, .effects = .pure, .evidence = &.{ fallback, source_span } },
        .{ .id = nil_call, .block = block_id, .operation = .{ .call = .{ .callee = nil_value, .arguments = &.{}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call },
        .{ .id = false_producer, .block = block_id, .operation = .{ .constant = .{ .boolean = false } }, .results = &.{false_value}, .effects = .pure },
        .{ .id = false_call, .block = block_id, .operation = .{ .call = .{ .callee = false_value, .arguments = &.{}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call },
        .{ .id = dynamic_read, .block = block_id, .operation = .{ .place_read = ir.PlaceId.fromIndex(0) }, .results = &.{dynamic_place_value}, .effects = .place_read },
        .{ .id = dynamic_call, .block = block_id, .operation = .{ .call = .{ .callee = dynamic_place_value, .arguments = &.{}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .dynamic_call },
        .{ .id = nil_read, .block = block_id, .operation = .{ .place_read = ir.PlaceId.fromIndex(1) }, .results = &.{nil_place_value}, .effects = .place_read },
        .{ .id = nil_namecall, .block = block_id, .operation = .{ .namecall = .{ .receiver = nil_place_value, .method = "probe", .arguments = &.{}, .result_arity = .{ .fixed = 0 } } }, .results = &.{}, .effects = .namecall },
    };
    const evidence = [_]ir.Evidence{
        .{ .id = source_span, .kind = .source_span, .locator = "source:generic:1,1 - 1,4" },
        .{ .id = fallback, .kind = .frontend_proof, .locator = "proof:generic:nil" },
    };
    const program: ir.Program = .{
        .program_id = "generic-blocker-report",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .evidence = &evidence,
    };
};

test "invocation blocker reports distinguish constant targets" {
    const nil_target = invocationTarget(&TestProgram.program, .{ .instruction = TestProgram.nil_call }).?;
    try std.testing.expectEqual(TestProgram.nil_value, nil_target.value);
    try std.testing.expectEqual(ir.TypeKind.nil_value, nil_target.value_type);
    try std.testing.expectEqualStrings("constant.nil_value", nil_target.producer.label());
    try std.testing.expectEqual(TestProgram.nil_producer, nil_target.producer_instruction.?);
    try std.testing.expectEqual(TestProgram.source_span, nil_target.evidence.?);

    const false_target = invocationTarget(&TestProgram.program, .{ .instruction = TestProgram.false_call }).?;
    try std.testing.expectEqual(ir.TypeKind.boolean, false_target.value_type);
    try std.testing.expectEqualStrings("constant.boolean", false_target.producer.label());
}

test "invocation blocker reports preserve place-read target types" {
    const dynamic_target = invocationTarget(&TestProgram.program, .{ .instruction = TestProgram.dynamic_call }).?;
    try std.testing.expectEqual(ir.TypeKind.dynamic, dynamic_target.value_type);
    try std.testing.expectEqualStrings("place_read", dynamic_target.producer.label());

    const nil_target = invocationTarget(&TestProgram.program, .{ .instruction = TestProgram.nil_namecall }).?;
    try std.testing.expectEqual(TestProgram.nil_place_value, nil_target.value);
    try std.testing.expectEqual(ir.TypeKind.nil_value, nil_target.value_type);
    try std.testing.expectEqualStrings("place_read", nil_target.producer.label());
}

test "invocation blocker reports reject invalid and non-instruction subjects" {
    try std.testing.expect(invocationTarget(&TestProgram.program, .{ .program = {} }) == null);
    try std.testing.expect(invocationTarget(&TestProgram.program, .{ .value = TestProgram.nil_value }) == null);
    try std.testing.expect(invocationTarget(&TestProgram.program, .{ .instruction = TestProgram.nil_producer }) == null);
    try std.testing.expect(invocationTarget(&TestProgram.program, .{ .instruction = ir.InstructionId.fromIndex(999) }) == null);
}

test "pack result reports preserve producer and projection ordinal" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const callee = ir.ValueId.fromIndex(0);
    const first = ir.ValueId.fromIndex(1);
    const second = ir.ValueId.fromIndex(2);
    const call_id = ir.InstructionId.fromIndex(0);
    const adjustment_id = ir.InstructionId.fromIndex(1);
    const pack_id = ir.ValuePackId.fromIndex(0);
    const values = [_]ir.Value{
        .{ .id = callee, .function = function_id, .type = .function, .origin = .{ .parameter = 0 } },
        .{ .id = first, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = adjustment_id, .index = 0 } } },
        .{ .id = second, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = adjustment_id, .index = 1 } } },
    };
    const instructions = [_]ir.Instruction{
        .{ .id = call_id, .block = block_id, .operation = .{ .call = .{ .callee = callee, .arguments = &.{}, .result_arity = .{ .variadic = {} } } }, .results = &.{}, .pack_result = pack_id, .effects = .dynamic_call },
        .{ .id = adjustment_id, .block = block_id, .operation = .{ .adjust_pack = pack_id }, .results = &.{ first, second }, .effects = .pure },
    };
    const packs = [_]ir.ValuePack{.{ .id = pack_id, .function = function_id, .origin = .{ .instruction_result = call_id } }};
    const program: ir.Program = .{
        .program_id = "generic-pack-projection-report",
        .entry_function = function_id,
        .functions = &.{},
        .blocks = &.{},
        .instructions = &instructions,
        .values = &values,
        .value_packs = &packs,
    };

    const projection = packResultProjection(&program, second).?;
    try std.testing.expectEqual(adjustment_id, projection.adjustment);
    try std.testing.expectEqual(@as(u32, 1), projection.result_index);
    try std.testing.expectEqual(pack_id, projection.pack);
    try std.testing.expectEqual(call_id, projection.producer);
    try std.testing.expectEqual(std.meta.Tag(ir.Operation).call, projection.producer_operation);
    try std.testing.expect(packResultProjection(&program, callee) == null);
    try std.testing.expect(placeFlowClassMatches(.{ .pack_projection = .{
        .producer_operation = .call,
        .result_index = 1,
    } }, "unique.pack.call.1"));
    try std.testing.expect(!placeFlowClassMatches(.{ .pack_projection = .{
        .producer_operation = .call,
        .result_index = 1,
    } }, "unique.pack.call.0"));
}

test "obligation proof-link reports preserve every explicit link combination" {
    const requirement: ir.ObligationRequirement = .{
        .kind = .prove_true,
        .predicate = ir.SolverTermId.fromIndex(0),
    };
    const rows = [_]struct {
        requirement: ?ir.ObligationRequirement = null,
        query: ?ir.QueryId = null,
        certificate: ?ir.CertificateId = null,
        expected: []const u8,
    }{
        .{ .expected = "none" },
        .{ .requirement = requirement, .expected = "requirement" },
        .{ .query = ir.QueryId.fromIndex(0), .expected = "query" },
        .{ .certificate = ir.CertificateId.fromIndex(0), .expected = "certificate" },
        .{ .requirement = requirement, .query = ir.QueryId.fromIndex(0), .expected = "requirement_query" },
        .{ .requirement = requirement, .certificate = ir.CertificateId.fromIndex(0), .expected = "requirement_certificate" },
        .{ .query = ir.QueryId.fromIndex(0), .certificate = ir.CertificateId.fromIndex(0), .expected = "query_certificate" },
        .{
            .requirement = requirement,
            .query = ir.QueryId.fromIndex(0),
            .certificate = ir.CertificateId.fromIndex(0),
            .expected = "requirement_query_certificate",
        },
    };
    for (rows) |row| {
        const obligation: ir.Obligation = .{
            .id = ir.ObligationId.fromIndex(0),
            .kind = .unresolved_identity,
            .subject = .{ .program = {} },
            .status = .open,
            .blocks_profile = .readable_luau,
            .detail = "generic proof-link census",
            .requirement = row.requirement,
            .query = row.query,
            .certificate = row.certificate,
        };
        try std.testing.expectEqualStrings(row.expected, @tagName(obligationProofLinks(obligation)));
        try std.testing.expect(obligationProofLinksMatch(obligation, row.expected));
        try std.testing.expect(!obligationProofLinksMatch(obligation, "sample-specific"));
    }
}
