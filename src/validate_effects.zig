const ir = @import("ir.zig");
const diagnostics = @import("diagnostics.zig");
const proof_validation = @import("validate_proofs.zig");
const operator_domain = @import("operator_domain.zig");

pub fn pendingAuthorityResolves(
    program: *const ir.Program,
    instruction: ir.Instruction,
    code: diagnostics.Code,
) bool {
    return switch (code) {
        .understated_call_effects => instruction.operation == .call and
            proof_validation.hasPendingEffectAuthority(program, instruction),
        .understated_operator_effects => pendingOperatorAuthorityResolves(program, instruction),
        .unproved_primitive_operator_domain => pendingPrimitiveAuthorityResolves(program, instruction),
        .understated_table_get_effects => switch (instruction.operation) {
            .table_get => |operation| operation.mode == .semantic and
                includes(instruction.effects, ir.EffectSummary.raw_table_read) and
                proof_validation.hasPendingNoMetamethodAuthority(program, instruction),
            else => false,
        },
        .understated_table_set_effects => switch (instruction.operation) {
            .table_set => |operation| operation.mode == .semantic and
                includes(instruction.effects, ir.EffectSummary.raw_table_write) and
                proof_validation.hasPendingNoMetamethodAuthority(program, instruction),
            else => false,
        },
        .understated_environment_get_effects => switch (instruction.operation) {
            .environment_get => |operation| operation.mode == .semantic and
                includes(instruction.effects, ir.EffectSummary.raw_table_read) and
                proof_validation.hasPendingNoMetamethodAuthority(program, instruction),
            else => false,
        },
        .understated_environment_set_effects => switch (instruction.operation) {
            .environment_set => |operation| operation.mode == .semantic and
                includes(instruction.effects, ir.EffectSummary.raw_table_write) and
                proof_validation.hasPendingNoMetamethodAuthority(program, instruction),
            else => false,
        },
        else => false,
    };
}

fn pendingOperatorAuthorityResolves(program: *const ir.Program, instruction: ir.Instruction) bool {
    if (!proof_validation.hasPendingNoMetamethodAuthority(program, instruction)) return false;
    return switch (instruction.operation) {
        .unary => |operation| operation.mode == .semantic and
            !operator_domain.unaryIsStatic(program.values, operation) and
            includes(instruction.effects, unaryNoDispatchMinimum(operation.operator)),
        .binary => |operation| operation.mode == .semantic and
            !operator_domain.binaryIsStatic(program.values, operation) and
            includes(instruction.effects, binaryNoDispatchMinimum(operation.operator)),
        else => false,
    };
}

fn pendingPrimitiveAuthorityResolves(program: *const ir.Program, instruction: ir.Instruction) bool {
    if (!proof_validation.hasPendingPrimitiveOperatorAuthority(program, instruction)) return false;
    return switch (instruction.operation) {
        .unary => |operation| operation.mode == .primitive and !operator_domain.unaryIsStatic(program.values, operation),
        .binary => |operation| operation.mode == .primitive and !operator_domain.binaryIsStatic(program.values, operation),
        else => false,
    };
}

pub fn validateCall(report: *diagnostics.Report, program: *const ir.Program, instruction: ir.Instruction) !void {
    if (instruction.effects.precision == .unknown) return;
    if (!includes(instruction.effects, ir.EffectSummary.dynamic_call) and !proof_validation.hasEffectAuthority(program, instruction)) {
        try report.add(.understated_call_effects, instruction.id.index());
    }
}

pub fn validateNamecall(report: *diagnostics.Report, instruction: ir.Instruction) !void {
    try validateKnownMinimum(report, instruction, ir.EffectSummary.namecall, .invalid_namecall_effects);
}

pub fn validateUnary(
    report: *diagnostics.Report,
    program: *const ir.Program,
    instruction: ir.Instruction,
    operation: ir.Unary,
) !void {
    const static_domain = operator_domain.unaryIsStatic(program.values, operation);
    if (operation.mode == .primitive and !static_domain and !proof_validation.hasPrimitiveOperatorAuthority(program, instruction)) {
        try report.add(.unproved_primitive_operator_domain, instruction.id.index());
    }
    if (operation.mode == .semantic and !static_domain and instruction.effects.precision != .unknown and
        !includes(
            instruction.effects,
            if (proof_validation.hasNoMetamethodAuthority(program, instruction))
                unaryNoDispatchMinimum(operation.operator)
            else
                ir.EffectSummary.dynamic_call,
        ))
    {
        try report.add(.understated_operator_effects, instruction.id.index());
    }
}

pub fn validateBinary(
    report: *diagnostics.Report,
    program: *const ir.Program,
    instruction: ir.Instruction,
    operation: ir.Binary,
) !void {
    const static_domain = operator_domain.binaryIsStatic(program.values, operation);
    if (operation.mode == .primitive and !static_domain and !proof_validation.hasPrimitiveOperatorAuthority(program, instruction)) {
        try report.add(.unproved_primitive_operator_domain, instruction.id.index());
    }
    if (operation.mode == .semantic and !static_domain and instruction.effects.precision != .unknown and
        !includes(
            instruction.effects,
            if (proof_validation.hasNoMetamethodAuthority(program, instruction))
                binaryNoDispatchMinimum(operation.operator)
            else
                ir.EffectSummary.dynamic_call,
        ))
    {
        try report.add(.understated_operator_effects, instruction.id.index());
    }
}

pub fn validateTableGet(report: *diagnostics.Report, program: *const ir.Program, instruction: ir.Instruction, operation: ir.TableGet) !void {
    if (instruction.effects.precision == .unknown) return;
    const required = switch (operation.mode) {
        .semantic => if (proof_validation.hasNoMetamethodAuthority(program, instruction))
            ir.EffectSummary.raw_table_read
        else
            ir.EffectSummary.semantic_table_read,
        .raw => ir.EffectSummary.raw_table_read,
    };
    if (!includes(instruction.effects, required)) {
        try report.add(.understated_table_get_effects, instruction.id.index());
    }
}

pub fn validateTableSet(report: *diagnostics.Report, program: *const ir.Program, instruction: ir.Instruction, operation: ir.TableSet) !void {
    if (instruction.effects.precision == .unknown) return;
    const required = switch (operation.mode) {
        .semantic => if (proof_validation.hasNoMetamethodAuthority(program, instruction))
            ir.EffectSummary.raw_table_write
        else
            ir.EffectSummary.semantic_table_write,
        .raw => ir.EffectSummary.raw_table_write,
    };
    if (!includes(instruction.effects, required)) {
        try report.add(.understated_table_set_effects, instruction.id.index());
    }
}

pub fn validateTableSetPack(report: *diagnostics.Report, instruction: ir.Instruction) !void {
    try validateKnownMinimum(report, instruction, ir.EffectSummary.raw_table_write, .invalid_table_set_pack_effects);
}

pub fn validateEnvironmentGet(report: *diagnostics.Report, program: *const ir.Program, instruction: ir.Instruction, operation: ir.EnvironmentGet) !void {
    if (operation.target == .ambient and operation.mode == .raw) {
        try report.add(.invalid_ambient_environment_mode, instruction.id.index());
    }
    if (instruction.effects.precision == .unknown) return;
    const required = switch (operation.mode) {
        .semantic => if (proof_validation.hasNoMetamethodAuthority(program, instruction))
            ir.EffectSummary.raw_table_read
        else
            ir.EffectSummary.semantic_environment_read,
        .raw => ir.EffectSummary.raw_table_read,
    };
    if (!includes(instruction.effects, required)) {
        try report.add(.understated_environment_get_effects, instruction.id.index());
    }
}

pub fn validateEnvironmentSet(report: *diagnostics.Report, program: *const ir.Program, instruction: ir.Instruction, operation: ir.EnvironmentSet) !void {
    if (operation.target == .ambient and operation.mode == .raw) {
        try report.add(.invalid_ambient_environment_mode, instruction.id.index());
    }
    if (instruction.effects.precision == .unknown) return;
    const required = switch (operation.mode) {
        .semantic => if (proof_validation.hasNoMetamethodAuthority(program, instruction))
            ir.EffectSummary.raw_table_write
        else
            ir.EffectSummary.semantic_environment_write,
        .raw => ir.EffectSummary.raw_table_write,
    };
    if (!includes(instruction.effects, required)) {
        try report.add(.understated_environment_set_effects, instruction.id.index());
    }
}

pub fn validateProtectedCall(report: *diagnostics.Report, instruction: ir.Instruction) !void {
    try validateKnownMinimum(report, instruction, ir.EffectSummary.protected_invocation, .invalid_protected_call_effects);
}

pub fn validateCoroutineCreate(report: *diagnostics.Report, instruction: ir.Instruction) !void {
    try validateKnownMinimum(report, instruction, ir.EffectSummary.coroutine_create, .invalid_coroutine_create_effects);
}

pub fn validateCoroutineResume(report: *diagnostics.Report, instruction: ir.Instruction) !void {
    try validateKnownMinimum(report, instruction, ir.EffectSummary.coroutine_resume, .invalid_coroutine_resume_effects);
}

pub fn validateCoroutineYield(report: *diagnostics.Report, instruction: ir.Instruction) !void {
    try validateKnownMinimum(report, instruction, ir.EffectSummary.coroutine_yield, .invalid_coroutine_yield_effects);
}

pub fn validateNumericForNext(
    report: *diagnostics.Report,
    instruction: ir.Instruction,
    operation: ir.NumericForNext,
) !void {
    const minimum = switch (operation.mode) {
        .luau_numeric => ir.EffectSummary.numeric_for_next,
        .semantic_normalized => ir.EffectSummary.dynamic_call,
    };
    try validateKnownMinimum(report, instruction, minimum, .invalid_numeric_for_next_effects);
}

pub fn validateGenericForNext(report: *diagnostics.Report, instruction: ir.Instruction) !void {
    try validateKnownMinimum(report, instruction, ir.EffectSummary.generic_for_next, .invalid_generic_for_next_effects);
}

pub fn validateTableConstructor(report: *diagnostics.Report, instruction: ir.Instruction) !void {
    try validateKnownMinimum(report, instruction, ir.EffectSummary.table_constructor, .invalid_table_constructor_effects);
}

pub fn validateStringInterpolation(report: *diagnostics.Report, instruction: ir.Instruction) !void {
    try validateKnownMinimum(report, instruction, ir.EffectSummary.string_interpolation, .invalid_string_interpolation_effects);
}

fn validateKnownMinimum(
    report: *diagnostics.Report,
    instruction: ir.Instruction,
    required: ir.EffectSummary,
    code: diagnostics.Code,
) !void {
    if (instruction.effects.precision != .unknown and !includes(instruction.effects, required)) {
        try report.add(code, instruction.id.index());
    }
}

fn includes(actual: ir.EffectSummary, required: ir.EffectSummary) bool {
    return (!required.reads_memory or actual.reads_memory) and
        (!required.writes_memory or actual.writes_memory) and
        (!required.may_throw or actual.may_throw) and
        (!required.may_yield or actual.may_yield) and
        (!required.invokes_unknown_code or actual.invokes_unknown_code);
}

fn unaryNoDispatchMinimum(operator: ir.UnaryOperator) ir.EffectSummary {
    return switch (operator) {
        .logical_not => .pure,
        .negate, .bit_not => .{ .precision = .conservative, .may_throw = true },
        .length => .{ .precision = .conservative, .reads_memory = true, .may_throw = true },
    };
}

fn binaryNoDispatchMinimum(operator: ir.BinaryOperator) ir.EffectSummary {
    return switch (operator) {
        .logical_and, .logical_or, .equal, .not_equal => .pure,
        else => .{ .precision = .conservative, .may_throw = true },
    };
}
