const ir = @import("ir.zig");
const diagnostics = @import("diagnostics.zig");

pub fn validateTopology(report: *diagnostics.Report, program: *const ir.Program) !void {
    if (validId(program.entry_function, program.functions.len) and program.functions[program.entry_function.index()].lexical_parent != null) {
        try report.add(.invalid_entry_function_parent, program.entry_function.index());
    }

    for (program.functions) |function| {
        var current = function;
        var depth: usize = 0;
        while (current.lexical_parent) |parent_id| {
            if (!validId(parent_id, program.functions.len)) break;
            if (parent_id == function.id or depth >= program.functions.len) {
                try report.add(.cyclic_function_lexical_parent, function.id.index());
                break;
            }
            current = program.functions[parent_id.index()];
            depth += 1;
        }
    }
}

pub fn validateCaptures(
    report: *diagnostics.Report,
    program: *const ir.Program,
    defined_values: []bool,
    defined_places: []bool,
) !void {
    for (program.captures, 0..) |capture, capture_index| {
        try validateEvidenceList(report, program, capture.evidence, capture_index);
        if (!validId(capture.function, program.functions.len)) try report.add(.invalid_capture_function, capture_index);
        switch (capture.kind) {
            .immutable_value => |value_id| {
                if (!validId(value_id, program.values.len)) {
                    try report.add(.invalid_capture_value, capture_index);
                    continue;
                }
                const value = program.values[value_id.index()];
                const origin_matches = switch (value.origin) {
                    .capture => |origin| origin == capture.id,
                    else => false,
                };
                if (value.function != capture.function or !origin_matches) {
                    try report.add(.capture_slot_origin_mismatch, capture_index);
                }
                try markValueDefinition(report, defined_values, value_id);
            },
            .shared_place => |place_id| {
                if (!validId(place_id, program.places.len)) {
                    try report.add(.invalid_capture_place, capture_index);
                    continue;
                }
                const place = program.places[place_id.index()];
                const origin_matches = switch (place.origin) {
                    .capture => |origin| origin == capture.id,
                    else => false,
                };
                if (place.function != capture.function or !origin_matches) {
                    try report.add(.capture_slot_origin_mismatch, capture_index);
                }
                try markPlaceDefinition(report, defined_places, place_id);
            },
        }
    }
}

pub fn validateEntryBindings(report: *diagnostics.Report, program: *const ir.Program) !void {
    for (program.external_bindings, 0..) |binding, binding_index| {
        try validateEvidenceList(report, program, binding.evidence, binding_index);
    }

    if (!validId(program.entry_function, program.functions.len)) {
        for (program.external_bindings, 0..) |_, binding_index| {
            try report.add(.unlisted_external_binding, binding_index);
        }
        return;
    }

    const entry = program.functions[program.entry_function.index()];
    if (entry.captures.len != program.entry_bindings.len) {
        try report.add(.entry_capture_binding_arity_mismatch, entry.id.index());
    }
    const pair_count = @min(entry.captures.len, program.entry_bindings.len);
    for (0..pair_count) |index| {
        const binding_id = program.entry_bindings[index];
        if (!validId(binding_id, program.external_bindings.len)) {
            try report.add(.invalid_entry_capture_binding, index);
            continue;
        }
        const capture_id = entry.captures[index];
        if (!validId(capture_id, program.captures.len)) continue;
        const capture = program.captures[capture_id.index()];
        const binding = program.external_bindings[binding_id.index()];
        const matching_kind = switch (capture.kind) {
            .immutable_value => binding.kind == .immutable_value,
            .shared_place => binding.kind == .shared_place,
        };
        if (!matching_kind) try report.add(.entry_capture_binding_kind_mismatch, index);
    }

    for (program.external_bindings, 0..) |binding, binding_index| {
        var listed = false;
        for (program.entry_bindings) |binding_id| {
            if (binding_id == binding.id) {
                listed = true;
                break;
            }
        }
        if (!listed) try report.add(.unlisted_external_binding, binding_index);
    }
}

pub fn validatePlaces(report: *diagnostics.Report, program: *const ir.Program, defined_places: []const bool) !void {
    for (program.places, 0..) |place, place_index| {
        try validateEvidenceList(report, program, place.evidence, place_index);
        if (!validId(place.function, program.functions.len)) try report.add(.invalid_place_function, place_index);
        if (!defined_places[place_index]) try report.add(.missing_place_definition, place_index);
        switch (place.origin) {
            .local => {},
            .instruction => |instruction_id| {
                if (!validId(instruction_id, program.instructions.len)) {
                    try report.add(.invalid_place_allocation, place_index);
                    continue;
                }
                const instruction = program.instructions[instruction_id.index()];
                const matches = switch (instruction.operation) {
                    .place_write => |write| write.place == place.id,
                    else => false,
                };
                if (!matches) try report.add(.invalid_place_allocation, place_index);
            },
            .capture => |capture_id| if (!validId(capture_id, program.captures.len)) try report.add(.invalid_place_origin, place_index),
        }
    }
}

pub fn validateFunctionReference(
    report: *diagnostics.Report,
    program: *const ir.Program,
    target_id: ir.FunctionId,
    entity_index: usize,
) !void {
    if (!validId(target_id, program.functions.len)) {
        try report.add(.invalid_operand, entity_index);
        return;
    }
    const target = program.functions[target_id.index()];
    if (target.lexical_parent != null or target.captures.len != 0) {
        try report.add(.invalid_function_reference, entity_index);
    }
}

pub fn validateClosureOperation(
    report: *diagnostics.Report,
    program: *const ir.Program,
    operation: ir.Closure,
    function_id: ir.FunctionId,
    entity_index: usize,
) !void {
    if (!validId(operation.function, program.functions.len)) {
        try report.add(.invalid_operand, entity_index);
        return;
    }
    const target = program.functions[operation.function.index()];
    if (target.lexical_parent == null or target.lexical_parent.? != function_id) {
        try report.add(.closure_lexical_parent_mismatch, entity_index);
    }
    if (operation.bindings.len != target.captures.len) {
        try report.add(.closure_binding_arity_mismatch, entity_index);
    }
    for (operation.bindings, 0..) |binding, index| {
        if (index >= target.captures.len or !validId(target.captures[index], program.captures.len)) {
            try validateBinding(report, program, binding, function_id, entity_index);
            continue;
        }
        const capture = program.captures[target.captures[index].index()];
        const matching_kind = switch (capture.kind) {
            .immutable_value => binding == .value,
            .shared_place => binding == .place,
        };
        if (!matching_kind) try report.add(.closure_binding_kind_mismatch, entity_index);
        try validateBinding(report, program, binding, function_id, entity_index);
    }
}

pub fn validatePlaceRead(
    report: *diagnostics.Report,
    program: *const ir.Program,
    place_id: ir.PlaceId,
    function_id: ir.FunctionId,
    effects: ir.EffectSummary,
    entity_index: usize,
) !void {
    try validatePlaceOperand(report, program, place_id, function_id, entity_index);
    if (!sameEffects(effects, ir.EffectSummary.place_read)) try report.add(.invalid_place_read_effects, entity_index);
}

pub fn validatePlaceWrite(
    report: *diagnostics.Report,
    program: *const ir.Program,
    operation: ir.PlaceWrite,
    function_id: ir.FunctionId,
    effects: ir.EffectSummary,
    entity_index: usize,
) !void {
    try validatePlaceOperand(report, program, operation.place, function_id, entity_index);
    if (!validId(operation.value, program.values.len)) {
        try report.add(.invalid_operand, entity_index);
    } else if (program.values[operation.value.index()].function != function_id) {
        try report.add(.cross_function_operand, entity_index);
    }
    if (!sameEffects(effects, ir.EffectSummary.place_write)) try report.add(.invalid_place_write_effects, entity_index);
}

pub fn markPlaceDefinition(report: *diagnostics.Report, defined_places: []bool, place_id: ir.PlaceId) !void {
    if (!validId(place_id, defined_places.len)) return;
    if (defined_places[place_id.index()]) try report.add(.duplicate_place_definition, place_id.index());
    defined_places[place_id.index()] = true;
}

fn markValueDefinition(report: *diagnostics.Report, defined_values: []bool, value_id: ir.ValueId) !void {
    if (!validId(value_id, defined_values.len)) return;
    if (defined_values[value_id.index()]) try report.add(.duplicate_value_definition, value_id.index());
    defined_values[value_id.index()] = true;
}

fn validateBinding(
    report: *diagnostics.Report,
    program: *const ir.Program,
    binding: ir.CaptureBinding,
    function_id: ir.FunctionId,
    entity_index: usize,
) !void {
    switch (binding) {
        .value => |value_id| {
            if (!validId(value_id, program.values.len)) {
                try report.add(.invalid_operand, entity_index);
            } else if (program.values[value_id.index()].function != function_id) {
                try report.add(.cross_function_operand, entity_index);
            }
        },
        .place => |place_id| {
            if (!validId(place_id, program.places.len)) {
                try report.add(.invalid_place_operand, entity_index);
            } else if (program.places[place_id.index()].function != function_id) {
                try report.add(.cross_function_place, entity_index);
            }
        },
    }
}

fn validatePlaceOperand(
    report: *diagnostics.Report,
    program: *const ir.Program,
    place_id: ir.PlaceId,
    function_id: ir.FunctionId,
    entity_index: usize,
) !void {
    if (!validId(place_id, program.places.len)) {
        try report.add(.invalid_place_operand, entity_index);
    } else if (program.places[place_id.index()].function != function_id) {
        try report.add(.cross_function_place, entity_index);
    }
}

fn sameEffects(left: ir.EffectSummary, right: ir.EffectSummary) bool {
    return left.precision == right.precision and
        left.reads_memory == right.reads_memory and
        left.writes_memory == right.writes_memory and
        left.may_throw == right.may_throw and
        left.may_yield == right.may_yield and
        left.invokes_unknown_code == right.invokes_unknown_code;
}

fn validateEvidenceList(
    report: *diagnostics.Report,
    program: *const ir.Program,
    evidence: []const ir.EvidenceId,
    entity_index: usize,
) !void {
    for (evidence) |evidence_id| {
        if (!validId(evidence_id, program.evidence.len)) try report.add(.invalid_evidence_reference, entity_index);
    }
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}
