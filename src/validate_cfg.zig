const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const structure = @import("structure.zig");
const irreducible_region = @import("irreducible_region.zig");
const irreducible_policy = @import("irreducible_policy.zig");
const structure_validation = @import("validate_structure.zig");
const diagnostics = @import("diagnostics.zig");
const pack_validation = @import("validate_packs.zig");
const iteration_protocol = @import("iteration_protocol.zig");
const syntax_depth_validation = @import("validate_luau_syntax_depth.zig");
const luau_runtime = @import("luau_runtime.zig");
const stage_trace = @import("stage_trace.zig");

pub fn validate(
    allocator: std.mem.Allocator,
    report: *diagnostics.Report,
    program: *const ir.Program,
    profile: ir.AdmissionProfile,
    block_memberships: []const u32,
    instruction_memberships: []const u32,
) !void {
    const instruction_positions = try allocator.alloc(?usize, program.instructions.len);
    defer allocator.free(instruction_positions);
    @memset(instruction_positions, null);
    for (program.blocks) |block| {
        for (block.instructions, 0..) |instruction_id, position| {
            if (validId(instruction_id, program.instructions.len) and instruction_memberships[instruction_id.index()] == 1) {
                instruction_positions[instruction_id.index()] = position;
            }
        }
    }

    for (program.functions) |function| {
        if (!hasCanonicalMembership(program, function, block_memberships, instruction_memberships)) continue;
        if (stage_trace.enabled) std.debug.print("cfg_validation function={} stage=begin\n", .{function.id.index()});
        var analysis = cfg.Analysis.init(allocator, program, function) catch |err| switch (err) {
            error.InvalidCfg => continue,
            error.OutOfMemory => return error.OutOfMemory,
        };
        defer analysis.deinit();

        if (profile == .readable_luau) {
            const direct_spine_depth = try syntax_depth_validation.maxDirectSpineDepth(allocator, program, &analysis);
            var skip_recursive_structuring = false;
            if (direct_spine_depth >= luau_runtime.max_emitted_syntax_nesting) {
                if (direct_spine_depth > luau_runtime.max_emitted_syntax_nesting) {
                    try report.add(.unsupported_readable_syntax_depth, function.id.index());
                }
                // The recursive structurer cannot safely consume the exact
                // parser limit. A proven direct branch spine has no joins,
                // loops, or cross-entry state, so ordinary CFG/use checks
                // remain sound without constructing its recursive region.
                skip_recursive_structuring = true;
            }
            if (!skip_recursive_structuring) {
                var maybe_plan: ?structure.Plan = structure.Plan.initWithArbitraryFallback(allocator, &analysis) catch |err| switch (err) {
                    error.UnsupportedShape => blk: {
                        if (stage_trace.enabled) {
                            if (@errorReturnTrace()) |trace| {
                                std.debug.print("UnsupportedShape trace for function {d}:\n", .{function.id.index()});
                                const st = std.debug.StackTrace{
                                    .return_addresses = trace.instruction_addresses[0..@min(trace.index, 6)],
                                    .skipped = .none,
                                };
                                std.debug.dumpStackTrace(&st);
                            }
                        }
                        try report.add(.unsupported_readable_control_flow, function.id.index());
                        var regions = try irreducible_region.analyze(allocator, &analysis);
                        defer regions.deinit();
                        for (regions.regions) |region| {
                            const selection = try irreducible_policy.selectPrimary(allocator, program, region);
                            const primary = selection.block;
                            for (region.entries) |entry| {
                                try report.add(.irreducible_control_entry, entry.block.index());
                                if (entry.block == primary) {
                                    if (selection.refusal) |refusal| try report.add(refusalDiagnostic(refusal), entry.block.index());
                                    continue;
                                }
                                if (irreducible_policy.classifySecondary(program, region, primary, entry)) |refusal| {
                                    try report.add(refusalDiagnostic(refusal), entry.block.index());
                                }
                            }
                        }
                        break :blk null;
                    },
                    error.OutOfMemory => return error.OutOfMemory,
                };
                if (maybe_plan) |*plan| {
                    defer plan.deinit();
                    if (!plan.root.arbitrary_cfg) {
                        try structure_validation.validateFunction(allocator, report, program, &analysis, plan);
                        try iteration_protocol.validateFunction(allocator, report, program, &analysis, plan);
                    }
                }
            }
        }

        for (function.blocks) |block_id| {
            const block = program.blocks[block_id.index()];
            if (!analysis.isReachable(block_id)) {
                continue;
            }
            for (block.instructions, 0..) |instruction_id, position| {
                if (!validId(instruction_id, program.instructions.len)) continue;
                const instruction = program.instructions[instruction_id.index()];
                try validateInstructionUses(report, program, &analysis, instruction_positions, instruction, position);
                try pack_validation.validateInstructionUse(report, program, &analysis, instruction_positions, instruction, position);
            }
            try validateTerminatorUses(report, program, &analysis, instruction_positions, block);
            try pack_validation.validateTerminatorUse(report, program, &analysis, instruction_positions, block);
        }
        if (stage_trace.enabled) std.debug.print("cfg_validation function={} stage=done\n", .{function.id.index()});
    }
}

fn refusalDiagnostic(refusal: irreducible_policy.Refusal) diagnostics.Code {
    return switch (refusal) {
        .instructions => .irreducible_entry_has_instructions,
        .parameter_contract => .irreducible_entry_parameter_contract,
        .entry_contract, .incoming_edge_contract => .irreducible_entry_edge_contract,
        .nonprimary_successor => .irreducible_entry_nonprimary_successor,
    };
}

fn hasCanonicalMembership(
    program: *const ir.Program,
    function: ir.Function,
    block_memberships: []const u32,
    instruction_memberships: []const u32,
) bool {
    for (program.blocks, 0..) |block, block_index| {
        if (block.function != function.id) continue;
        if (block.id.index() != block_index) return false;
        if (block_memberships[block.id.index()] != 1) return false;
        for (block.instructions) |instruction_id| {
            if (!validId(instruction_id, program.instructions.len) or instruction_memberships[instruction_id.index()] != 1) return false;
            if (program.instructions[instruction_id.index()].block != block.id) return false;
        }
    }
    return true;
}

fn validateInstructionUses(
    report: *diagnostics.Report,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    instruction_positions: []const ?usize,
    instruction: ir.Instruction,
    position: usize,
) !void {
    const block = program.blocks[instruction.block.index()];
    switch (instruction.operation) {
        .constant, .make_table, .function_ref => {},
        .place_read => |place_id| try validatePlaceUse(report, program, analysis, instruction_positions, block, position, place_id, instruction.id, instruction.id.index()),
        .pack_values => |values| for (values) |value| try validateValueUse(report, program, analysis, instruction_positions, block, position, value, instruction.id.index()),
        .adjust_pack => {},
        .copy => |value| try validateValueUse(report, program, analysis, instruction_positions, block, position, value, instruction.id.index()),
        .unary => |operation| try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.operand, instruction.id.index()),
        .binary => |operation| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.left, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.right, instruction.id.index());
        },
        .call => |operation| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.callee, instruction.id.index());
            for (operation.arguments) |argument| try validateValueUse(report, program, analysis, instruction_positions, block, position, argument, instruction.id.index());
        },
        .call_repeated_table_get => |operation| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.callee, instruction.id.index());
            for (operation.prefix_arguments) |argument| try validateValueUse(report, program, analysis, instruction_positions, block, position, argument, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.table, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.key, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.from, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.to, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.step, instruction.id.index());
            if (operation.counter) |counter| try validatePlaceUse(report, program, analysis, instruction_positions, block, position, counter, instruction.id, instruction.id.index());
        },
        .namecall => |operation| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.receiver, instruction.id.index());
            for (operation.arguments) |argument| try validateValueUse(report, program, analysis, instruction_positions, block, position, argument, instruction.id.index());
        },
        .protected_call => |operation| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.callee, instruction.id.index());
            if (operation.error_handler) |handler| try validateValueUse(report, program, analysis, instruction_positions, block, position, handler, instruction.id.index());
            for (operation.arguments) |argument| try validateValueUse(report, program, analysis, instruction_positions, block, position, argument, instruction.id.index());
        },
        .coroutine_create => |operation| try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.callee, instruction.id.index()),
        .coroutine_resume => |operation| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.thread, instruction.id.index());
            for (operation.arguments) |argument| try validateValueUse(report, program, analysis, instruction_positions, block, position, argument, instruction.id.index());
        },
        .coroutine_yield => |operation| for (operation.arguments) |argument| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, argument, instruction.id.index());
        },
        .environment_get => |operation| switch (operation.target) {
            .ambient => {},
            .value => |value_id| try validateValueUse(report, program, analysis, instruction_positions, block, position, value_id, instruction.id.index()),
        },
        .environment_set => |operation| {
            switch (operation.target) {
                .ambient => {},
                .value => |value_id| try validateValueUse(report, program, analysis, instruction_positions, block, position, value_id, instruction.id.index()),
            }
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.value, instruction.id.index());
        },
        .table_get => |operation| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.table, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.key, instruction.id.index());
        },
        .table_set => |operation| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.table, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.key, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.value, instruction.id.index());
        },
        .table_set_pack => |operation| try validateValueUse(
            report,
            program,
            analysis,
            instruction_positions,
            block,
            position,
            operation.table,
            instruction.id.index(),
        ),
        .make_closure => |operation| for (operation.bindings) |binding| switch (binding) {
            .value => |value_id| try validateValueUse(report, program, analysis, instruction_positions, block, position, value_id, instruction.id.index()),
            .place => |place_id| try validatePlaceUse(report, program, analysis, instruction_positions, block, position, place_id, instruction.id, instruction.id.index()),
        },
        .place_write => |operation| {
            try validatePlaceUse(report, program, analysis, instruction_positions, block, position, operation.place, instruction.id, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.value, instruction.id.index());
        },
        .numeric_for_next => |operation| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.control, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.limit, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.step, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.initial, instruction.id.index());
        },
        .generic_for_next => |operation| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.iterator, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.state, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.control, instruction.id.index());
            try validateValueUse(report, program, analysis, instruction_positions, block, position, operation.initial, instruction.id.index());
        },
        .make_table_literal => |operation| for (operation.fields) |field| switch (field) {
            .list => |value| try validateValueUse(report, program, analysis, instruction_positions, block, position, value, instruction.id.index()),
            .keyed => |keyed| {
                try validateValueUse(report, program, analysis, instruction_positions, block, position, keyed.key, instruction.id.index());
                try validateValueUse(report, program, analysis, instruction_positions, block, position, keyed.value, instruction.id.index());
            },
        },
        .string_interpolate => |operation| for (operation.values) |value| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, value, instruction.id.index());
        },
    }
}

fn validateTerminatorUses(
    report: *diagnostics.Report,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    instruction_positions: []const ?usize,
    block: ir.Block,
) !void {
    const position = block.instructions.len;
    switch (block.terminator) {
        .jump => |edge| try validateEdgeUses(report, program, analysis, instruction_positions, block, position, edge),
        .branch => |branch| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, branch.condition, block.id.index());
            try validateEdgeUses(report, program, analysis, instruction_positions, block, position, branch.then_edge);
            try validateEdgeUses(report, program, analysis, instruction_positions, block, position, branch.else_edge);
        },
        .return_values => |values| for (values) |value| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, value, block.id.index());
        },
        .return_pack => {},
        .return_expanded => |expanded| for (expanded.values) |value| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, value, block.id.index());
        },
        .throw_error => |throw_error| {
            try validateValueUse(report, program, analysis, instruction_positions, block, position, throw_error.value, block.id.index());
            if (throw_error.dynamic_level) |level| {
                try validateValueUse(report, program, analysis, instruction_positions, block, position, level, block.id.index());
            }
        },
        .unreachable_block => {},
    }
}

fn validateEdgeUses(
    report: *diagnostics.Report,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    instruction_positions: []const ?usize,
    block: ir.Block,
    position: usize,
    edge: ir.Edge,
) !void {
    for (edge.arguments) |argument| {
        try validateValueUse(report, program, analysis, instruction_positions, block, position, argument, block.id.index());
    }
}

fn validateValueUse(
    report: *diagnostics.Report,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    instruction_positions: []const ?usize,
    use_block: ir.Block,
    use_position: usize,
    value_id: ir.ValueId,
    entity_index: usize,
) !void {
    if (!validId(value_id, program.values.len)) return;
    const value = program.values[value_id.index()];
    if (value.function != use_block.function) return;

    switch (value.origin) {
        .parameter, .capture => {},
        .block_parameter => |origin| {
            if (!validId(origin.block, program.blocks.len) or origin.block == use_block.id) return;
            if (!analysis.dominates(origin.block, use_block.id)) {
                if (stage_trace.enabled) std.debug.print(
                    "cfg_non_dom function={} value={} origin_block={} use_block={} use_position={} entity={} kind=block_parameter\n",
                    .{ use_block.function.index(), value_id.index(), origin.block.index(), use_block.id.index(), use_position, entity_index },
                );
                try report.add(.non_dominating_value_use, entity_index);
            }
        },
        .instruction_result => |origin| {
            if (!validId(origin.instruction, program.instructions.len)) return;
            const definition = program.instructions[origin.instruction.index()];
            if (!validId(definition.block, program.blocks.len)) return;
            if (definition.block == use_block.id) {
                const definition_position = instruction_positions[origin.instruction.index()] orelse return;
                if (definition_position >= use_position) try report.add(.value_used_before_definition, entity_index);
            } else if (!analysis.dominates(definition.block, use_block.id)) {
                if (stage_trace.enabled) std.debug.print(
                    "cfg_non_dom function={} value={} origin_instruction={} origin_block={} use_block={} use_position={} entity={} kind=instruction_result\n",
                    .{ use_block.function.index(), value_id.index(), origin.instruction.index(), definition.block.index(), use_block.id.index(), use_position, entity_index },
                );
                try report.add(.non_dominating_value_use, entity_index);
            }
        },
    }
}

fn validatePlaceUse(
    report: *diagnostics.Report,
    program: *const ir.Program,
    analysis: *const cfg.Analysis,
    instruction_positions: []const ?usize,
    use_block: ir.Block,
    use_position: usize,
    place_id: ir.PlaceId,
    use_instruction: ir.InstructionId,
    entity_index: usize,
) !void {
    if (!validId(place_id, program.places.len)) return;
    const place = program.places[place_id.index()];
    if (place.function != use_block.function) return;
    const allocation_id = switch (place.origin) {
        .instruction => |instruction_id| instruction_id,
        .local, .capture => return,
    };
    if (!validId(allocation_id, program.instructions.len) or allocation_id == use_instruction) return;
    const allocation = program.instructions[allocation_id.index()];
    if (!validId(allocation.block, program.blocks.len)) return;
    if (allocation.block == use_block.id) {
        const allocation_position = instruction_positions[allocation_id.index()] orelse return;
        if (allocation_position >= use_position) try report.add(.place_used_before_allocation, entity_index);
    } else if (!analysis.dominates(allocation.block, use_block.id)) {
        try report.add(.non_dominating_place_allocation, entity_index);
    }
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}
