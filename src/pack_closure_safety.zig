const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const normalized_value = @import("normalized_value.zig");
const readable_scope = @import("readable_scope.zig");
const runtime_uses = @import("runtime_uses.zig");

pub fn precedesInSameBlock(program: *const ir.Program, producer: ir.Instruction, consumer: ir.Instruction) bool {
    if (producer.block != consumer.block or !validId(producer.block, program.blocks.len)) return false;
    var producer_index: ?usize = null;
    var consumer_index: ?usize = null;
    for (program.blocks[producer.block.index()].instructions, 0..) |instruction_id, index| {
        if (instruction_id == producer.id) {
            if (producer_index != null) return false;
            producer_index = index;
        }
        if (instruction_id == consumer.id) {
            if (consumer_index != null) return false;
            consumer_index = index;
        }
    }
    return producer_index != null and consumer_index != null and producer_index.? < consumer_index.?;
}

pub fn functionHasReachableUnsafeClosure(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    roles: anytype,
    analysis: *const cfg.Analysis,
    producer_block: ir.BlockId,
    function_id: ir.FunctionId,
) !bool {
    for (program.instructions) |instruction| {
        if (!scope.instruction(instruction.id) or !validId(instruction.block, program.blocks.len)) continue;
        if (program.blocks[instruction.block.index()].function != function_id) continue;
        const closure = switch (instruction.operation) {
            .make_closure => |value| value,
            else => continue,
        };
        var needs_ephemeral_call = false;
        for (closure.bindings) |binding| {
            if (try closureBindingIsStable(
                allocator,
                program,
                scope,
                analysis,
                producer_block,
                function_id,
                binding,
            )) continue;
            if (!closureBindingIsCanonicalEphemeral(program, scope, function_id, binding)) return true;
            needs_ephemeral_call = true;
        }
        if (needs_ephemeral_call and !try closureHasOnlySynchronousUses(
            allocator,
            program,
            scope,
            roles,
            analysis,
            producer_block,
            function_id,
            instruction,
            closure,
        )) return true;
    }
    return false;
}

fn closureBindingIsStable(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    analysis: *const cfg.Analysis,
    producer_block: ir.BlockId,
    function_id: ir.FunctionId,
    binding: ir.CaptureBinding,
) !bool {
    const value_id = switch (binding) {
        .value => |value| value,
        .place => |place_id| return closurePlaceBindingIsStableRoot(
            allocator,
            program,
            scope,
            analysis,
            producer_block,
            function_id,
            place_id,
        ),
    };
    if (!closureValueIsCanonical(program, scope, function_id, value_id)) return false;
    const value = program.values[value_id.index()];
    return switch (value.origin) {
        .parameter, .capture => true,
        .instruction_result => |origin| blk: {
            const instruction = program.instructions[origin.instruction.index()];
            break :blk try blockIsStableBeforeProducer(
                allocator,
                program,
                scope,
                analysis,
                producer_block,
                function_id,
                instruction.block,
            );
        },
        .block_parameter => |origin| blockIsStableBeforeProducer(
            allocator,
            program,
            scope,
            analysis,
            producer_block,
            function_id,
            origin.block,
        ),
    };
}

fn closureBindingIsCanonicalEphemeral(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    function_id: ir.FunctionId,
    binding: ir.CaptureBinding,
) bool {
    return switch (binding) {
        .value => |value_id| closureValueIsCanonical(program, scope, function_id, value_id),
        .place => |place_id| closureInstructionPlaceIsCanonical(program, scope, function_id, place_id),
    };
}

fn closureValueIsCanonical(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    function_id: ir.FunctionId,
    value_id: ir.ValueId,
) bool {
    if (!validId(function_id, program.functions.len) or !validId(value_id, program.values.len)) return false;
    const value = program.values[value_id.index()];
    if (value.function != function_id) return false;
    const function = program.functions[function_id.index()];
    return switch (value.origin) {
        .parameter => |parameter_index| blk: {
            const index: usize = @intCast(parameter_index);
            break :blk index < function.parameters.len and function.parameters[index] == value_id;
        },
        .capture => |capture_id| blk: {
            if (!validId(capture_id, program.captures.len) or !functionListsCapture(function, capture_id)) break :blk false;
            const capture = program.captures[capture_id.index()];
            if (capture.function != function_id) break :blk false;
            break :blk switch (capture.kind) {
                .immutable_value => |captured| captured == value_id,
                .shared_place => false,
            };
        },
        .instruction_result => |origin| blk: {
            if (!validId(origin.instruction, program.instructions.len) or !scope.instruction(origin.instruction)) break :blk false;
            const instruction = program.instructions[origin.instruction.index()];
            if (instruction.id != origin.instruction or !validId(instruction.block, program.blocks.len) or
                program.blocks[instruction.block.index()].function != function_id) break :blk false;
            const result_index: usize = @intCast(origin.index);
            break :blk result_index < instruction.results.len and instruction.results[result_index] == value_id;
        },
        .block_parameter => |origin| blk: {
            if (!validId(origin.block, program.blocks.len) or !scope.block(origin.block)) break :blk false;
            const block = program.blocks[origin.block.index()];
            const parameter_index: usize = @intCast(origin.index);
            break :blk block.function == function_id and parameter_index < block.parameters.len and
                block.parameters[parameter_index] == value_id;
        },
    };
}

fn closureHasOnlySynchronousUses(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    roles: anytype,
    analysis: *const cfg.Analysis,
    producer_block: ir.BlockId,
    function_id: ir.FunctionId,
    instruction: ir.Instruction,
    closure: ir.Closure,
) !bool {
    if (!normalized_value.isExactPure(instruction.effects) or instruction.pack_result != null or instruction.results.len != 1 or
        !validId(closure.function, program.functions.len)) return false;
    const target = program.functions[closure.function.index()];
    if (target.lexical_parent == null or target.lexical_parent.? != function_id) return false;
    for (program.functions) |candidate| {
        if (candidate.lexical_parent != null and candidate.lexical_parent.? == closure.function) return false;
    }

    const closure_value = instruction.results[0];
    if (!closureValueIsCanonical(program, scope, function_id, closure_value)) return false;
    const origin = program.values[closure_value.index()].origin;
    if (origin != .instruction_result or origin.instruction_result.instruction != instruction.id or origin.instruction_result.index != 0) return false;

    const aliases = try allocator.alloc(bool, program.values.len);
    defer allocator.free(aliases);
    @memset(aliases, false);
    const definitions = try allocator.alloc(?ClosureAliasDefinition, program.values.len);
    defer allocator.free(definitions);
    @memset(definitions, null);
    aliases[closure_value.index()] = true;
    definitions[closure_value.index()] = .{ .instruction = instruction.id };
    try discoverClosureAliases(
        allocator,
        program,
        scope,
        analysis,
        producer_block,
        function_id,
        aliases,
        definitions,
    );

    var use_count: usize = 0;
    var accepted_use_count: usize = 0;
    var synchronous_use_count: usize = 0;
    for (program.instructions) |candidate| {
        if (!scope.instruction(candidate.id) or !validId(candidate.block, program.blocks.len) or
            program.blocks[candidate.block.index()].function != function_id) continue;
        runtime_uses.visitOperationUses(candidate.operation, ClosureAliasUseCounter{ .aliases = aliases, .count = &use_count });
        switch (candidate.operation) {
            .copy => |source| {
                if (!closureAliasContains(aliases, source)) continue;
                const result = canonicalClosureCopyResult(program, scope, function_id, candidate, source) orelse return false;
                if (!closureAliasContains(aliases, result) or definitions[result.index()] == null or
                    definitions[result.index()].? != .instruction or
                    definitions[result.index()].?.instruction != candidate.id) return false;
                const definition = closureAliasDefinition(program, definitions, source) orelse return false;
                if (!try closureAliasDefinitionIsFresh(
                    allocator,
                    program,
                    scope,
                    analysis,
                    producer_block,
                    function_id,
                    definition,
                    .{ .instruction = candidate },
                )) return false;
                accepted_use_count += 1;
            },
            .call => |call| {
                if (!closureAliasContains(aliases, call.callee)) continue;
                if (!synchronousInvocationResultsAreRenderable(roles, candidate, call.result_arity)) return false;
                const definition = closureAliasDefinition(program, definitions, call.callee) orelse return false;
                if (!try closureAliasDefinitionIsFresh(
                    allocator,
                    program,
                    scope,
                    analysis,
                    producer_block,
                    function_id,
                    definition,
                    .{ .instruction = candidate },
                )) return false;
                accepted_use_count += 1;
                synchronous_use_count += 1;
            },
            .protected_call => |call| {
                const callee_is_alias = closureAliasContains(aliases, call.callee);
                const handler_is_alias = call.error_handler != null and closureAliasContains(aliases, call.error_handler.?);
                if (!callee_is_alias and !handler_is_alias) continue;
                const protected_use_count = protectedCallSynchronousAliasUseCount(program, roles, aliases, candidate, call) orelse return false;
                const protected_aliases = [_]?ir.ValueId{
                    if (callee_is_alias) call.callee else null,
                    if (handler_is_alias) call.error_handler.? else null,
                };
                for (protected_aliases) |maybe_alias| {
                    const alias = maybe_alias orelse continue;
                    const definition = closureAliasDefinition(program, definitions, alias) orelse return false;
                    if (!try closureAliasDefinitionIsFresh(
                        allocator,
                        program,
                        scope,
                        analysis,
                        producer_block,
                        function_id,
                        definition,
                        .{ .instruction = candidate },
                    )) return false;
                }
                accepted_use_count += protected_use_count;
                synchronous_use_count += 1;
            },
            else => {},
        }
    }
    for (program.blocks) |block| {
        if (!scope.block(block.id) or block.function != function_id) continue;
        runtime_uses.visitTerminatorUses(block.terminator, ClosureAliasUseCounter{ .aliases = aliases, .count = &use_count });
    }
    for (definitions) |definition| {
        if (definition != null and definition.? == .block_parameter) accepted_use_count += 1;
    }
    return synchronous_use_count > 0 and use_count == accepted_use_count;
}

fn discoverClosureAliases(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    analysis: *const cfg.Analysis,
    producer_block: ir.BlockId,
    function_id: ir.FunctionId,
    aliases: []bool,
    definitions: []?ClosureAliasDefinition,
) !void {
    var changed = true;
    while (changed) {
        changed = false;
        for (program.instructions) |candidate| {
            if (!scope.instruction(candidate.id) or !validId(candidate.block, program.blocks.len) or
                program.blocks[candidate.block.index()].function != function_id) continue;
            const source = switch (candidate.operation) {
                .copy => |value| value,
                else => continue,
            };
            if (!closureAliasContains(aliases, source)) continue;
            const result = canonicalClosureCopyResult(program, scope, function_id, candidate, source) orelse continue;
            if (closureAliasContains(aliases, result)) continue;
            const definition = closureAliasDefinition(program, definitions, source) orelse continue;
            if (!try closureAliasDefinitionIsFresh(
                allocator,
                program,
                scope,
                analysis,
                producer_block,
                function_id,
                definition,
                .{ .instruction = candidate },
            )) continue;
            aliases[result.index()] = true;
            definitions[result.index()] = .{ .instruction = candidate.id };
            changed = true;
        }
        for (program.blocks) |block| {
            const predecessor_id = closureAliasTransferPredecessor(program, scope, analysis, function_id, block) orelse continue;
            const edge = program.blocks[predecessor_id.index()].terminator.jump;
            for (block.parameters, edge.arguments, 0..) |parameter, argument, index| {
                if (!closureAliasContains(aliases, argument) or closureAliasContains(aliases, parameter)) continue;
                if (parameter == argument or !canonicalClosureBlockParameter(program, scope, function_id, block, parameter, index)) continue;
                const definition = closureAliasDefinition(program, definitions, argument) orelse continue;
                if (!try closureAliasDefinitionIsFresh(
                    allocator,
                    program,
                    scope,
                    analysis,
                    producer_block,
                    function_id,
                    definition,
                    .{ .block_exit = predecessor_id },
                )) continue;
                aliases[parameter.index()] = true;
                definitions[parameter.index()] = .{ .block_parameter = block.id };
                changed = true;
            }
        }
    }
}

fn closureAliasTransferPredecessor(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    analysis: *const cfg.Analysis,
    function_id: ir.FunctionId,
    block: ir.Block,
) ?ir.BlockId {
    if (!validId(function_id, program.functions.len) or !validId(block.id, program.blocks.len) or
        program.blocks[block.id.index()].id != block.id or block.function != function_id or !scope.block(block.id) or
        program.functions[function_id.index()].entry_block == block.id or analysis.predecessorCount(block.id) != 1) return null;
    const predecessor_id = analysis.predecessorAt(block.id, 0) orelse return null;
    if (predecessor_id == block.id or !validId(predecessor_id, program.blocks.len) or !scope.block(predecessor_id)) return null;
    const predecessor = program.blocks[predecessor_id.index()];
    if (predecessor.function != function_id or predecessor.terminator != .jump) return null;
    const edge = predecessor.terminator.jump;
    if (edge.target != block.id or edge.arguments.len != block.parameters.len) return null;
    return predecessor_id;
}

fn canonicalClosureBlockParameter(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    function_id: ir.FunctionId,
    block: ir.Block,
    parameter: ir.ValueId,
    parameter_index: usize,
) bool {
    if (parameter_index >= block.parameters.len or block.parameters[parameter_index] != parameter or
        !closureValueIsCanonical(program, scope, function_id, parameter)) return false;
    const origin = program.values[parameter.index()].origin;
    return origin == .block_parameter and origin.block_parameter.block == block.id and
        origin.block_parameter.index == parameter_index;
}

fn canonicalClosureCopyResult(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    function_id: ir.FunctionId,
    instruction: ir.Instruction,
    source: ir.ValueId,
) ?ir.ValueId {
    const copied = switch (instruction.operation) {
        .copy => |value| value,
        else => return null,
    };
    if (copied != source or !scope.instruction(instruction.id) or !validId(instruction.block, program.blocks.len) or
        program.blocks[instruction.block.index()].function != function_id or !normalized_value.isExactPure(instruction.effects) or
        instruction.pack_result != null or instruction.results.len != 1) return null;
    const result = instruction.results[0];
    if (result == source or !closureValueIsCanonical(program, scope, function_id, result)) return null;
    const origin = program.values[result.index()].origin;
    if (origin != .instruction_result or origin.instruction_result.instruction != instruction.id or
        origin.instruction_result.index != 0) return null;
    return result;
}

fn closureAliasContains(aliases: []const bool, value_id: ir.ValueId) bool {
    return validId(value_id, aliases.len) and aliases[value_id.index()];
}

const ClosureAliasDefinition = union(enum) {
    instruction: ir.InstructionId,
    block_parameter: ir.BlockId,
};

fn closureAliasDefinition(
    program: *const ir.Program,
    definitions: []const ?ClosureAliasDefinition,
    value_id: ir.ValueId,
) ?ClosureAliasDefinition {
    if (!validId(value_id, definitions.len)) return null;
    const definition = definitions[value_id.index()] orelse return null;
    switch (definition) {
        .instruction => |instruction_id| {
            if (!validId(instruction_id, program.instructions.len) or
                program.instructions[instruction_id.index()].id != instruction_id) return null;
        },
        .block_parameter => |block_id| {
            if (!validId(block_id, program.blocks.len) or program.blocks[block_id.index()].id != block_id) return null;
        },
    }
    return definition;
}

const ClosureAliasUseLocation = union(enum) {
    instruction: ir.Instruction,
    block_exit: ir.BlockId,
};

fn closureAliasDefinitionIsFresh(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    analysis: *const cfg.Analysis,
    producer_block: ir.BlockId,
    function_id: ir.FunctionId,
    definition: ClosureAliasDefinition,
    use: ClosureAliasUseLocation,
) !bool {
    const use_block = switch (use) {
        .instruction => |instruction| blk: {
            if (!scope.instruction(instruction.id) or !validId(instruction.block, program.blocks.len) or
                program.blocks[instruction.block.index()].function != function_id) return false;
            break :blk instruction.block;
        },
        .block_exit => |block_id| blk: {
            if (!validId(block_id, program.blocks.len) or !scope.block(block_id) or
                program.blocks[block_id.index()].function != function_id) return false;
            break :blk block_id;
        },
    };
    const definition_block = switch (definition) {
        .instruction => |instruction_id| blk: {
            if (!validId(instruction_id, program.instructions.len) or !scope.instruction(instruction_id)) return false;
            const instruction = program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id or !validId(instruction.block, program.blocks.len) or
                program.blocks[instruction.block.index()].function != function_id) return false;
            if (instruction.block == use_block) return switch (use) {
                .instruction => |use_instruction| precedesInSameBlock(program, instruction, use_instruction),
                .block_exit => blockListsInstruction(program, use_block, instruction_id),
            };
            break :blk instruction.block;
        },
        .block_parameter => |block_id| blk: {
            if (!validId(block_id, program.blocks.len) or !scope.block(block_id) or
                program.blocks[block_id.index()].function != function_id) return false;
            if (block_id == use_block) return true;
            break :blk block_id;
        },
    };
    return closureAliasDefinitionBlockIsFreshAtBlock(
        allocator,
        program,
        scope,
        analysis,
        producer_block,
        function_id,
        definition_block,
        use_block,
    );
}

fn closureAliasDefinitionBlockIsFreshAtBlock(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    analysis: *const cfg.Analysis,
    producer_block: ir.BlockId,
    function_id: ir.FunctionId,
    definition_block: ir.BlockId,
    use_block: ir.BlockId,
) !bool {
    if (!validId(definition_block, program.blocks.len) or !validId(use_block, program.blocks.len) or
        !scope.block(definition_block) or !scope.block(use_block) or
        program.blocks[definition_block.index()].function != function_id or
        program.blocks[use_block.index()].function != function_id or
        !analysis.dominates(definition_block, use_block)) return false;
    if (producer_block == definition_block) return true;
    return !try hasReachablePathAvoidingBlock(
        allocator,
        program,
        scope,
        producer_block,
        use_block,
        function_id,
        definition_block,
    );
}

fn blockListsInstruction(program: *const ir.Program, block_id: ir.BlockId, instruction_id: ir.InstructionId) bool {
    if (!validId(block_id, program.blocks.len)) return false;
    for (program.blocks[block_id.index()].instructions) |listed_id| {
        if (listed_id == instruction_id) return true;
    }
    return false;
}

fn protectedCallSynchronousAliasUseCount(
    program: *const ir.Program,
    roles: anytype,
    aliases: []const bool,
    instruction: ir.Instruction,
    call: ir.ProtectedCall,
) ?usize {
    var alias_use_count: usize = @intFromBool(closureAliasContains(aliases, call.callee));
    if (call.error_handler) |handler| alias_use_count += @intFromBool(closureAliasContains(aliases, handler));
    for (call.arguments) |argument| {
        if (closureAliasContains(aliases, argument)) return null;
    }
    if (alias_use_count == 0 or !synchronousInvocationResultsAreRenderable(roles, instruction, call.result_arity)) return null;
    switch (call.result_arity) {
        .fixed => |count| {
            if (count == 0 or instruction.results.len != count) return null;
            const status_id = instruction.results[0];
            if (!validId(status_id, program.values.len)) return null;
            const status_kind = program.values[status_id.index()].type.kind;
            if (status_kind != .boolean and status_kind != .dynamic) return null;
        },
        .variadic => {
            const pack_id = instruction.pack_result orelse return null;
            if (!validId(pack_id, program.value_packs.len)) return null;
            const shape = program.value_packs[pack_id.index()].shape;
            if (shape.tail != .open or shape.prefix.len == 0 or shape.prefix[0].kind != .boolean) return null;
        },
    }
    return alias_use_count;
}

fn synchronousInvocationResultsAreRenderable(
    roles: anytype,
    instruction: ir.Instruction,
    result_arity: ir.ResultArity,
) bool {
    if (!validId(instruction.id, roles.len)) return false;
    return switch (result_arity) {
        .fixed => instruction.pack_result == null,
        .variadic => instruction.pack_result != null and switch (roles[instruction.id.index()]) {
            .fused_invocation_producer, .fused_return_producer => true,
            else => false,
        },
    };
}

const ClosureAliasUseCounter = struct {
    aliases: []const bool,
    count: *usize,

    pub fn value(self: ClosureAliasUseCounter, value_id: ir.ValueId) void {
        if (closureAliasContains(self.aliases, value_id)) self.count.* += 1;
    }

    pub fn pack(_: ClosureAliasUseCounter, _: ir.ValuePackId) void {}
    pub fn place(_: ClosureAliasUseCounter, _: ir.PlaceId) void {}
};

fn functionListsCapture(function: ir.Function, capture_id: ir.CaptureId) bool {
    for (function.captures) |listed_id| {
        if (listed_id == capture_id) return true;
    }
    return false;
}

fn functionListsLocalPlace(function: ir.Function, place_id: ir.PlaceId) bool {
    for (function.local_places) |listed_id| {
        if (listed_id == place_id) return true;
    }
    return false;
}

fn closureInstructionPlaceIsCanonical(
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    function_id: ir.FunctionId,
    place_id: ir.PlaceId,
) bool {
    if (!validId(function_id, program.functions.len) or !validId(place_id, program.places.len)) return false;
    const place = program.places[place_id.index()];
    if (place.function != function_id or place.origin != .instruction) return false;
    if (!functionListsLocalPlace(program.functions[function_id.index()], place_id)) return false;
    const instruction_id = place.origin.instruction;
    if (!validId(instruction_id, program.instructions.len) or !scope.instruction(instruction_id)) return false;
    const instruction = program.instructions[instruction_id.index()];
    if (instruction.id != instruction_id or !validId(instruction.block, program.blocks.len) or
        program.blocks[instruction.block.index()].function != function_id) return false;
    return switch (instruction.operation) {
        .place_write => |write| write.place == place_id,
        else => false,
    };
}

fn closurePlaceBindingIsStableRoot(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    analysis: *const cfg.Analysis,
    producer_block: ir.BlockId,
    function_id: ir.FunctionId,
    place_id: ir.PlaceId,
) !bool {
    if (!validId(function_id, program.functions.len) or !validId(place_id, program.places.len)) return false;
    const place = program.places[place_id.index()];
    if (place.function != function_id) return false;
    const function = program.functions[function_id.index()];
    return switch (place.origin) {
        .local => |local_index| blk: {
            const index: usize = @intCast(local_index);
            break :blk index < function.local_places.len and function.local_places[index] == place_id;
        },
        .capture => |capture_id| blk: {
            if (!validId(capture_id, program.captures.len)) break :blk false;
            if (!functionListsCapture(function, capture_id)) break :blk false;
            const capture = program.captures[capture_id.index()];
            if (capture.function != function_id) break :blk false;
            break :blk switch (capture.kind) {
                .shared_place => |captured| captured == place_id,
                .immutable_value => false,
            };
        },
        .instruction => |instruction_id| blk: {
            if (!closureInstructionPlaceIsCanonical(program, scope, function_id, place_id)) break :blk false;
            const instruction = program.instructions[instruction_id.index()];
            break :blk try blockIsStableBeforeProducer(
                allocator,
                program,
                scope,
                analysis,
                producer_block,
                function_id,
                instruction.block,
            );
        },
    };
}

fn blockIsStableBeforeProducer(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    analysis: *const cfg.Analysis,
    producer_block: ir.BlockId,
    function_id: ir.FunctionId,
    block_id: ir.BlockId,
) !bool {
    if (!validId(block_id, program.blocks.len) or !scope.block(block_id)) return false;
    const block = program.blocks[block_id.index()];
    if (block.function != function_id or block_id == producer_block or !analysis.dominates(block_id, producer_block)) return false;
    return !try hasReachablePath(allocator, program, scope, producer_block, block_id, function_id);
}

pub fn hasReachablePath(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    start: ir.BlockId,
    target: ir.BlockId,
    function_id: ir.FunctionId,
) !bool {
    return hasReachablePathFiltered(allocator, program, scope, start, target, function_id, null);
}

pub fn blockHasReachableReentry(analysis: *const cfg.Analysis, block_id: ir.BlockId) !bool {
    for (0..analysis.successorCount(block_id)) |index| {
        const successor = analysis.successorAt(block_id, index) orelse return true;
        if (try analysis.canReach(successor, block_id)) return true;
    }
    return false;
}

fn hasReachablePathAvoidingBlock(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    start: ir.BlockId,
    target: ir.BlockId,
    function_id: ir.FunctionId,
    forbidden: ir.BlockId,
) !bool {
    return hasReachablePathFiltered(allocator, program, scope, start, target, function_id, forbidden);
}

fn hasReachablePathFiltered(
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    scope: *const readable_scope.Scope,
    start: ir.BlockId,
    target: ir.BlockId,
    function_id: ir.FunctionId,
    forbidden: ?ir.BlockId,
) !bool {
    const visited = try allocator.alloc(bool, program.blocks.len);
    defer allocator.free(visited);
    @memset(visited, false);
    var pending: std.ArrayList(ir.BlockId) = .empty;
    defer pending.deinit(allocator);
    try pending.append(allocator, start);

    while (pending.pop()) |block_id| {
        if (!validId(block_id, program.blocks.len) or visited[block_id.index()] or !scope.block(block_id)) continue;
        if (forbidden != null and block_id == forbidden.?) continue;
        const block = program.blocks[block_id.index()];
        if (block.function != function_id) continue;
        if (block_id == target) return true;
        visited[block_id.index()] = true;
        switch (block.terminator) {
            .jump => |edge| try pending.append(allocator, edge.target),
            .branch => |branch| {
                try pending.append(allocator, branch.then_edge.target);
                try pending.append(allocator, branch.else_edge.target);
            },
            else => {},
        }
    }
    return false;
}

fn incrementCount(count: *u32) void {
    if (count.* != std.math.maxInt(u32)) count.* += 1;
}

fn validId(id: anytype, length: usize) bool {
    return id.index() < length;
}
