const std = @import("std");
const ir = @import("ir.zig");
const cfg = @import("cfg.zig");
const structure = @import("structure.zig");
const iteration_protocol = @import("iteration_protocol.zig");
const pack_plan = @import("pack_plan.zig");
const dead_code = @import("dead_code.zig");
const place_write_fusion = @import("place_write_fusion.zig");
const place_read_fusion = @import("place_read_fusion.zig");
const value_fusion = @import("value_fusion.zig");
const closure_store_fusion = @import("closure_store_fusion.zig");
const runtime_uses = @import("runtime_uses.zig");
const invocation_projection_witness = @import("invocation_projection_witness.zig");

pub const ScopeId = u32;
pub const invalid_scope = std.math.maxInt(ScopeId);

pub const GenericInitializerFusion = struct {
    adjustment: ir.InstructionId,
    producer: ir.InstructionId,
};

const max_region_nodes = 6;
const max_segment_instructions = 32;

const MovedLiteralInitializer = struct {
    instruction: ir.InstructionId,
    literal: ir.Literal,
};

pub const Plan = struct {
    allocator: std.mem.Allocator,
    program: *const ir.Program,
    function: ir.Function,
    analysis: *const cfg.Analysis,
    packs: *const pack_plan.Plan,
    dead: *const dead_code.Plan,
    place_writes: *const place_write_fusion.Plan,
    place_reads: *const place_read_fusion.Plan,
    fused_values: *const value_fusion.Plan,
    closure_stores: *const closure_store_fusion.Plan,
    parents: []ScopeId,
    depths: []u32,
    loop_hosts: []ScopeId,
    physical_hosts: []ScopeId,
    declaration_counts: []usize,
    node_scopes: std.AutoHashMapUnmanaged(*const structure.Node, ScopeId),
    block_scopes: []ScopeId,
    repeated_blocks: []bool,
    loop_header_blocks: []bool,
    native_iteration_headers: []bool,
    native_reentry_forwarders: []bool,
    instruction_scopes: []ScopeId,
    value_scopes: []ScopeId,
    pack_scopes: []ScopeId,
    place_scopes: []ScopeId,
    arbitrary_leaf_places: []bool,
    arbitrary_per_execution_cell_places: []bool,
    place_initializers: []?ir.InstructionId,
    moved_literal_initializers: []?MovedLiteralInitializer,
    synthetic_value_declarations: []bool,
    suppressed_control_values: []bool,
    suppressed_control_instructions: []bool,
    inline_root_group: ScopeId,
    arbitrary_cfg: bool,

    pub fn init(
        allocator: std.mem.Allocator,
        program: *const ir.Program,
        function: ir.Function,
        analysis: *const cfg.Analysis,
        structured: *const structure.Plan,
        packs: *const pack_plan.Plan,
        dead: *const dead_code.Plan,
        place_writes: *const place_write_fusion.Plan,
        place_reads: *const place_read_fusion.Plan,
        fused_values: *const value_fusion.Plan,
        closure_stores: *const closure_store_fusion.Plan,
    ) !Plan {
        var parents: std.ArrayList(ScopeId) = .empty;
        defer parents.deinit(allocator);
        var depths: std.ArrayList(u32) = .empty;
        defer depths.deinit(allocator);
        var loop_hosts: std.ArrayList(ScopeId) = .empty;
        defer loop_hosts.deinit(allocator);
        var physical_hosts: std.ArrayList(ScopeId) = .empty;
        defer physical_hosts.deinit(allocator);
        try parents.append(allocator, invalid_scope);
        try depths.append(allocator, 0);
        try loop_hosts.append(allocator, invalid_scope);
        try physical_hosts.append(allocator, 0);

        const block_scopes = try allocator.alloc(ScopeId, program.blocks.len);
        errdefer allocator.free(block_scopes);
        @memset(block_scopes, invalid_scope);
        const repeated_blocks = try allocator.alloc(bool, program.blocks.len);
        errdefer allocator.free(repeated_blocks);
        @memset(repeated_blocks, false);
        const loop_header_blocks = try allocator.alloc(bool, program.blocks.len);
        errdefer allocator.free(loop_header_blocks);
        @memset(loop_header_blocks, false);
        const native_iteration_headers = try allocator.alloc(bool, program.blocks.len);
        errdefer allocator.free(native_iteration_headers);
        @memset(native_iteration_headers, false);
        const native_reentry_forwarders = try allocator.alloc(bool, program.blocks.len);
        errdefer allocator.free(native_reentry_forwarders);
        @memset(native_reentry_forwarders, false);
        const instruction_scopes = try allocator.alloc(ScopeId, program.instructions.len);
        errdefer allocator.free(instruction_scopes);
        @memset(instruction_scopes, invalid_scope);
        const value_scopes = try allocator.alloc(ScopeId, program.values.len);
        errdefer allocator.free(value_scopes);
        @memset(value_scopes, invalid_scope);
        const pack_scopes = try allocator.alloc(ScopeId, program.value_packs.len);
        errdefer allocator.free(pack_scopes);
        @memset(pack_scopes, invalid_scope);
        const place_scopes = try allocator.alloc(ScopeId, program.places.len);
        errdefer allocator.free(place_scopes);
        @memset(place_scopes, invalid_scope);
        const arbitrary_leaf_places = try allocator.alloc(bool, program.places.len);
        errdefer allocator.free(arbitrary_leaf_places);
        @memset(arbitrary_leaf_places, false);
        const arbitrary_per_execution_cell_places = try allocator.alloc(bool, program.places.len);
        errdefer allocator.free(arbitrary_per_execution_cell_places);
        @memset(arbitrary_per_execution_cell_places, false);
        const place_initializers = try allocator.alloc(?ir.InstructionId, program.places.len);
        errdefer allocator.free(place_initializers);
        @memset(place_initializers, null);
        const moved_literal_initializers = try allocator.alloc(?MovedLiteralInitializer, program.places.len);
        errdefer allocator.free(moved_literal_initializers);
        @memset(moved_literal_initializers, null);
        const synthetic_value_declarations = try allocator.alloc(bool, program.values.len);
        errdefer allocator.free(synthetic_value_declarations);
        @memset(synthetic_value_declarations, false);
        const suppressed_control_values = try allocator.alloc(bool, program.values.len);
        errdefer allocator.free(suppressed_control_values);
        @memset(suppressed_control_values, false);
        const suppressed_control_instructions = try allocator.alloc(bool, program.instructions.len);
        errdefer allocator.free(suppressed_control_instructions);
        @memset(suppressed_control_instructions, false);

        var plan: Plan = .{
            .allocator = allocator,
            .program = program,
            .function = function,
            .analysis = analysis,
            .packs = packs,
            .dead = dead,
            .place_writes = place_writes,
            .place_reads = place_reads,
            .fused_values = fused_values,
            .closure_stores = closure_stores,
            .parents = &.{},
            .depths = &.{},
            .loop_hosts = &.{},
            .physical_hosts = &.{},
            .declaration_counts = &.{},
            .node_scopes = .empty,
            .block_scopes = block_scopes,
            .repeated_blocks = repeated_blocks,
            .loop_header_blocks = loop_header_blocks,
            .native_iteration_headers = native_iteration_headers,
            .native_reentry_forwarders = native_reentry_forwarders,
            .instruction_scopes = instruction_scopes,
            .value_scopes = value_scopes,
            .pack_scopes = pack_scopes,
            .place_scopes = place_scopes,
            .arbitrary_leaf_places = arbitrary_leaf_places,
            .arbitrary_per_execution_cell_places = arbitrary_per_execution_cell_places,
            .place_initializers = place_initializers,
            .moved_literal_initializers = moved_literal_initializers,
            .synthetic_value_declarations = synthetic_value_declarations,
            .suppressed_control_values = suppressed_control_values,
            .suppressed_control_instructions = suppressed_control_instructions,
            .inline_root_group = invalid_scope,
            .arbitrary_cfg = structured.root.arbitrary_cfg,
        };
        errdefer plan.node_scopes.deinit(allocator);

        try plan.indexRegion(&parents, &depths, &loop_hosts, &physical_hosts, structured.root, 0, invalid_scope, false);
        try plan.indexInstructionSegments(&parents, &depths, &loop_hosts, &physical_hosts);
        plan.parents = try parents.toOwnedSlice(allocator);
        errdefer allocator.free(plan.parents);
        plan.depths = try depths.toOwnedSlice(allocator);
        errdefer allocator.free(plan.depths);
        plan.loop_hosts = try loop_hosts.toOwnedSlice(allocator);
        errdefer allocator.free(plan.loop_hosts);
        plan.physical_hosts = try physical_hosts.toOwnedSlice(allocator);
        errdefer allocator.free(plan.physical_hosts);
        plan.inline_root_group = if (plan.entryHasIncomingEdge()) invalid_scope else plan.findInlineRootGroup(structured.root);

        plan.initializeDefinitions();
        plan.collectUses();
        plan.collectStructuredEdgeOverrideUses(structured.root);
        try plan.collectNativeIterationInitializerUses(structured.root);
        plan.hoistFunctionPlacesOutOfLoops();
        plan.findLocalPlaceInitializers();
        if (structured.root.arbitrary_cfg) try plan.findArbitraryLeafPlaces();

        plan.declaration_counts = try allocator.alloc(usize, plan.parents.len);
        errdefer allocator.free(plan.declaration_counts);
        @memset(plan.declaration_counts, 0);
        for (plan.value_scopes, 0..) |scope, index| {
            if (scope != invalid_scope and !plan.valueDeclaredAtInstruction(ir.ValueId.fromIndex(index))) {
                plan.declaration_counts[scope] += 1;
            }
        }
        for (plan.pack_scopes) |scope| {
            if (scope != invalid_scope) plan.declaration_counts[scope] += 1;
        }
        for (plan.place_scopes, 0..) |scope, index| {
            if (scope != invalid_scope and !plan.placeDeclaredAtInstruction(ir.PlaceId.fromIndex(index))) {
                plan.declaration_counts[scope] += 1;
            }
        }
        try plan.markNativeIterationDeclarations(structured.root);
        return plan;
    }

    pub fn deinit(self: *Plan) void {
        self.allocator.free(self.suppressed_control_instructions);
        self.allocator.free(self.suppressed_control_values);
        self.allocator.free(self.synthetic_value_declarations);
        self.allocator.free(self.moved_literal_initializers);
        self.allocator.free(self.place_initializers);
        self.allocator.free(self.arbitrary_leaf_places);
        self.allocator.free(self.arbitrary_per_execution_cell_places);
        self.allocator.free(self.place_scopes);
        self.allocator.free(self.pack_scopes);
        self.allocator.free(self.value_scopes);
        self.allocator.free(self.instruction_scopes);
        self.allocator.free(self.native_reentry_forwarders);
        self.allocator.free(self.native_iteration_headers);
        self.allocator.free(self.loop_header_blocks);
        self.allocator.free(self.repeated_blocks);
        self.allocator.free(self.block_scopes);
        self.node_scopes.deinit(self.allocator);
        self.allocator.free(self.declaration_counts);
        self.allocator.free(self.physical_hosts);
        self.allocator.free(self.loop_hosts);
        self.allocator.free(self.depths);
        self.allocator.free(self.parents);
        self.* = undefined;
    }

    pub fn rootScope(_: *const Plan) ScopeId {
        return 0;
    }

    pub fn nodeScope(self: *const Plan, node: *const structure.Node) ?ScopeId {
        return self.node_scopes.get(node);
    }

    pub fn nodeContainerScope(self: *const Plan, node: *const structure.Node) ?ScopeId {
        const scope = self.nodeScope(node) orelse return null;
        if (scope >= self.parents.len) return null;
        const parent = self.parents[scope];
        return if (parent == invalid_scope) null else parent;
    }

    pub fn blockScope(self: *const Plan, block_id: ir.BlockId) ?ScopeId {
        if (block_id.index() >= self.block_scopes.len) return null;
        const scope = self.block_scopes[block_id.index()];
        return if (scope == invalid_scope) null else scope;
    }

    pub fn instructionScope(self: *const Plan, instruction_id: ir.InstructionId) ?ScopeId {
        if (instruction_id.index() >= self.instruction_scopes.len) return null;
        const scope = self.instruction_scopes[instruction_id.index()];
        return if (scope == invalid_scope) null else scope;
    }

    pub fn renderedPressureScope(self: *const Plan, instruction_id: ir.InstructionId) ?ScopeId {
        if (instruction_id.index() >= self.program.instructions.len) return null;
        const scope = self.renderedInstructionScope(self.program.instructions[instruction_id.index()]);
        return if (scope == invalid_scope) null else scope;
    }

    pub fn valueScope(self: *const Plan, value_id: ir.ValueId) ?ScopeId {
        if (value_id.index() >= self.value_scopes.len) return null;
        const scope = self.value_scopes[value_id.index()];
        return if (scope == invalid_scope) null else scope;
    }

    pub fn packScope(self: *const Plan, pack_id: ir.ValuePackId) ?ScopeId {
        if (pack_id.index() >= self.pack_scopes.len) return null;
        const scope = self.pack_scopes[pack_id.index()];
        return if (scope == invalid_scope) null else scope;
    }

    pub fn placeScope(self: *const Plan, place_id: ir.PlaceId) ?ScopeId {
        if (place_id.index() >= self.place_scopes.len) return null;
        const scope = self.place_scopes[place_id.index()];
        return if (scope == invalid_scope) null else scope;
    }

    pub fn declarationCount(self: *const Plan, scope: ScopeId) usize {
        if (scope == invalid_scope or scope >= self.declaration_counts.len) return 0;
        return self.declaration_counts[scope];
    }

    pub fn pressureSlotCount(self: *const Plan) usize {
        return self.parents.len;
    }

    pub fn physicalHost(self: *const Plan, scope: ScopeId) ?ScopeId {
        if (scope == invalid_scope or scope >= self.physical_hosts.len) return null;
        return self.physical_hosts[scope];
    }

    pub fn parentPhysicalHost(self: *const Plan, host: ScopeId) ?ScopeId {
        if (host == invalid_scope or host >= self.parents.len or self.physicalHost(host) != host) return null;
        const parent = self.parents[host];
        if (parent == invalid_scope) return null;
        const parent_host = self.physicalHost(parent) orelse return null;
        return if (parent_host == host) null else parent_host;
    }

    pub fn scopesSharePhysicalBlock(self: *const Plan, left: ScopeId, right: ScopeId) bool {
        if (left == invalid_scope or right == invalid_scope or left >= self.physical_hosts.len or right >= self.physical_hosts.len) return false;
        return self.physical_hosts[left] == self.physical_hosts[right];
    }

    pub fn nativeIterationConsumesParameters(self: *const Plan, block_id: ir.BlockId) bool {
        return block_id.index() < self.native_iteration_headers.len and self.native_iteration_headers[block_id.index()];
    }

    /// No edge into this block writes a parameter copy: a native header (its loop statement holds the state) or a
    /// forwarding block on such a header's re-entry path (its parameters only carry the transition state there).
    /// Whether a node is written as a native loop is asked of `nativeIterationConsumesParameters` alone.
    pub fn edgeParametersConsumed(self: *const Plan, block_id: ir.BlockId) bool {
        if (self.nativeIterationConsumesParameters(block_id)) return true;
        return block_id.index() < self.native_reentry_forwarders.len and self.native_reentry_forwarders[block_id.index()];
    }

    pub fn instructionDeclaresResults(self: *const Plan, instruction_id: ir.InstructionId) bool {
        if (self.arbitrary_cfg) return false;
        if (instruction_id.index() >= self.program.instructions.len or instruction_id.index() >= self.instruction_scopes.len) return false;
        if (self.instructionSuppressedByControl(instruction_id)) return false;
        const instruction = self.program.instructions[instruction_id.index()];
        if (!instructionResultsAreMaterialized(self.packs, self.place_writes, self.place_reads, self.fused_values, self.closure_stores, instruction) or self.dead.contains(instruction_id)) return false;
        const binding_instruction = self.resultBindingInstruction(instruction) orelse return false;
        if (binding_instruction.id.index() >= self.instruction_scopes.len) return false;
        const scope = self.instruction_scopes[binding_instruction.id.index()];
        if (scope == invalid_scope) return false;
        for (instruction.results) |result| {
            if (result.index() >= self.value_scopes.len or !self.bindingDeclarationIsPhysical(self.value_scopes[result.index()], binding_instruction)) return false;
        }
        return true;
    }

    pub fn instructionDeclaresPlace(self: *const Plan, instruction_id: ir.InstructionId, place_id: ir.PlaceId) bool {
        if (self.arbitrary_cfg) return false;
        if (instruction_id.index() >= self.instruction_scopes.len or place_id.index() >= self.place_scopes.len or place_id.index() >= self.program.places.len) return false;
        if (self.place_initializers[place_id.index()]) |initializer| return initializer == instruction_id;
        const origin = switch (self.program.places[place_id.index()].origin) {
            .instruction => |value| value,
            else => return false,
        };
        return origin == instruction_id and
            self.instruction_scopes[instruction_id.index()] != invalid_scope and
            self.instruction_scopes[instruction_id.index()] == self.place_scopes[place_id.index()];
    }

    pub fn valueDeclaredAtInstruction(self: *const Plan, value_id: ir.ValueId) bool {
        if (value_id.index() >= self.program.values.len) return false;
        const instruction_id = switch (self.program.values[value_id.index()].origin) {
            .instruction_result => |origin| origin.instruction,
            else => return false,
        };
        return self.instructionDeclaresResults(instruction_id);
    }

    pub fn valueHasStableLexicalBinding(self: *const Plan, value_id: ir.ValueId) bool {
        if (value_id.index() >= self.program.values.len or self.program.values[value_id.index()].function != self.function.id) return false;
        return switch (self.program.values[value_id.index()].origin) {
            .parameter, .capture => true,
            .instruction_result => self.valueDeclaredAtInstruction(value_id),
            .block_parameter => self.valueDeclaredAtSyntheticSite(value_id),
        };
    }

    pub fn markSyntheticValueDeclaration(self: *Plan, value_id: ir.ValueId, scope: ScopeId) bool {
        if (value_id.index() >= self.value_scopes.len or value_id.index() >= self.synthetic_value_declarations.len) return false;
        if (scope == invalid_scope or scope >= self.declaration_counts.len or self.value_scopes[value_id.index()] != scope) return false;
        if (self.valueDeclaredAtInstruction(value_id) or self.synthetic_value_declarations[value_id.index()] or
            self.suppressed_control_values[value_id.index()]) return false;
        if (self.declaration_counts[scope] == 0) return false;
        self.synthetic_value_declarations[value_id.index()] = true;
        self.declaration_counts[scope] -= 1;
        return true;
    }

    pub fn valueDeclaredAtSyntheticSite(self: *const Plan, value_id: ir.ValueId) bool {
        return value_id.index() < self.synthetic_value_declarations.len and self.synthetic_value_declarations[value_id.index()];
    }

    pub fn valueSuppressedByControl(self: *const Plan, value_id: ir.ValueId) bool {
        return value_id.index() < self.suppressed_control_values.len and self.suppressed_control_values[value_id.index()];
    }

    pub fn instructionSuppressedByControl(self: *const Plan, instruction_id: ir.InstructionId) bool {
        return instruction_id.index() < self.suppressed_control_instructions.len and self.suppressed_control_instructions[instruction_id.index()];
    }

    fn markSuppressedControlValue(self: *Plan, value_id: ir.ValueId, scope: ScopeId) bool {
        if (value_id.index() >= self.value_scopes.len or value_id.index() >= self.suppressed_control_values.len) return false;
        if (scope == invalid_scope or scope >= self.declaration_counts.len or self.value_scopes[value_id.index()] != scope) return false;
        if (self.valueDeclaredAtInstruction(value_id) or self.synthetic_value_declarations[value_id.index()] or
            self.suppressed_control_values[value_id.index()]) return false;
        if (self.declaration_counts[scope] == 0) return false;
        self.suppressed_control_values[value_id.index()] = true;
        self.declaration_counts[scope] -= 1;
        return true;
    }

    pub fn placeDeclaredAtInstruction(self: *const Plan, place_id: ir.PlaceId) bool {
        if (place_id.index() >= self.program.places.len) return false;
        if (self.place_initializers[place_id.index()]) |initializer| return self.instructionDeclaresPlace(initializer, place_id);
        const instruction_id = switch (self.program.places[place_id.index()].origin) {
            .instruction => |value| value,
            else => return false,
        };
        return self.instructionDeclaresPlace(instruction_id, place_id);
    }

    /// Arbitrary-CFG (dispatcher) layout: whether `place_id` is declared
    /// `local` at its allocating write inside the allocating block's leaf
    /// instead of in the function's root list (`findArbitraryLeafPlaces`).
    pub fn arbitraryLeafDeclaresPlace(self: *const Plan, place_id: ir.PlaceId) bool {
        return place_id.index() < self.arbitrary_leaf_places.len and self.arbitrary_leaf_places[place_id.index()];
    }

    /// Arbitrary-CFG (dispatcher) layout: whether `place_id` needs a
    /// per-execution cell the flat layout cannot declare (a nested function
    /// reads it, it is used in several blocks, and its allocating block lies on
    /// a CFG cycle; `findArbitraryLeafPlaces`). Such a place is refused.
    pub fn arbitraryPlaceNeedsPerExecutionCell(self: *const Plan, place_id: ir.PlaceId) bool {
        return place_id.index() < self.arbitrary_per_execution_cell_places.len and self.arbitrary_per_execution_cell_places[place_id.index()];
    }

    /// Structured layout: a closure-captured loop cell must stay one declaration per pass. An instruction-origin
    /// place gets a fresh cell from every execution of its allocating write; its declaration scope is the common
    /// ancestor of that write and its uses (`addPlaceUse`). When that scope encloses loops around the write, every
    /// pass of those loops assigns one local declared before them, and a live `make_closure` of this function that
    /// binds the place inside the outermost of them captures that one local in every pass. Whether some place of this
    /// function is so: the writer then does not use this plan, and the dispatcher layout gives every execution of the
    /// write a fresh cell (`findArbitraryLeafPlaces`). A closure made only after those loops captures the cell of
    /// their last pass, which the one local holds.
    pub fn capturedCellSharedAcrossPasses(self: *const Plan) bool {
        if (self.arbitrary_cfg) return false;
        for (self.function.local_places) |place_id| {
            const loop = self.outermostLoopSharingDeclaration(place_id);
            if (loop != invalid_scope and self.placeBoundByClosureInLoop(place_id, loop)) return true;
        }
        return false;
    }

    // The outermost loop node around an instruction-origin place's allocating write whose statement the place's
    // declaration precedes, so that every pass of it assigns one local; invalid_scope when the write declares the
    // place or the declaration lies inside the innermost loop around the write.
    fn outermostLoopSharingDeclaration(self: *const Plan, place_id: ir.PlaceId) ScopeId {
        if (place_id.index() >= self.program.places.len or place_id.index() >= self.place_scopes.len) return invalid_scope;
        const allocation = switch (self.program.places[place_id.index()].origin) {
            .instruction => |instruction_id| instruction_id,
            .local, .capture => return invalid_scope,
        };
        if (allocation.index() >= self.program.instructions.len or allocation.index() >= self.instruction_scopes.len or
            self.dead.contains(allocation)) return invalid_scope;
        const place_scope = self.place_scopes[place_id.index()];
        const allocation_scope = self.instruction_scopes[allocation.index()];
        if (place_scope == invalid_scope or allocation_scope == invalid_scope or place_scope == allocation_scope) return invalid_scope;
        var outermost: ScopeId = invalid_scope;
        var loop = self.innermostLoopAround(allocation);
        while (loop != invalid_scope and self.mergeScopes(place_scope, loop) == place_scope) : (loop = self.loop_hosts[loop]) {
            outermost = loop;
        }
        return outermost;
    }

    // A `while` header runs once per pass in its loop node's own scope; any other instruction runs in the body of the
    // loop its scope's host names.
    fn innermostLoopAround(self: *const Plan, instruction_id: ir.InstructionId) ScopeId {
        if (instruction_id.index() >= self.program.instructions.len or instruction_id.index() >= self.instruction_scopes.len) return invalid_scope;
        const block_id = self.program.instructions[instruction_id.index()].block;
        if (block_id.index() >= self.block_scopes.len) return invalid_scope;
        if (self.loop_header_blocks[block_id.index()]) return self.block_scopes[block_id.index()];
        const scope = self.instruction_scopes[instruction_id.index()];
        return if (scope == invalid_scope) invalid_scope else self.loop_hosts[scope];
    }

    fn placeBoundByClosureInLoop(self: *const Plan, place_id: ir.PlaceId, loop: ScopeId) bool {
        for (self.function.blocks) |block_id| {
            if (block_id.index() >= self.program.blocks.len) continue;
            for (self.program.blocks[block_id.index()].instructions) |instruction_id| {
                if (instruction_id.index() >= self.program.instructions.len or self.dead.contains(instruction_id)) continue;
                if (!closureBindsPlace(self.program.instructions[instruction_id.index()].operation, place_id)) continue;
                var around = self.innermostLoopAround(instruction_id);
                while (around != invalid_scope) : (around = self.loop_hosts[around]) {
                    if (around == loop) return true;
                }
            }
        }
        return false;
    }

    pub fn placeMovedLiteralInitializer(self: *const Plan, place_id: ir.PlaceId) ?ir.Literal {
        if (place_id.index() >= self.moved_literal_initializers.len) return null;
        return if (self.moved_literal_initializers[place_id.index()]) |initializer| initializer.literal else null;
    }

    pub fn instructionIsMovedLiteralInitializer(self: *const Plan, instruction_id: ir.InstructionId) bool {
        if (instruction_id.index() >= self.program.instructions.len) return false;
        const place_id = switch (self.program.instructions[instruction_id.index()].operation) {
            .place_write => |write| write.place,
            else => return false,
        };
        if (place_id.index() >= self.moved_literal_initializers.len) return false;
        return if (self.moved_literal_initializers[place_id.index()]) |initializer| initializer.instruction == instruction_id else false;
    }

    fn addScope(
        parents: *std.ArrayList(ScopeId),
        depths: *std.ArrayList(u32),
        loop_hosts: *std.ArrayList(ScopeId),
        physical_hosts: *std.ArrayList(ScopeId),
        allocator: std.mem.Allocator,
        parent: ScopeId,
        loop_host: ScopeId,
        creates_physical_block: bool,
    ) !ScopeId {
        const id: ScopeId = @intCast(parents.items.len);
        try parents.append(allocator, parent);
        try depths.append(allocator, depths.items[parent] + 1);
        try loop_hosts.append(allocator, loop_host);
        try physical_hosts.append(allocator, if (creates_physical_block) id else physical_hosts.items[parent]);
        return id;
    }

    fn indexRegion(
        self: *Plan,
        parents: *std.ArrayList(ScopeId),
        depths: *std.ArrayList(u32),
        loop_hosts: *std.ArrayList(ScopeId),
        physical_hosts: *std.ArrayList(ScopeId),
        region: *const structure.Region,
        parent: ScopeId,
        enclosing_loop: ScopeId,
        enters_physical_block: bool,
    ) !void {
        if (region.arbitrary_cfg) {
            // Arbitrary CFG emission has one lexical function scope.  Do not
            // manufacture six-node containers for a graph that is not being
            // emitted as structured regions.
            for (region.nodes) |*node| {
                try self.node_scopes.put(self.allocator, node, self.rootScope());
                switch (node.*) {
                    .block => |block_id| self.assignBlock(block_id, self.rootScope(), false),
                    else => return error.UnsupportedControlFlow,
                }
            }
            return;
        }
        var container: ScopeId = invalid_scope;
        const wraps_groups = region.nodes.len > max_region_nodes;
        for (region.nodes, 0..) |*node, index| {
            if (index % max_region_nodes == 0) {
                container = try addScope(
                    parents,
                    depths,
                    loop_hosts,
                    physical_hosts,
                    self.allocator,
                    parent,
                    enclosing_loop,
                    enters_physical_block or wraps_groups,
                );
            }
            const scope = try addScope(parents, depths, loop_hosts, physical_hosts, self.allocator, container, enclosing_loop, false);
            try self.node_scopes.put(self.allocator, node, scope);
            const repeated = enclosing_loop != invalid_scope;
            switch (node.*) {
                .block => |block_id| self.assignBlock(block_id, scope, repeated),
                .branch => |branch| {
                    self.assignBlock(branch.block, scope, repeated);
                    try self.indexRegion(parents, depths, loop_hosts, physical_hosts, branch.then_region, scope, enclosing_loop, true);
                    try self.indexRegion(parents, depths, loop_hosts, physical_hosts, branch.else_region, scope, enclosing_loop, true);
                },
                .loop => |loop| {
                    if (loop.header.index() < self.loop_header_blocks.len) self.loop_header_blocks[loop.header.index()] = true;
                    self.assignBlock(loop.header, scope, true);
                    try self.indexRegion(parents, depths, loop_hosts, physical_hosts, loop.body_region, scope, scope, true);
                },
                .latch_loop => |loop| try self.indexRegion(parents, depths, loop_hosts, physical_hosts, loop.body_region, scope, scope, true),
                .infinite_loop => |loop| {
                    try self.indexRegion(parents, depths, loop_hosts, physical_hosts, loop.body_region, scope, scope, true);
                    if (loop.shared_side_exit) |side_exit| {
                        for (side_exit.entries) |entry| {
                            try self.indexRegion(parents, depths, loop_hosts, physical_hosts, entry.region, scope, enclosing_loop, true);
                        }
                    }
                },
                .loop_control => |control| self.assignBlock(control.block, scope, repeated),
                .loop_boundary => |control| {
                    self.assignBlock(control.block, scope, repeated);
                    try self.indexRegion(parents, depths, loop_hosts, physical_hosts, control.body_region, scope, enclosing_loop, true);
                    switch (control.boundary) {
                        .exit, .escape, .shared_exit => {},
                        .terminal => |terminal| self.assignBlock(terminal.block, scope, repeated),
                        .side_exit => |side_exit| try self.indexRegion(parents, depths, loop_hosts, physical_hosts, side_exit.region, scope, enclosing_loop, true),
                        .side_escape => |side_escape| try self.indexRegion(parents, depths, loop_hosts, physical_hosts, side_escape.region, scope, enclosing_loop, true),
                    }
                },
                .loop_terminal => |control| {
                    self.assignBlock(control.block, scope, repeated);
                    self.assignBlock(control.terminal_block, scope, repeated);
                },
            }
        }
    }

    fn assignBlock(self: *Plan, block_id: ir.BlockId, scope: ScopeId, repeated: bool) void {
        if (block_id.index() >= self.block_scopes.len) return;
        if (self.block_scopes[block_id.index()] == invalid_scope) self.block_scopes[block_id.index()] = scope;
        self.repeated_blocks[block_id.index()] = self.repeated_blocks[block_id.index()] or repeated;
    }

    fn indexInstructionSegments(
        self: *Plan,
        parents: *std.ArrayList(ScopeId),
        depths: *std.ArrayList(u32),
        loop_hosts: *std.ArrayList(ScopeId),
        physical_hosts: *std.ArrayList(ScopeId),
    ) !void {
        for (self.function.blocks) |block_id| {
            if (block_id.index() >= self.program.blocks.len or self.block_scopes[block_id.index()] == invalid_scope) continue;
            const block = self.program.blocks[block_id.index()];
            if (self.arbitrary_cfg) {
                for (block.instructions) |instruction_id| {
                    if (instruction_id.index() < self.instruction_scopes.len) {
                        self.instruction_scopes[instruction_id.index()] = self.rootScope();
                    }
                }
                continue;
            }
            if (block.instructions.len <= max_segment_instructions or self.renderedInstructionCountAtMost(block, max_segment_instructions) <= max_segment_instructions) {
                for (block.instructions) |instruction_id| {
                    if (instruction_id.index() < self.instruction_scopes.len) {
                        self.instruction_scopes[instruction_id.index()] = self.block_scopes[block_id.index()];
                    }
                }
                continue;
            }
            var index: usize = 0;
            while (index < block.instructions.len) {
                const parent = self.block_scopes[block_id.index()];
                const scope = try addScope(parents, depths, loop_hosts, physical_hosts, self.allocator, parent, loop_hosts.items[parent], true);
                const end = @min(index + max_segment_instructions, block.instructions.len);
                for (block.instructions[index..end]) |instruction_id| {
                    if (instruction_id.index() < self.instruction_scopes.len) self.instruction_scopes[instruction_id.index()] = scope;
                }
                index = end;
            }
        }
    }

    fn renderedInstructionCountAtMost(self: *const Plan, block: ir.Block, limit: usize) usize {
        var count: usize = 0;
        for (block.instructions) |instruction_id| {
            if (instruction_id.index() >= self.program.instructions.len) continue;
            const instruction = self.program.instructions[instruction_id.index()];
            if (!self.instructionContributesRenderedStatement(instruction)) continue;
            count += 1;
            if (count > limit) return count;
        }
        return count;
    }

    fn instructionContributesRenderedStatement(self: *const Plan, instruction: ir.Instruction) bool {
        if (self.dead.contains(instruction.id) or self.place_reads.contains(instruction.id) or self.fused_values.contains(instruction.id)) return false;
        if (self.closure_stores.consumerForProducer(instruction.id) != null or self.place_writes.consumerForProducer(instruction.id) != null) return false;
        return switch (self.packs.role(instruction.id)) {
            .fused_invocation_producer, .fused_return_producer => false,
            .materialized_adjustment => false,
            .materialized_adjustment_copy => instruction.results.len != 0,
            .stored_adjustment => instruction.results.len != 0,
            .direct_vararg_adjustment => instruction.results.len != 0,
            else => true,
        };
    }

    fn initializeDefinitions(self: *Plan) void {
        for (self.program.values) |value| {
            if (value.function != self.function.id) continue;
            switch (value.origin) {
                .parameter, .capture => {},
                .block_parameter => |origin| {
                    if (self.dead.isValueAlias(value.id) or origin.block.index() >= self.block_scopes.len) continue;
                    self.value_scopes[value.id.index()] = self.block_scopes[origin.block.index()];
                },
                .instruction_result => |origin| {
                    if (origin.instruction.index() >= self.program.instructions.len or self.dead.contains(origin.instruction)) continue;
                    const instruction = self.program.instructions[origin.instruction.index()];
                    if (!instructionResultsAreMaterialized(self.packs, self.place_writes, self.place_reads, self.fused_values, self.closure_stores, instruction)) continue;
                    const binding_instruction = self.resultBindingInstruction(instruction) orelse continue;
                    if (binding_instruction.id.index() >= self.instruction_scopes.len) continue;
                    self.value_scopes[value.id.index()] = self.instruction_scopes[binding_instruction.id.index()];
                },
            }
        }
        for (self.program.instructions) |instruction| {
            if (self.packs.role(instruction.id) != .stored_invocation_producer) continue;
            const pack_id = instruction.pack_result orelse continue;
            if (pack_id.index() >= self.pack_scopes.len or instruction.block.index() >= self.block_scopes.len) continue;
            self.pack_scopes[pack_id.index()] = self.block_scopes[instruction.block.index()];
        }
        for (self.function.local_places) |place_id| {
            if (place_id.index() >= self.program.places.len) continue;
            const place = self.program.places[place_id.index()];
            switch (place.origin) {
                .local, .capture => {},
                .instruction => |instruction_id| if (instruction_id.index() < self.instruction_scopes.len) {
                    self.place_scopes[place_id.index()] = self.instruction_scopes[instruction_id.index()];
                },
            }
        }
    }

    fn collectUses(self: *Plan) void {
        for (self.function.blocks) |block_id| {
            if (block_id.index() >= self.program.blocks.len) continue;
            const block_scope = self.block_scopes[block_id.index()];
            if (block_scope == invalid_scope) continue;
            const block = self.program.blocks[block_id.index()];
            for (block.instructions) |instruction_id| {
                if (instruction_id.index() >= self.program.instructions.len or self.dead.contains(instruction_id)) continue;
                const instruction = self.program.instructions[instruction_id.index()];
                const use_scope = self.renderedInstructionScope(instruction);
                if (use_scope == invalid_scope) continue;
                if (self.packs.role(instruction.id) == .materialized_adjustment_copy) {
                    const primary_id = self.packs.role(instruction.id).materialized_adjustment_copy;
                    if (primary_id.index() < self.program.instructions.len) {
                        const primary = self.program.instructions[primary_id.index()];
                        if (primary.results.len >= instruction.results.len) {
                            for (primary.results[0..instruction.results.len]) |value_id| self.addRenderedValueUse(value_id, use_scope);
                        }
                    }
                }
                runtime_uses.visitOperationUses(instruction.operation, UseVisitor{
                    .plan = self,
                    .scope = use_scope,
                    .remaining = self.renderedUseDepth(),
                });
            }
            runtime_uses.visitTerminatorUses(block.terminator, UseVisitor{
                .plan = self,
                .scope = block_scope,
                .remaining = self.renderedUseDepth(),
            });
            self.includeParameterAssignments(block.terminator, block_scope);
        }
    }

    fn collectStructuredEdgeOverrideUses(self: *Plan, region: *const structure.Region) void {
        for (region.nodes) |node| switch (node) {
            .block, .loop_control, .loop_terminal => {},
            .branch => |branch| {
                const scope = if (branch.block.index() < self.block_scopes.len)
                    self.block_scopes[branch.block.index()]
                else
                    invalid_scope;
                const overrides = [_]?structure.EdgeOverride{ branch.then_edge_override, branch.else_edge_override };
                if (scope != invalid_scope) for (overrides) |edge_override| if (edge_override) |value| {
                    const edge = value.edge();
                    for (edge.arguments) |argument| self.addRenderedValueUse(argument, scope);
                    self.includeParameterAssignment(edge, scope);
                };
                self.collectStructuredEdgeOverrideUses(branch.then_region);
                self.collectStructuredEdgeOverrideUses(branch.else_region);
            },
            .loop => |loop| self.collectStructuredEdgeOverrideUses(loop.body_region),
            .latch_loop => |loop| self.collectStructuredEdgeOverrideUses(loop.body_region),
            .infinite_loop => |loop| {
                self.collectStructuredEdgeOverrideUses(loop.body_region);
                if (loop.shared_side_exit) |side_exit| {
                    for (side_exit.entries) |entry| self.collectStructuredEdgeOverrideUses(entry.region);
                }
            },
            .loop_boundary => |control| {
                self.collectStructuredEdgeOverrideUses(control.body_region);
                switch (control.boundary) {
                    .side_exit => |side_exit| self.collectStructuredEdgeOverrideUses(side_exit.region),
                    .side_escape => |side_escape| self.collectStructuredEdgeOverrideUses(side_escape.region),
                    .exit, .escape, .terminal, .shared_exit => {},
                }
            },
        };
    }

    fn collectNativeIterationInitializerUses(self: *Plan, region: *const structure.Region) !void {
        for (region.nodes) |node| switch (node) {
            .block, .loop_control, .loop_terminal => {},
            .branch => |branch| {
                if (try iteration_protocol.matchAcyclicBranch(self.allocator, self.program, branch)) |acyclic| {
                    const scope = self.blockScope(branch.block) orelse invalid_scope;
                    const initial_arguments = switch (acyclic.protocol) {
                        .numeric => |numeric| numeric.initial_arguments,
                        .generic => |generic| generic.initial_arguments,
                    };
                    for (initial_arguments[0..@min(initial_arguments.len, 3)]) |value_id| {
                        self.addRenderedValueUse(value_id, scope);
                    }
                    switch (acyclic.protocol) {
                        .generic => |generic| self.addGenericInitializerProducerUses(generic.initial_arguments, branch.block, scope),
                        .numeric => {},
                    }
                }
                try self.collectNativeIterationInitializerUses(branch.then_region);
                try self.collectNativeIterationInitializerUses(branch.else_region);
            },
            .loop => |loop| {
                if (try iteration_protocol.matchLoop(self.allocator, self.program, loop)) |match| {
                    const scope = self.blockScope(loop.header) orelse invalid_scope;
                    const initial_arguments = switch (match) {
                        .numeric => |numeric| numeric.initial_arguments,
                        .generic => |generic| generic.initial_arguments,
                    };
                    for (initial_arguments[0..@min(initial_arguments.len, 3)]) |value_id| {
                        self.addRenderedValueUse(value_id, scope);
                    }
                    switch (match) {
                        .generic => |generic| self.addGenericInitializerProducerUses(generic.initial_arguments, loop.header, scope),
                        .numeric => {},
                    }
                }
                try self.collectNativeIterationInitializerUses(loop.body_region);
            },
            .latch_loop => |loop| try self.collectNativeIterationInitializerUses(loop.body_region),
            .infinite_loop => |loop| {
                try self.collectNativeIterationInitializerUses(loop.body_region);
                if (loop.shared_side_exit) |side_exit| {
                    for (side_exit.entries) |entry| try self.collectNativeIterationInitializerUses(entry.region);
                }
            },
            .loop_boundary => |control| {
                if (try iteration_protocol.matchAcyclicLoopBoundary(self.allocator, self.program, control)) |acyclic| {
                    const scope = self.blockScope(control.block) orelse invalid_scope;
                    const initial_arguments = switch (acyclic.protocol) {
                        .numeric => |numeric| numeric.initial_arguments,
                        .generic => |generic| generic.initial_arguments,
                    };
                    for (initial_arguments[0..@min(initial_arguments.len, 3)]) |value_id| {
                        self.addRenderedValueUse(value_id, scope);
                    }
                    switch (acyclic.protocol) {
                        .generic => |generic| self.addGenericInitializerProducerUses(generic.initial_arguments, control.block, scope),
                        .numeric => {},
                    }
                }
                try self.collectNativeIterationInitializerUses(control.body_region);
                switch (control.boundary) {
                    .side_exit => |side_exit| try self.collectNativeIterationInitializerUses(side_exit.region),
                    .side_escape => |side_escape| try self.collectNativeIterationInitializerUses(side_escape.region),
                    else => {},
                }
            },
        };
    }

    /// A fused generic initializer's producer is rendered on the native `for`
    /// line (`render.plannedInvocation` in `emitGenericForOpen`), so its callee
    /// or receiver, arguments and argument pack are read at the loop header,
    /// not in the preheader where activation suppresses it. Charge them at the
    /// header scope too, or a `do` group or segment that closes before the loop
    /// hides their declarations from the `for` line.
    fn addGenericInitializerProducerUses(self: *Plan, initial_arguments: []const ir.ValueId, header: ir.BlockId, scope: ScopeId) void {
        if (initial_arguments.len < 3) return;
        const fusion = self.genericInitializerFusion(initial_arguments[0..3], header) orelse return;
        if (fusion.producer.index() >= self.program.instructions.len) return;
        runtime_uses.visitOperationUses(self.program.instructions[fusion.producer.index()].operation, UseVisitor{
            .plan = self,
            .scope = scope,
            .remaining = self.renderedUseDepth(),
        });
    }

    fn hoistFunctionPlacesOutOfLoops(self: *Plan) void {
        for (self.function.local_places) |place_id| {
            if (place_id.index() >= self.program.places.len or self.program.places[place_id.index()].origin != .local) continue;
            var scope = self.place_scopes[place_id.index()];
            while (scope != invalid_scope and scope < self.loop_hosts.len) {
                const loop_host = self.loop_hosts[scope];
                if (loop_host == invalid_scope) break;
                scope = loop_host;
            }
            self.place_scopes[place_id.index()] = scope;
        }
    }

    fn findLocalPlaceInitializers(self: *Plan) void {
        for (self.function.local_places) |place_id| {
            if (place_id.index() >= self.program.places.len or self.program.places[place_id.index()].origin != .local) continue;
            if (self.findDominatingLocalPlaceInitializer(place_id)) |initializer| {
                self.place_initializers[place_id.index()] = initializer;
            }
        }

        if (self.function.entry_block.index() >= self.program.blocks.len or self.entryHasIncomingEdge()) return;
        const entry = self.program.blocks[self.function.entry_block.index()];
        for (self.function.local_places) |place_id| {
            if (place_id.index() >= self.program.places.len or
                self.program.places[place_id.index()].origin != .local or
                self.place_initializers[place_id.index()] != null) continue;
            for (entry.instructions) |instruction_id| {
                if (instruction_id.index() >= self.program.instructions.len) break;
                const instruction = self.program.instructions[instruction_id.index()];
                if (!operationUsesPlace(instruction.operation, place_id)) continue;
                const initializes = switch (instruction.operation) {
                    .place_write => |write| write.place == place_id,
                    else => false,
                };
                if (initializes) {
                    if (exactLiteralValue(self.program, self.dead, instruction.operation.place_write.value)) |literal| {
                        self.moved_literal_initializers[place_id.index()] = .{ .instruction = instruction_id, .literal = literal };
                    }
                }
                break;
            }
        }
    }

    /// Arbitrary-CFG (dispatcher) layout only. Marks each instruction-origin
    /// local place whose allocation `A` is a live instruction of this
    /// function, that a live `make_closure` of this function binds, and whose
    /// every live use (`operationUsesPlace`) lies in `A`'s block. A leaf is one
    /// block, so such a place is declared at `A` inside that block's leaf and
    /// every execution of `A` creates a fresh cell (Luau `local` semantics):
    /// closures created in a loop keep one cell per iteration. Every other
    /// place keeps its root declaration.
    ///
    /// Also marks (`arbitrary_per_execution_cell_places`) each place that a
    /// nested function reads, that is used in several blocks, and whose
    /// allocating block lies on a CFG cycle: it has no single Luau `local` that
    /// is both executed once per execution of the allocation and visible from
    /// every use, so the flat emitter boxes it — a holder in the
    /// root list, a fresh box per execution of the allocation, and a per-creation
    /// snapshot each closure reads through `[1]`. On no cycle the root
    /// declaration is one cell per activation, which is one per execution.
    fn findArbitraryLeafPlaces(self: *Plan) std.mem.Allocator.Error!void {
        for (self.function.local_places) |place_id| {
            if (place_id.index() >= self.program.places.len or place_id.index() >= self.arbitrary_leaf_places.len) continue;
            const allocation = switch (self.program.places[place_id.index()].origin) {
                .instruction => |allocation_id| allocation_id,
                .local, .capture => continue,
            };
            if (allocation.index() >= self.program.instructions.len or self.dead.contains(allocation)) continue;
            const allocation_block = self.program.instructions[allocation.index()].block;
            if (allocation_block.index() >= self.program.blocks.len or
                self.program.blocks[allocation_block.index()].function != self.function.id) continue;
            var captured = false;
            var single_block = true;
            for (self.function.blocks) |block_id| {
                if (block_id.index() >= self.program.blocks.len) continue;
                for (self.program.blocks[block_id.index()].instructions) |instruction_id| {
                    if (instruction_id.index() >= self.program.instructions.len or self.dead.contains(instruction_id)) continue;
                    const operation = self.program.instructions[instruction_id.index()].operation;
                    if (!operationUsesPlace(operation, place_id)) continue;
                    if (block_id != allocation_block) single_block = false;
                    if (closureBindsPlace(operation, place_id)) captured = true;
                }
            }
            self.arbitrary_leaf_places[place_id.index()] = captured and single_block;
            self.arbitrary_per_execution_cell_places[place_id.index()] = captured and !single_block and
                try self.analysis.canReachNonEmptyPath(allocation_block, allocation_block);
        }
    }

    fn findDominatingLocalPlaceInitializer(self: *const Plan, place_id: ir.PlaceId) ?ir.InstructionId {
        for (self.function.blocks) |block_id| {
            if (block_id.index() >= self.program.blocks.len or
                block_id.index() >= self.repeated_blocks.len or
                self.repeated_blocks[block_id.index()] or
                !self.analysis.isReachable(block_id)) continue;
            const block = self.program.blocks[block_id.index()];
            for (block.instructions, 0..) |instruction_id, instruction_index| {
                if (instruction_id.index() >= self.program.instructions.len or self.dead.contains(instruction_id)) continue;
                const instruction = self.program.instructions[instruction_id.index()];
                const write = switch (instruction.operation) {
                    .place_write => |value| value,
                    else => continue,
                };
                if (write.place != place_id or !self.initializerDeclarationIsPhysical(place_id, instruction)) continue;
                if (self.placeWriteDominatesEveryUse(place_id, block_id, instruction_index)) return instruction_id;
            }
        }
        return null;
    }

    fn placeWriteDominatesEveryUse(
        self: *const Plan,
        place_id: ir.PlaceId,
        initializer_block: ir.BlockId,
        initializer_index: usize,
    ) bool {
        var saw_initializer = false;
        for (self.function.blocks) |block_id| {
            if (block_id.index() >= self.program.blocks.len or !self.analysis.isReachable(block_id)) continue;
            const block = self.program.blocks[block_id.index()];
            for (block.instructions, 0..) |instruction_id, instruction_index| {
                if (instruction_id.index() >= self.program.instructions.len or self.dead.contains(instruction_id)) continue;
                const instruction = self.program.instructions[instruction_id.index()];
                if (!operationUsesPlace(instruction.operation, place_id)) continue;
                if (!self.analysis.dominates(initializer_block, block_id)) return false;
                if (block_id == initializer_block and instruction_index < initializer_index) return false;
                if (block_id == initializer_block and instruction_index == initializer_index) saw_initializer = true;
            }
        }
        return saw_initializer;
    }

    fn markNativeIterationDeclarations(self: *Plan, region: *const structure.Region) !void {
        for (region.nodes) |node| switch (node) {
            .block, .loop_control, .loop_terminal => {},
            .branch => |branch| {
                if (try iteration_protocol.matchAcyclicBranch(self.allocator, self.program, branch)) |acyclic| {
                    const initial_flag = switch (acyclic.protocol) {
                        .numeric => |numeric| numeric.initial_flag_instruction,
                        .generic => |generic| generic.initial_flag_instruction,
                    };
                    const body_parameters = self.program.blocks[acyclic.body_edge.target.index()].parameters;
                    const allow_aliased_header = switch (acyclic.protocol) {
                        .numeric => |numeric| numeric.operation.mode == .luau_numeric,
                        .generic => true,
                    };
                    const initial_arguments: ?[]const ir.ValueId = switch (acyclic.protocol) {
                        .numeric => null,
                        .generic => |generic| generic.initial_arguments[0..3],
                    };
                    const activated = try self.activateNativeIteration(
                        branch.block,
                        acyclic.protocol.instructionId(),
                        body_parameters,
                        initial_flag,
                        allow_aliased_header,
                        initial_arguments,
                    );
                    if (activated) {
                        self.native_iteration_headers[branch.block.index()] = true;
                    }
                }
                try self.markNativeIterationDeclarations(branch.then_region);
                try self.markNativeIterationDeclarations(branch.else_region);
            },
            .loop => |loop| {
                if (try iteration_protocol.matchLoop(self.allocator, self.program, loop)) |match| {
                    const activated = switch (match) {
                        .numeric => |numeric| try self.activateNativeIteration(
                            loop.header,
                            numeric.transition.id,
                            self.program.blocks[loop.body_edge.target.index()].parameters,
                            numeric.initial_flag_instruction,
                            false,
                            null,
                        ),
                        .generic => |generic| try self.activateNativeIteration(
                            loop.header,
                            generic.transition.id,
                            generic.body_parameters,
                            generic.initial_flag_instruction,
                            false,
                            generic.initial_arguments[0..3],
                        ),
                    };
                    if (activated) {
                        self.native_iteration_headers[loop.header.index()] = true;
                        self.markReentryForwarders(loop, match);
                    }
                }
                try self.markNativeIterationDeclarations(loop.body_region);
            },
            .latch_loop => |loop| try self.markNativeIterationDeclarations(loop.body_region),
            .infinite_loop => |loop| {
                try self.markNativeIterationDeclarations(loop.body_region);
                if (loop.shared_side_exit) |side_exit| {
                    for (side_exit.entries) |entry| try self.markNativeIterationDeclarations(entry.region);
                }
            },
            .loop_boundary => |control| {
                if (try iteration_protocol.matchAcyclicLoopBoundary(self.allocator, self.program, control)) |acyclic| {
                    const initial_flag = switch (acyclic.protocol) {
                        .numeric => |numeric| numeric.initial_flag_instruction,
                        .generic => |generic| generic.initial_flag_instruction,
                    };
                    const body_parameters = self.program.blocks[acyclic.body_edge.target.index()].parameters;
                    const allow_aliased_header = switch (acyclic.protocol) {
                        .numeric => |numeric| numeric.operation.mode == .luau_numeric,
                        .generic => true,
                    };
                    const initial_arguments: ?[]const ir.ValueId = switch (acyclic.protocol) {
                        .numeric => null,
                        .generic => |generic| generic.initial_arguments[0..3],
                    };
                    const activated = try self.activateNativeIteration(
                        control.block,
                        acyclic.protocol.instructionId(),
                        body_parameters,
                        initial_flag,
                        allow_aliased_header,
                        initial_arguments,
                    );
                    if (activated) {
                        self.native_iteration_headers[control.block.index()] = true;
                    }
                }
                try self.markNativeIterationDeclarations(control.body_region);
                switch (control.boundary) {
                    .side_exit => |side_exit| try self.markNativeIterationDeclarations(side_exit.region),
                    .side_escape => |side_escape| try self.markNativeIterationDeclarations(side_escape.region),
                    else => {},
                }
            },
        };
    }

    /// Marks the pure forwarding blocks on an activated cyclic native header's re-entry path, exactly the blocks the
    /// loop's match walks (`iteration_protocol.markReentryForwarders`), and suppresses the declarations of their
    /// parameters that are not value aliases: they only carry the transition state to the header, which the native
    /// loop computes itself, so no edge into them writes a copy and nothing reads them. A forwarder on the entry path
    /// carries the initializers the loop line reads and is not walked.
    fn markReentryForwarders(self: *Plan, loop: structure.Loop, match: iteration_protocol.Match) void {
        const transition = switch (match) {
            .numeric => |numeric| numeric.transition,
            .generic => |generic| generic.transition,
        };
        iteration_protocol.markReentryForwarders(self.program, self.analysis, loop, transition, self.native_reentry_forwarders);
        for (self.native_reentry_forwarders, 0..) |marked, index| {
            if (!marked) continue;
            for (self.program.blocks[index].parameters) |parameter| {
                if (self.dead.isValueAlias(parameter)) continue;
                _ = self.markSuppressedControlValue(parameter, self.value_scopes[parameter.index()]);
            }
        }
    }

    fn activateNativeIteration(
        self: *Plan,
        header_id: ir.BlockId,
        transition_instruction: ir.InstructionId,
        body_parameters: []const ir.ValueId,
        initial_flag_instruction: ?ir.InstructionId,
        allow_aliased_header: bool,
        initial_arguments: ?[]const ir.ValueId,
    ) !bool {
        if (header_id.index() >= self.program.blocks.len or header_id.index() >= self.native_iteration_headers.len) return false;
        if (transition_instruction.index() >= self.suppressed_control_instructions.len or
            self.suppressed_control_instructions[transition_instruction.index()]) return false;
        const initial_flag = if (initial_flag_instruction) |instruction_id| blk: {
            if (instruction_id.index() >= self.program.instructions.len or
                instruction_id.index() >= self.suppressed_control_instructions.len or
                self.suppressed_control_instructions[instruction_id.index()]) return false;
            const instruction = self.program.instructions[instruction_id.index()];
            if (instruction.id != instruction_id) return false;
            break :blk instruction;
        } else null;
        const generic_initializer = if (initial_arguments) |arguments|
            self.genericInitializerFusion(arguments, header_id)
        else
            null;
        const header_parameters = self.program.blocks[header_id.index()].parameters;
        const needed = try self.allocator.alloc(usize, self.declaration_counts.len);
        defer self.allocator.free(needed);
        @memset(needed, 0);
        if (!self.addNativeControlDeclarationNeeds(needed, header_parameters, allow_aliased_header) or
            !self.addNativeControlDeclarationNeeds(needed, body_parameters, false) or
            (initial_flag != null and !self.addSuppressedInstructionResultNeeds(needed, initial_flag.?)) or
            (generic_initializer != null and
                !self.addSuppressedInstructionResultNeeds(needed, self.program.instructions[generic_initializer.?.adjustment.index()]))) return false;
        for (needed, self.declaration_counts) |count, available| {
            if (count > available) return false;
        }
        for (header_parameters) |value_id| {
            if (allow_aliased_header and self.dead.isValueAlias(value_id)) continue;
            const scope = self.value_scopes[value_id.index()];
            std.debug.assert(self.markSuppressedControlValue(value_id, scope));
        }
        for (body_parameters) |value_id| {
            const scope = self.value_scopes[value_id.index()];
            std.debug.assert(self.markSyntheticValueDeclaration(value_id, scope));
        }
        if (initial_flag) |instruction| {
            for (instruction.results) |value_id| {
                const scope = self.value_scopes[value_id.index()];
                if (scope == invalid_scope or self.valueDeclaredAtInstruction(value_id)) {
                    self.suppressed_control_values[value_id.index()] = true;
                } else {
                    std.debug.assert(self.markSuppressedControlValue(value_id, scope));
                }
            }
            self.suppressed_control_instructions[instruction.id.index()] = true;
        }
        if (generic_initializer) |fusion| {
            const adjustment = self.program.instructions[fusion.adjustment.index()];
            for (adjustment.results) |value_id| {
                const scope = self.value_scopes[value_id.index()];
                if (scope == invalid_scope or self.valueDeclaredAtInstruction(value_id)) {
                    self.suppressed_control_values[value_id.index()] = true;
                } else {
                    std.debug.assert(self.markSuppressedControlValue(value_id, scope));
                }
            }
            self.suppressed_control_instructions[fusion.adjustment.index()] = true;
            self.suppressed_control_instructions[fusion.producer.index()] = true;
            self.suppressGenericIteratorStores(adjustment.results, body_parameters);
        }
        self.suppressed_control_instructions[transition_instruction.index()] = true;
        return true;
    }

    pub fn genericInitializerFusion(self: *const Plan, initial_arguments: []const ir.ValueId, header: ir.BlockId) ?GenericInitializerFusion {
        if (initial_arguments.len != 3) return null;
        var adjustment_id: ?ir.InstructionId = null;
        for (initial_arguments, 0..) |value_id, index| {
            const resolved = self.dead.resolveValue(value_id);
            if (resolved.index() >= self.program.values.len) return null;
            const origin = switch (self.program.values[resolved.index()].origin) {
                .instruction_result => |value| value,
                else => return null,
            };
            if (origin.index != index) return null;
            if (adjustment_id) |existing| {
                if (existing != origin.instruction) return null;
            } else {
                adjustment_id = origin.instruction;
            }
        }
        const adjustment = adjustment_id orelse return null;
        if (adjustment.index() >= self.program.instructions.len) return null;
        const instruction = self.program.instructions[adjustment.index()];
        if (instruction.results.len != 3 or instruction.id != adjustment) return null;
        switch (instruction.operation) {
            .adjust_pack => {},
            else => return null,
        }
        for (instruction.results, initial_arguments) |result, argument| {
            if (self.dead.resolveValue(result) != self.dead.resolveValue(argument)) return null;
        }
        const producer = switch (self.packs.role(adjustment)) {
            .fused_adjustment, .materialized_adjustment => |value| value,
            else => return null,
        };
        if (producer.index() >= self.program.instructions.len) return null;
        switch (self.packs.role(producer)) {
            .fused_invocation_producer, .materialized_invocation_producer => |consumer| if (consumer != adjustment) return null,
            else => return null,
        }
        if (!self.initializerKeepsEvaluationOrder(producer, adjustment, header)) return null;
        if (!self.initializerResultsReadOnlyAtHeader(producer, adjustment, header)) return null;
        return .{ .adjustment = adjustment, .producer = producer };
    }

    /// The fused producer is evaluated on the `for` line, so it may move there only
    /// when its block enters the loop header by a jump and every later instruction
    /// of that block but the adjustment is one an open invocation may move past
    /// (`invocation_projection_witness.invocationGapIsMovable`). A producer whose
    /// block jumps to the header runs once per loop entry, and a gap that is not
    /// movable keeps the producer and its adjustment in place, so the loop reads
    /// the three initial arguments in evaluation order.
    fn initializerKeepsEvaluationOrder(
        self: *const Plan,
        producer_id: ir.InstructionId,
        adjustment_id: ir.InstructionId,
        header: ir.BlockId,
    ) bool {
        const producer = self.program.instructions[producer_id.index()];
        if (producer.block.index() >= self.program.blocks.len) return false;
        const block = self.program.blocks[producer.block.index()];
        const entry = switch (block.terminator) {
            .jump => |edge| edge,
            else => return false,
        };
        if (entry.target != header) return false;
        var after_producer = false;
        for (block.instructions) |instruction_id| {
            if (instruction_id == producer_id) {
                after_producer = true;
                continue;
            }
            if (!after_producer or instruction_id == adjustment_id) continue;
            if (instruction_id.index() >= self.program.instructions.len) return false;
            if (!invocation_projection_witness.invocationGapIsMovable(self.program, self.program.instructions[instruction_id.index()])) return false;
        }
        return after_producer;
    }

    /// A fused producer is written on the `for` line and its three results lose their
    /// declarations, so the fusion stands only when nothing outside the loop header
    /// uses those results. The header block is the header's own use (its transition
    /// reads the header parameters, which the acyclic sites alias to the results), and
    /// so are the first three arguments of the entry jump. A result used anywhere else
    /// in the function, after the loop or in its body, keeps the producer and its
    /// adjustment in place, so the loop reads the three initial arguments
    /// and a read after the loop sees the call's result.
    fn initializerResultsReadOnlyAtHeader(
        self: *const Plan,
        producer_id: ir.InstructionId,
        adjustment_id: ir.InstructionId,
        header: ir.BlockId,
    ) bool {
        const entry_block = self.program.instructions[producer_id.index()].block;
        for (self.program.instructions[adjustment_id.index()].results) |result_id| {
            const result = self.dead.resolveValue(result_id);
            for (self.function.blocks) |block_id| {
                if (block_id == header) continue;
                if (block_id.index() >= self.program.blocks.len) return false;
                const block = self.program.blocks[block_id.index()];
                for (block.instructions) |instruction_id| {
                    if (instruction_id == adjustment_id) continue;
                    if (instruction_id.index() >= self.program.instructions.len) return false;
                    if (self.dead.contains(instruction_id) and !self.dead.isInlined(instruction_id)) continue;
                    if (self.dead.operationUsesValue(self.program.instructions[instruction_id.index()].operation, result)) return false;
                }
                if (block_id == entry_block) {
                    const entry = switch (block.terminator) {
                        .jump => |edge| edge,
                        else => return false,
                    };
                    for (entry.arguments, 0..) |argument, index| {
                        if (index >= 3 and self.dead.resolveValue(argument) == result) return false;
                    }
                } else if (self.dead.terminatorUsesValue(block.terminator, result)) return false;
            }
        }
        return true;
    }

    fn suppressGenericIteratorStores(self: *Plan, values: []const ir.ValueId, body_parameters: []const ir.ValueId) void {
        for (self.program.instructions) |instruction| {
            const store = switch (instruction.operation) {
                .environment_set => |value| value,
                else => continue,
            };
            if (store.target != .ambient or !std.mem.startsWith(u8, store.name, "__fs_for_")) continue;
            var value_matches = false;
            for (values) |value_id| {
                if (self.dead.resolveValue(value_id) == self.dead.resolveValue(store.value)) {
                    value_matches = true;
                    break;
                }
            }
            if (!value_matches and body_parameters.len != 0) {
                value_matches = self.dead.resolveValue(body_parameters[0]) == self.dead.resolveValue(store.value);
            }
            if (!value_matches) continue;
            if (instruction.id.index() < self.suppressed_control_instructions.len) {
                self.suppressed_control_instructions[instruction.id.index()] = true;
            }
        }
    }

    fn addNativeControlDeclarationNeeds(
        self: *const Plan,
        needed: []usize,
        values: []const ir.ValueId,
        allow_aliases: bool,
    ) bool {
        for (values) |value_id| {
            if (value_id.index() >= self.value_scopes.len or value_id.index() >= self.synthetic_value_declarations.len) return false;
            if (allow_aliases and self.dead.isValueAlias(value_id)) continue;
            const scope = self.value_scopes[value_id.index()];
            if (scope == invalid_scope or scope >= needed.len or self.valueDeclaredAtInstruction(value_id) or
                self.synthetic_value_declarations[value_id.index()] or
                self.suppressed_control_values[value_id.index()]) return false;
            needed[scope] += 1;
        }
        return true;
    }

    fn addSuppressedInstructionResultNeeds(
        self: *const Plan,
        needed: []usize,
        instruction: ir.Instruction,
    ) bool {
        for (instruction.results) |value_id| {
            if (value_id.index() >= self.value_scopes.len or value_id.index() >= self.suppressed_control_values.len) return false;
            if (self.synthetic_value_declarations[value_id.index()] or self.suppressed_control_values[value_id.index()]) return false;
            const scope = self.value_scopes[value_id.index()];
            if (scope == invalid_scope or self.valueDeclaredAtInstruction(value_id)) continue;
            if (scope >= needed.len) return false;
            needed[scope] += 1;
        }
        return true;
    }

    fn findInlineRootGroup(self: *const Plan, root: *const structure.Region) ScopeId {
        if (root.nodes.len == 0 or root.nodes[0].blockId() != self.function.entry_block) return invalid_scope;
        const group = self.nodeContainerScope(&root.nodes[0]) orelse return invalid_scope;
        for (root.nodes[1..]) |*node| {
            const node_group = self.nodeContainerScope(node) orelse return invalid_scope;
            if (node_group != group) return invalid_scope;
        }
        return group;
    }

    fn initializerDeclarationIsPhysical(self: *const Plan, place_id: ir.PlaceId, instruction: ir.Instruction) bool {
        if (place_id.index() >= self.place_scopes.len or instruction.id.index() >= self.instruction_scopes.len) return false;
        const place_scope = self.place_scopes[place_id.index()];
        const instruction_scope = self.instruction_scopes[instruction.id.index()];
        return self.scopesSharePhysicalBlock(place_scope, instruction_scope);
    }

    fn bindingDeclarationIsPhysical(self: *const Plan, binding_scope: ScopeId, instruction: ir.Instruction) bool {
        if (instruction.id.index() >= self.instruction_scopes.len) return false;
        const instruction_scope = self.instruction_scopes[instruction.id.index()];
        if (binding_scope == instruction_scope) return true;
        if (instruction.block.index() < self.repeated_blocks.len and instruction.block.index() < self.loop_header_blocks.len and
            (!self.repeated_blocks[instruction.block.index()] or !self.loop_header_blocks[instruction.block.index()]) and
            self.scopesSharePhysicalBlock(binding_scope, instruction_scope)) return true;
        if (self.inline_root_group == invalid_scope or instruction.block != self.function.entry_block) return false;
        if (instruction.block.index() >= self.block_scopes.len or self.block_scopes[instruction.block.index()] != instruction_scope) return false;
        if (instruction_scope >= self.parents.len or self.parents[instruction_scope] != self.inline_root_group) return false;
        return binding_scope == self.inline_root_group or binding_scope == self.rootScope();
    }

    fn resultBindingInstruction(self: *const Plan, instruction: ir.Instruction) ?ir.Instruction {
        const producer_id = switch (self.packs.role(instruction.id)) {
            .materialized_adjustment => |value| value,
            else => return instruction,
        };
        if (producer_id.index() >= self.program.instructions.len) return null;
        const producer = self.program.instructions[producer_id.index()];
        const consumer_id = switch (self.packs.role(producer_id)) {
            .materialized_invocation_producer => |value| value,
            else => return null,
        };
        return if (consumer_id == instruction.id) producer else null;
    }

    fn entryHasIncomingEdge(self: *const Plan) bool {
        return self.analysis.predecessorCount(self.function.entry_block) != 0;
    }

    fn renderedInstructionScope(self: *const Plan, instruction: ir.Instruction) ScopeId {
        return self.renderedInstructionScopeBounded(instruction, self.program.instructions.len + 1);
    }

    fn renderedInstructionScopeBounded(self: *const Plan, instruction: ir.Instruction, remaining: usize) ScopeId {
        if (remaining == 0) return invalid_scope;
        if (self.fused_values.consumer(instruction.id)) |consumer| switch (consumer) {
            .instruction => |consumer_id| return if (consumer_id.index() < self.program.instructions.len)
                self.renderedInstructionScopeBounded(self.program.instructions[consumer_id.index()], remaining - 1)
            else
                invalid_scope,
            .terminator => |block_id| return if (block_id.index() < self.block_scopes.len)
                self.block_scopes[block_id.index()]
            else
                invalid_scope,
        };
        if (self.place_reads.consumer(instruction.id)) |consumer| switch (consumer) {
            .instruction => |consumer_id| return if (consumer_id.index() < self.program.instructions.len)
                self.renderedInstructionScopeBounded(self.program.instructions[consumer_id.index()], remaining - 1)
            else
                invalid_scope,
            .terminator => |block_id| return if (block_id.index() < self.block_scopes.len)
                self.block_scopes[block_id.index()]
            else
                invalid_scope,
        };
        if (self.place_writes.consumerForProducer(instruction.id)) |consumer| {
            return if (consumer.index() < self.program.instructions.len)
                self.renderedInstructionScopeBounded(self.program.instructions[consumer.index()], remaining - 1)
            else
                invalid_scope;
        }
        if (self.closure_stores.consumerForProducer(instruction.id)) |consumer| {
            return if (consumer.index() < self.program.instructions.len)
                self.renderedInstructionScopeBounded(self.program.instructions[consumer.index()], remaining - 1)
            else
                invalid_scope;
        }
        return switch (self.packs.role(instruction.id)) {
            .fused_invocation_producer => |consumer| if (consumer.index() < self.program.instructions.len)
                self.renderedInstructionScopeBounded(self.program.instructions[consumer.index()], remaining - 1)
            else
                invalid_scope,
            .fused_return_producer => |block_id| if (block_id.index() < self.block_scopes.len)
                self.block_scopes[block_id.index()]
            else
                invalid_scope,
            .materialized_adjustment => invalid_scope,
            else => if (instruction.id.index() < self.instruction_scopes.len)
                self.instruction_scopes[instruction.id.index()]
            else
                invalid_scope,
        };
    }

    fn includeParameterAssignments(self: *Plan, terminator: ir.Terminator, assignment_scope: ScopeId) void {
        switch (terminator) {
            .jump => |edge| self.includeParameterAssignment(edge, assignment_scope),
            .branch => |branch| {
                self.includeParameterAssignment(branch.then_edge, assignment_scope);
                self.includeParameterAssignment(branch.else_edge, assignment_scope);
            },
            else => {},
        }
    }

    fn includeParameterAssignment(self: *Plan, edge: ir.Edge, assignment_scope: ScopeId) void {
        if (edge.target.index() >= self.program.blocks.len) return;
        for (self.program.blocks[edge.target.index()].parameters) |parameter| {
            if (self.dead.isValueAlias(parameter) or parameter.index() >= self.value_scopes.len) continue;
            self.mergeValueScope(parameter, assignment_scope);
        }
    }

    fn addRenderedValueUse(self: *Plan, value_id: ir.ValueId, scope: ScopeId) void {
        self.addRenderedValueUseBounded(value_id, scope, self.renderedUseDepth());
    }

    fn addRenderedValueUseBounded(self: *Plan, value_id: ir.ValueId, scope: ScopeId, remaining: usize) void {
        if (remaining == 0) return;
        const resolved = self.dead.resolveValue(value_id);
        if (resolved.index() >= self.program.values.len) return;
        const value = self.program.values[resolved.index()];
        if (value.function != self.function.id) return;
        const instruction_id = switch (value.origin) {
            .instruction_result => |origin| if (origin.index == 0) origin.instruction else null,
            else => null,
        };
        if (instruction_id) |id| {
            if (id.index() >= self.program.instructions.len) return;
            const instruction = self.program.instructions[id.index()];
            if (self.fused_values.contains(id) or self.dead.isInlined(id)) {
                runtime_uses.visitOperationUses(instruction.operation, UseVisitor{
                    .plan = self,
                    .scope = scope,
                    .remaining = remaining - 1,
                });
                return;
            }
            if (self.place_reads.contains(id)) {
                const place_id = switch (instruction.operation) {
                    .place_read => |place| place,
                    else => return,
                };
                self.addPlaceUse(place_id, scope);
                return;
            }
        }
        self.mergeValueScope(resolved, scope);
    }

    fn addRenderedPackUseBounded(self: *Plan, pack_id: ir.ValuePackId, scope: ScopeId, remaining: usize) void {
        if (remaining == 0 or pack_id.index() >= self.program.value_packs.len) return;
        const pack = self.program.value_packs[pack_id.index()];
        if (pack.function != self.function.id) return;
        const producer_id = switch (pack.origin) {
            .varargs => return,
            .instruction_result => |instruction_id| instruction_id,
        };
        if (producer_id.index() >= self.program.instructions.len) return;
        if (self.packs.role(producer_id) == .stored_invocation_producer) {
            self.pack_scopes[pack_id.index()] = self.mergeScopes(self.pack_scopes[pack_id.index()], scope);
            return;
        }
        runtime_uses.visitOperationUses(
            self.program.instructions[producer_id.index()].operation,
            UseVisitor{
                .plan = self,
                .scope = scope,
                .remaining = remaining - 1,
            },
        );
    }

    fn renderedUseDepth(self: *const Plan) usize {
        return self.program.instructions.len +| 1;
    }

    fn addPlaceUse(self: *Plan, place_id: ir.PlaceId, scope: ScopeId) void {
        if (place_id.index() >= self.program.places.len) return;
        const place = self.program.places[place_id.index()];
        if (place.function != self.function.id or place.origin == .capture) return;
        self.place_scopes[place_id.index()] = self.mergeScopes(self.place_scopes[place_id.index()], scope);
    }

    fn mergeValueScope(self: *Plan, value_id: ir.ValueId, scope: ScopeId) void {
        if (value_id.index() >= self.value_scopes.len or self.value_scopes[value_id.index()] == invalid_scope) return;
        self.value_scopes[value_id.index()] = self.mergeScopes(self.value_scopes[value_id.index()], scope);
    }

    fn mergeScopes(self: *const Plan, left_input: ScopeId, right_input: ScopeId) ScopeId {
        if (left_input == invalid_scope) return right_input;
        if (right_input == invalid_scope) return left_input;
        var left = left_input;
        var right = right_input;
        while (self.depths[left] > self.depths[right]) left = self.parents[left];
        while (self.depths[right] > self.depths[left]) right = self.parents[right];
        while (left != right) {
            left = self.parents[left];
            right = self.parents[right];
        }
        return left;
    }
};

const UseVisitor = struct {
    plan: *Plan,
    scope: ScopeId,
    remaining: usize,

    pub fn value(self: UseVisitor, value_id: ir.ValueId) void {
        self.plan.addRenderedValueUseBounded(value_id, self.scope, self.remaining);
    }

    pub fn pack(self: UseVisitor, pack_id: ir.ValuePackId) void {
        self.plan.addRenderedPackUseBounded(pack_id, self.scope, self.remaining);
    }

    pub fn place(self: UseVisitor, place_id: ir.PlaceId) void {
        self.plan.addPlaceUse(place_id, self.scope);
    }
};

fn operationUsesPlace(operation: ir.Operation, target: ir.PlaceId) bool {
    var found = false;
    runtime_uses.visitOperationUses(operation, PlaceUseVisitor{ .target = target, .found = &found });
    return found;
}

fn closureBindsPlace(operation: ir.Operation, target: ir.PlaceId) bool {
    const closure = switch (operation) {
        .make_closure => |value| value,
        else => return false,
    };
    for (closure.bindings) |binding| {
        switch (binding) {
            .place => |place_id| if (place_id == target) return true,
            .value => {},
        }
    }
    return false;
}

const PlaceUseVisitor = struct {
    target: ir.PlaceId,
    found: *bool,

    pub fn value(_: PlaceUseVisitor, _: ir.ValueId) void {}
    pub fn pack(_: PlaceUseVisitor, _: ir.ValuePackId) void {}

    pub fn place(self: PlaceUseVisitor, place_id: ir.PlaceId) void {
        if (place_id == self.target) self.found.* = true;
    }
};

fn exactLiteralValue(program: *const ir.Program, dead: *const dead_code.Plan, value_id: ir.ValueId) ?ir.Literal {
    const resolved = dead.resolveValue(value_id);
    if (resolved.index() >= program.values.len) return null;
    const origin = switch (program.values[resolved.index()].origin) {
        .instruction_result => |value| value,
        else => return null,
    };
    if (origin.index != 0 or origin.instruction.index() >= program.instructions.len) return null;
    return switch (program.instructions[origin.instruction.index()].operation) {
        .constant => |literal| literal,
        else => null,
    };
}

fn instructionResultsAreMaterialized(
    packs: *const pack_plan.Plan,
    place_writes: *const place_write_fusion.Plan,
    place_reads: *const place_read_fusion.Plan,
    fused_values: *const value_fusion.Plan,
    closure_stores: *const closure_store_fusion.Plan,
    instruction: ir.Instruction,
) bool {
    if (instruction.results.len == 0) return false;
    if (place_writes.consumerForProducer(instruction.id) != null) return false;
    if (place_reads.contains(instruction.id)) return false;
    if (fused_values.contains(instruction.id)) return false;
    if (closure_stores.consumerForProducer(instruction.id) != null) return false;
    switch (instruction.operation) {
        .numeric_for_next => |operation| return operation.mode == .semantic_normalized,
        .generic_for_next => return false,
        else => {},
    }
    return switch (packs.role(instruction.id)) {
        .fused_invocation_producer, .materialized_invocation_producer, .fused_return_producer => false,
        else => true,
    };
}

test "arbitrary CFG instruction results are not stable lexical bindings" {
    const function_id = ir.FunctionId.fromIndex(0);
    const block_id = ir.BlockId.fromIndex(0);
    const instruction_id = ir.InstructionId.fromIndex(0);
    const parameter = ir.ValueId.fromIndex(0);
    const capture = ir.ValueId.fromIndex(1);
    const instruction_result = ir.ValueId.fromIndex(2);
    const values = [_]ir.Value{
        .{ .id = parameter, .function = function_id, .origin = .{ .parameter = 0 } },
        .{ .id = capture, .function = function_id, .origin = .{ .capture = ir.CaptureId.fromIndex(0) } },
        .{ .id = instruction_result, .function = function_id, .origin = .{ .instruction_result = .{ .instruction = instruction_id, .index = 0 } } },
    };
    const block = ir.Block{
        .id = block_id,
        .function = function_id,
        .terminator = .{ .unreachable_block = {} },
    };
    const function = ir.Function{
        .id = function_id,
        .blocks = &.{block_id},
        .entry_block = block_id,
    };
    const program = ir.Program{
        .program_id = "arbitrary-cfg-stable-binding-test",
        .entry_function = function_id,
        .functions = &.{function},
        .blocks = &.{block},
        .instructions = &.{},
        .values = &values,
    };
    var plan: Plan = undefined;
    plan.program = &program;
    plan.function = function;
    plan.arbitrary_cfg = true;

    try std.testing.expect(plan.valueHasStableLexicalBinding(parameter));
    try std.testing.expect(plan.valueHasStableLexicalBinding(capture));
    try std.testing.expect(!plan.valueHasStableLexicalBinding(instruction_result));
}
