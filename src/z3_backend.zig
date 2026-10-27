const std = @import("std");
const ir = @import("ir.zig");
const backend = @import("solver_backend.zig");
const fact_solver = @import("solver.zig");
const normalized_value = @import("normalized_value.zig");
const numerals = @import("numerals.zig");
const solver_equivalence = @import("solver_equivalence.zig");
const solver_model = @import("solver_model.zig");
const proof_closure = @import("proof_closure.zig");

const c = @cImport({
    @cInclude("z3.h");
});

pub const enabled = true;

pub const Options = struct {
    timeout_ms: u32 = 5000,
    resource_limit: u32 = 0,
};

const default_options: Options = .{};

pub fn solverBackend(options: *const Options) backend.Backend {
    return .{
        .engine = .z3,
        .context = @ptrCast(@constCast(options)),
        .solve_fn = solveThunk,
    };
}

pub fn defaultBackend() backend.Backend {
    return solverBackend(&default_options);
}

pub fn version() []const u8 {
    return std.mem.span(c.Z3_get_full_version());
}

fn solveThunk(raw_options: ?*anyopaque, allocator: std.mem.Allocator, program: *const ir.Program, query: ir.SolverQuery) !backend.Result {
    const options: *const Options = if (raw_options) |pointer|
        @ptrCast(@alignCast(pointer))
    else
        &default_options;

    const config = c.Z3_mk_config() orelse return error.Z3ConfigCreationFailed;
    defer c.Z3_del_config(config);
    c.Z3_set_param_value(config, "unsat_core", "true");
    const context = c.Z3_mk_context(config) orelse return error.Z3ContextCreationFailed;
    defer c.Z3_del_context(context);

    const solver = c.Z3_mk_solver(context) orelse return error.Z3SolverCreationFailed;
    c.Z3_solver_inc_ref(context, solver);
    defer c.Z3_solver_dec_ref(context, solver);
    try applyLimits(context, solver, options.*);

    var closure = proof_closure.Closure.init(std.heap.page_allocator, program, query, &.{}, &.{}) catch |err| switch (err) {
        error.InvalidClosureInput => return error.InvalidSolverClosure,
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer closure.deinit();
    var translator = try Translator.init(std.heap.page_allocator, context, program);
    defer translator.deinit();
    try translator.translateNeeded(closure.terms);
    try translator.assertDynamicSemantics(solver);

    var tracked_assumptions: std.ArrayList(TrackedAssumption) = .empty;
    defer tracked_assumptions.deinit(allocator);
    for (query.assumptions, 0..) |constraint_id, assumption_index| {
        if (constraint_id.index() >= program.constraints.len) return error.InvalidConstraintReference;
        const predicate = program.constraints[constraint_id.index()].predicate;
        var name_buffer: [96]u8 = undefined;
        const name = try std.fmt.bufPrintZ(&name_buffer, "query_{d}_assumption_{d}_constraint_{d}", .{ query.id.index(), assumption_index, constraint_id.index() });
        const symbol = c.Z3_mk_string_symbol(context, name.ptr) orelse return error.Z3SymbolCreationFailed;
        const boolean_sort = c.Z3_mk_bool_sort(context) orelse return error.Z3SortCreationFailed;
        const tracking_literal = c.Z3_mk_const(context, symbol, boolean_sort) orelse return error.Z3AstCreationFailed;
        c.Z3_solver_assert_and_track(context, solver, try translator.get(predicate), tracking_literal);
        try tracked_assumptions.append(allocator, .{ .constraint = constraint_id, .literal = tracking_literal });
    }

    const goal = try translator.get(query.goal);
    const asserted_goal = switch (query.kind) {
        .prove_true, .prove_equivalent => c.Z3_mk_not(context, goal),
        .prove_false, .prove_unreachable, .find_model => goal,
    } orelse return error.Z3AstCreationFailed;
    c.Z3_solver_assert(context, solver, asserted_goal);

    const checked = c.Z3_solver_check(context, solver);
    // A satisfying model is kept only inside the region where every integer step is exact in Luau doubles.
    if (checked == c.Z3_L_TRUE and translator.region_conditions.items.len != 0) {
        const first_model = c.Z3_solver_get_model(context, solver) orelse return error.Z3ModelUnavailable;
        c.Z3_model_inc_ref(context, first_model);
        defer c.Z3_model_dec_ref(context, first_model);
        const inside_region = for (translator.region_conditions.items) |condition| {
            var evaluated: c.Z3_ast = null;
            if (!c.Z3_model_eval(context, first_model, condition, true, &evaluated) or evaluated == null) return error.Z3ModelEvaluationFailed;
            if (c.Z3_get_bool_value(context, evaluated) != c.Z3_L_TRUE) break false;
        } else true;
        if (!inside_region) {
            const region = c.Z3_mk_and(context, @intCast(translator.region_conditions.items.len), translator.region_conditions.items.ptr) orelse return error.Z3AstCreationFailed;
            c.Z3_solver_assert(context, solver, region);
            if (c.Z3_solver_check(context, solver) != c.Z3_L_TRUE) return .{
                .engine = .z3,
                .resolution = .unknown,
                .unknown_reason = .model_value_unrepresentability,
            };
        }
    }
    const resolution: ir.SolverResolution = switch (checked) {
        c.Z3_L_FALSE => if (query.kind == .find_model) .disproved else .proved,
        c.Z3_L_TRUE => if (query.kind == .find_model) .proved else .disproved,
        c.Z3_L_UNDEF => .unknown,
        else => return error.InvalidZ3Result,
    };
    var result: backend.Result = .{
        .engine = .z3,
        .resolution = resolution,
        .unknown_reason = if (checked == c.Z3_L_UNDEF) z3UnknownReason(context, solver, options.*) else null,
    };
    errdefer result.deinit(allocator);
    switch (checked) {
        c.Z3_L_FALSE => try collectUnsatCore(allocator, context, solver, tracked_assumptions.items, &result),
        c.Z3_L_TRUE => collectModel(allocator, context, solver, &translator, program, &result) catch |err| switch (err) {
            error.UnrepresentableSolverModelValue => {
                result.deinit(allocator);
                return .{
                    .engine = .z3,
                    .resolution = .unknown,
                    .unknown_reason = .model_value_unrepresentability,
                };
            },
            else => return err,
        },
        else => {},
    }
    return result;
}

fn z3UnknownReason(context: c.Z3_context, solver: c.Z3_solver, options: Options) backend.UnknownReason {
    const raw_reason = c.Z3_solver_get_reason_unknown(context, solver);
    if (raw_reason == null) return .backend_indeterminacy;
    return classifyUnknownReason(std.mem.span(raw_reason), options);
}

fn classifyUnknownReason(raw_reason: []const u8, options: Options) backend.UnknownReason {
    if (containsAsciiFolded(raw_reason, "resource") or containsAsciiFolded(raw_reason, "rlimit")) {
        return .resource_exhaustion;
    }
    if (containsAsciiFolded(raw_reason, "timeout")) return .timeout;
    if (containsAsciiFolded(raw_reason, "cancel")) {
        if (options.resource_limit != 0 and options.timeout_ms == 0) return .resource_exhaustion;
        if (options.timeout_ms != 0 and options.resource_limit == 0) return .timeout;
    }
    return .backend_indeterminacy;
}

fn containsAsciiFolded(haystack: []const u8, needle: []const u8) bool {
    if (needle.len == 0) return true;
    if (haystack.len < needle.len) return false;
    outer: for (0..haystack.len - needle.len + 1) |start| {
        for (needle, 0..) |expected, offset| {
            const actual = haystack[start + offset];
            const folded_actual = if (actual >= 'A' and actual <= 'Z') actual + ('a' - 'A') else actual;
            const folded_expected = if (expected >= 'A' and expected <= 'Z') expected + ('a' - 'A') else expected;
            if (folded_actual != folded_expected) continue :outer;
        }
        return true;
    }
    return false;
}

test "Z3 unknown reasons normalize at the native boundary" {
    try std.testing.expectEqual(
        backend.UnknownReason.timeout,
        classifyUnknownReason("timeout", .{}),
    );
    try std.testing.expectEqual(
        backend.UnknownReason.resource_exhaustion,
        classifyUnknownReason("max. resource limit exceeded", .{}),
    );
    try std.testing.expectEqual(
        backend.UnknownReason.timeout,
        classifyUnknownReason("canceled", .{ .timeout_ms = 1, .resource_limit = 0 }),
    );
    try std.testing.expectEqual(
        backend.UnknownReason.resource_exhaustion,
        classifyUnknownReason("canceled", .{ .timeout_ms = 0, .resource_limit = 1 }),
    );
    try std.testing.expectEqual(
        backend.UnknownReason.backend_indeterminacy,
        classifyUnknownReason("incomplete theory", .{}),
    );
}

const TrackedAssumption = struct {
    constraint: ir.ConstraintId,
    literal: c.Z3_ast,
};

fn collectUnsatCore(
    allocator: std.mem.Allocator,
    context: c.Z3_context,
    solver: c.Z3_solver,
    tracked: []const TrackedAssumption,
    result: *backend.Result,
) !void {
    const core = c.Z3_solver_get_unsat_core(context, solver) orelse return error.Z3UnsatCoreUnavailable;
    c.Z3_ast_vector_inc_ref(context, core);
    defer c.Z3_ast_vector_dec_ref(context, core);
    const core_size = c.Z3_ast_vector_size(context, core);
    for (tracked) |assumption| {
        var core_index: c_uint = 0;
        while (core_index < core_size) : (core_index += 1) {
            const core_literal = c.Z3_ast_vector_get(context, core, core_index) orelse return error.Z3AstCreationFailed;
            if (c.Z3_is_eq_ast(context, assumption.literal, core_literal)) {
                try result.unsat_core.append(allocator, assumption.constraint);
                break;
            }
        }
    }
}

fn collectModel(
    allocator: std.mem.Allocator,
    context: c.Z3_context,
    solver: c.Z3_solver,
    translator: *const Translator,
    program: *const ir.Program,
    result: *backend.Result,
) !void {
    const model = c.Z3_solver_get_model(context, solver) orelse return error.Z3ModelUnavailable;
    c.Z3_model_inc_ref(context, model);
    defer c.Z3_model_dec_ref(context, model);
    var dynamic_representatives: std.ArrayList(c.Z3_ast) = .empty;
    defer dynamic_representatives.deinit(allocator);
    for (program.solver_terms) |term| {
        if (!translator.has(term.id)) continue;
        switch (term.operation) {
            .value, .semantic_atom, .dynamic_truthiness, .dynamic_number_is_nan => {},
            else => continue,
        }
        var evaluated: c.Z3_ast = null;
        if (!c.Z3_model_eval(context, model, try translator.get(term.id), true, &evaluated) or evaluated == null) return error.Z3ModelEvaluationFailed;
        const value: ir.SolverModelValue = if (term.sort.kind == .dynamic_value)
            .{ .dynamic_identity = try dynamicIdentityForRepresentative(allocator, context, &dynamic_representatives, evaluated) }
        else
            try modelValueAlloc(allocator, context, term.sort, evaluated);
        errdefer freeModelValue(allocator, value);
        try result.model.append(allocator, .{ .term = term.id, .value = value });
    }
    switch (solver_model.dynamicBindingsCoherence(program, result.model.items)) {
        .coherent => {},
        .unrepresentable => return error.UnrepresentableSolverModelValue,
        .contradictory => return error.Z3ModelContradictsDynamicSemantics,
    }
}

fn dynamicIdentityForRepresentative(
    allocator: std.mem.Allocator,
    context: c.Z3_context,
    representatives: *std.ArrayList(c.Z3_ast),
    value: c.Z3_ast,
) !u32 {
    for (representatives.items, 0..) |representative, identity| {
        if (c.Z3_is_eq_ast(context, representative, value)) return @intCast(identity);
    }
    if (representatives.items.len > std.math.maxInt(u32)) return error.TooManyDynamicModelIdentities;
    const identity: u32 = @intCast(representatives.items.len);
    try representatives.append(allocator, value);
    return identity;
}

fn modelValueAlloc(allocator: std.mem.Allocator, context: c.Z3_context, sort: ir.SolverSort, value: c.Z3_ast) !ir.SolverModelValue {
    return switch (sort.kind) {
        .boolean => switch (c.Z3_get_bool_value(context, value)) {
            c.Z3_L_TRUE => .{ .boolean = true },
            c.Z3_L_FALSE => .{ .boolean = false },
            else => error.NonBooleanModelValue,
        },
        .integer => .{ .integer = try numeralAlloc(allocator, context, value) },
        .bit_vector => .{ .bit_vector = .{
            .value = try numeralAlloc(allocator, context, value),
            .bit_width = sort.bit_width,
        } },
        .real => .{ .real = try rationalAlloc(allocator, context, value) },
        .dynamic_value => error.DynamicModelValueUnavailable,
    };
}

fn numeralAlloc(allocator: std.mem.Allocator, context: c.Z3_context, value: c.Z3_ast) ![]u8 {
    const raw = c.Z3_get_numeral_string(context, value) orelse return error.Z3NumeralUnavailable;
    return allocator.dupe(u8, std.mem.span(raw));
}

fn rationalAlloc(allocator: std.mem.Allocator, context: c.Z3_context, value: c.Z3_ast) !ir.SolverRational {
    if (c.Z3_is_algebraic_number(context, value)) return error.UnrepresentableSolverModelValue;
    const raw = c.Z3_get_numeral_string(context, value) orelse return error.Z3NumeralUnavailable;
    const text = std.mem.span(raw);
    const slash = std.mem.indexOfScalar(u8, text, '/');
    const numerator_text = if (slash) |index| text[0..index] else text;
    const denominator_text = if (slash) |index| text[index + 1 ..] else "1";
    const numerator = try allocator.dupe(u8, numerator_text);
    errdefer allocator.free(numerator);
    const denominator = try allocator.dupe(u8, denominator_text);
    return .{ .numerator = numerator, .denominator = denominator };
}

fn freeModelValue(allocator: std.mem.Allocator, value: ir.SolverModelValue) void {
    switch (value) {
        .boolean => {},
        .integer => |integer| allocator.free(@constCast(integer)),
        .real => |real| {
            allocator.free(@constCast(real.numerator));
            allocator.free(@constCast(real.denominator));
        },
        .bit_vector => |bit_vector| allocator.free(@constCast(bit_vector.value)),
        .dynamic_identity => {},
    }
}

fn applyLimits(context: c.Z3_context, solver: c.Z3_solver, options: Options) !void {
    if (options.timeout_ms == 0 and options.resource_limit == 0) return;
    const parameters = c.Z3_mk_params(context) orelse return error.Z3ParamsCreationFailed;
    c.Z3_params_inc_ref(context, parameters);
    defer c.Z3_params_dec_ref(context, parameters);
    if (options.timeout_ms != 0) {
        const timeout_symbol = c.Z3_mk_string_symbol(context, "timeout") orelse return error.Z3SymbolCreationFailed;
        c.Z3_params_set_uint(context, parameters, timeout_symbol, options.timeout_ms);
    }
    if (options.resource_limit != 0) {
        const resource_symbol = c.Z3_mk_string_symbol(context, "rlimit") orelse return error.Z3SymbolCreationFailed;
        c.Z3_params_set_uint(context, parameters, resource_symbol, options.resource_limit);
    }
    c.Z3_solver_set_params(context, solver, parameters);
}

const DynamicAtom = struct {
    ast: c.Z3_ast,
    descriptor: ?solver_equivalence.DynamicDescriptor,
};

fn dynamicAtomsMustBeDistinct(left: DynamicAtom, right: DynamicAtom) bool {
    const left_descriptor = left.descriptor orelse return false;
    const right_descriptor = right.descriptor orelse return false;
    return solver_equivalence.dynamicDescriptorsDistinct(left_descriptor, right_descriptor);
}

const Translator = struct {
    allocator: std.mem.Allocator,
    context: c.Z3_context,
    program: *const ir.Program,
    terms: []c.Z3_ast,
    dynamic_sort: c.Z3_sort,
    dynamic_number_is_nan: c.Z3_func_decl,
    dynamic_atoms: std.ArrayList(DynamicAtom) = .empty,
    // Every model the solver returns must satisfy these conditions, the region where integer steps are exact in Luau doubles.
    region_conditions: std.ArrayList(c.Z3_ast) = .empty,

    fn init(allocator: std.mem.Allocator, context: c.Z3_context, program: *const ir.Program) !Translator {
        const terms = try allocator.alloc(c.Z3_ast, program.solver_terms.len);
        errdefer allocator.free(terms);
        @memset(terms, null);
        const dynamic_symbol = c.Z3_mk_string_symbol(context, "lifter_dynamic_value") orelse return error.Z3SymbolCreationFailed;
        const dynamic_sort = c.Z3_mk_uninterpreted_sort(context, dynamic_symbol) orelse return error.Z3SortCreationFailed;
        const boolean_sort = c.Z3_mk_bool_sort(context) orelse return error.Z3SortCreationFailed;
        const nan_symbol = c.Z3_mk_string_symbol(context, "lifter_dynamic_number_is_nan") orelse return error.Z3SymbolCreationFailed;
        var nan_domain = [_]c.Z3_sort{dynamic_sort};
        const dynamic_number_is_nan = c.Z3_mk_func_decl(context, nan_symbol, nan_domain.len, &nan_domain, boolean_sort) orelse return error.Z3AstCreationFailed;
        return .{
            .allocator = allocator,
            .context = context,
            .program = program,
            .terms = terms,
            .dynamic_sort = dynamic_sort,
            .dynamic_number_is_nan = dynamic_number_is_nan,
        };
    }

    fn deinit(self: *Translator) void {
        self.dynamic_atoms.deinit(self.allocator);
        self.region_conditions.deinit(self.allocator);
        self.allocator.free(self.terms);
    }

    fn translateNeeded(self: *Translator, needed: []const bool) !void {
        if (needed.len != self.program.solver_terms.len) return error.InvalidSolverClosure;
        for (self.program.solver_terms, 0..) |term, index| {
            if (term.id.index() != index) return error.NoncanonicalSolverTermId;
            if (!needed[index]) continue;
            self.terms[index] = try self.translate(term);
        }
    }

    fn assertDynamicSemantics(self: *const Translator, solver: c.Z3_solver) !void {
        for (self.dynamic_atoms.items, 0..) |right, right_index| {
            for (self.dynamic_atoms.items[0..right_index]) |left| {
                if (!dynamicAtomsMustBeDistinct(left, right)) continue;
                const equal = c.Z3_mk_eq(self.context, left.ast, right.ast) orelse return error.Z3AstCreationFailed;
                const distinct = c.Z3_mk_not(self.context, equal) orelse return error.Z3AstCreationFailed;
                c.Z3_solver_assert(self.context, solver, distinct);
            }
        }
        for (self.dynamic_atoms.items) |atom| {
            const descriptor = atom.descriptor orelse continue;
            if (descriptor.category != .boolean or descriptor.exact_boolean != null) continue;
            const false_equal = c.Z3_mk_eq(self.context, atom.ast, try self.dynamicBooleanAst(false)) orelse return error.Z3AstCreationFailed;
            const true_equal = c.Z3_mk_eq(self.context, atom.ast, try self.dynamicBooleanAst(true)) orelse return error.Z3AstCreationFailed;
            var choices = [_]c.Z3_ast{ false_equal, true_equal };
            const domain = c.Z3_mk_or(self.context, choices.len, &choices) orelse return error.Z3AstCreationFailed;
            c.Z3_solver_assert(self.context, solver, domain);
        }
    }

    fn dynamicBooleanAst(self: *const Translator, value: bool) !c.Z3_ast {
        for (self.dynamic_atoms.items) |atom| {
            const descriptor = atom.descriptor orelse continue;
            if (descriptor.category == .boolean and descriptor.exact_boolean == value) return atom.ast;
        }
        return error.DynamicBooleanDomainMissing;
    }

    fn has(self: *const Translator, term_id: ir.SolverTermId) bool {
        return term_id.index() < self.terms.len and self.terms[term_id.index()] != null;
    }

    fn get(self: *const Translator, term_id: ir.SolverTermId) !c.Z3_ast {
        if (term_id.index() >= self.terms.len) return error.InvalidSolverTermReference;
        return self.terms[term_id.index()] orelse error.UntranslatedSolverTerm;
    }

    fn translate(self: *Translator, term: ir.SolverTerm) !c.Z3_ast {
        return switch (term.operation) {
            .value => |value_id| self.translateValue(term.sort, value_id),
            // A value definition is exact only inside the region where its integer steps stay within 2^53.
            .value_definition => |definition| self.translateDefinition(term.sort, definition),
            .semantic_atom => |atom| self.translateSemanticAtom(term.sort, atom),
            .dynamic_truthiness => |operand| self.translateDynamicTruthiness(operand),
            .dynamic_number_is_nan => |operand| self.translateDynamicNumberIsNaN(operand),
            .boolean_literal => |value| (if (value) c.Z3_mk_true(self.context) else c.Z3_mk_false(self.context)) orelse error.Z3AstCreationFailed,
            .integer_literal => |value| self.translateNumeral(term.sort, value),
            .real_literal => |value| self.translateRational(value),
            .bit_vector_literal => |literal| self.translateNumeral(term.sort, literal.value),
            .logical_not => |operand| c.Z3_mk_not(self.context, try self.get(operand)) orelse error.Z3AstCreationFailed,
            .binary => |binary| self.translateBinary(term.sort, binary),
            .if_then_else => |selection| c.Z3_mk_ite(
                self.context,
                try self.get(selection.condition),
                try self.get(selection.then_term),
                try self.get(selection.else_term),
            ) orelse error.Z3AstCreationFailed,
            .bit_vector_not => |operand| c.Z3_mk_bvnot(self.context, try self.get(operand)) orelse error.Z3AstCreationFailed,
            .bit_vector_extract => |extract| c.Z3_mk_extract(
                self.context,
                extract.high,
                extract.low,
                try self.get(extract.operand),
            ) orelse error.Z3AstCreationFailed,
            .bit_vector_concat => |concat| c.Z3_mk_concat(
                self.context,
                try self.get(concat.high),
                try self.get(concat.low),
            ) orelse error.Z3AstCreationFailed,
            .bit_vector_extend => |extension| switch (extension.mode) {
                .zero => c.Z3_mk_zero_ext(self.context, extension.extra_bits, try self.get(extension.operand)) orelse error.Z3AstCreationFailed,
                .sign => c.Z3_mk_sign_ext(self.context, extension.extra_bits, try self.get(extension.operand)) orelse error.Z3AstCreationFailed,
            },
            .bit_vector_rotate => |rotation| switch (rotation.direction) {
                .left => c.Z3_mk_ext_rotate_left(
                    self.context,
                    try self.get(rotation.operand),
                    try self.get(rotation.amount),
                ) orelse error.Z3AstCreationFailed,
                .right => c.Z3_mk_ext_rotate_right(
                    self.context,
                    try self.get(rotation.operand),
                    try self.get(rotation.amount),
                ) orelse error.Z3AstCreationFailed,
            },
            .integer_to_bit_vector => |operand| c.Z3_mk_int2bv(
                self.context,
                term.sort.bit_width,
                try self.get(operand),
            ) orelse error.Z3AstCreationFailed,
            .bit_vector_to_integer => |conversion| c.Z3_mk_bv2int(
                self.context,
                try self.get(conversion.operand),
                conversion.signed,
            ) orelse error.Z3AstCreationFailed,
            .arithmetic_negate => |operand| if (term.sort.kind == .bit_vector)
                c.Z3_mk_bvneg(self.context, try self.get(operand)) orelse error.Z3AstCreationFailed
            else
                c.Z3_mk_unary_minus(self.context, try self.get(operand)) orelse error.Z3AstCreationFailed,
            .is_nonzero => |operand| self.translateNonzero(operand),
            .division => |division| self.translateDivision(division),
            .remainder => |remainder| self.translateRemainder(remainder),
        };
    }

    // Outside its exact region a value definition takes the Luau rounded result of its one operation, or stays free.
    fn translateDefinition(self: *Translator, sort: ir.SolverSort, definition: ir.SolverValueDefinition) !c.Z3_ast {
        const expression = try self.get(definition.expression);
        const terms = self.program.solver_terms;
        const visited = try self.allocator.alloc(bool, terms.len);
        defer self.allocator.free(visited);
        @memset(visited, false);
        var pending: std.ArrayList(ir.SolverTermId) = .empty;
        defer pending.deinit(self.allocator);
        var conditions: std.ArrayList(c.Z3_ast) = .empty;
        defer conditions.deinit(self.allocator);
        try pending.append(self.allocator, definition.expression);
        while (pending.pop()) |term_id| {
            if (term_id.index() >= terms.len) return error.InvalidSolverTermReference;
            if (visited[term_id.index()] or !self.has(term_id)) continue;
            visited[term_id.index()] = true;
            switch (terms[term_id.index()].operation) {
                .value, .value_definition, .semantic_atom, .boolean_literal, .real_literal, .bit_vector_literal => {},
                .integer_literal => |decimal| if (!exactLuauDecimal(decimal)) {
                    try conditions.append(self.allocator, c.Z3_mk_false(self.context) orelse return error.Z3AstCreationFailed);
                },
                .dynamic_truthiness, .dynamic_number_is_nan, .logical_not, .bit_vector_not, .integer_to_bit_vector, .arithmetic_negate, .is_nonzero => |operand| {
                    try pending.append(self.allocator, operand);
                },
                .binary => |binary| {
                    if (binary.left.index() >= terms.len) return error.InvalidSolverTermReference;
                    const arithmetic = binary.operator == .add or binary.operator == .subtract or binary.operator == .multiply;
                    if (arithmetic and terms[binary.left.index()].sort.kind == .integer) {
                        try conditions.append(self.allocator, try self.luauExactRange(try self.get(term_id)));
                    }
                    try pending.append(self.allocator, binary.left);
                    try pending.append(self.allocator, binary.right);
                },
                .if_then_else => |selection| {
                    try pending.append(self.allocator, selection.condition);
                    try pending.append(self.allocator, selection.then_term);
                    try pending.append(self.allocator, selection.else_term);
                },
                .bit_vector_extract => |extract| try pending.append(self.allocator, extract.operand),
                .bit_vector_concat => |concat| {
                    try pending.append(self.allocator, concat.high);
                    try pending.append(self.allocator, concat.low);
                },
                .bit_vector_extend => |extension| try pending.append(self.allocator, extension.operand),
                .bit_vector_rotate => |rotation| {
                    try pending.append(self.allocator, rotation.operand);
                    try pending.append(self.allocator, rotation.amount);
                },
                .bit_vector_to_integer => |conversion| try pending.append(self.allocator, conversion.operand),
                .division => |division| {
                    if (division.mode == .integer_floor) {
                        try conditions.append(self.allocator, try self.luauExactRange(try self.get(division.left)));
                    }
                    try pending.append(self.allocator, division.left);
                    try pending.append(self.allocator, division.right);
                },
                .remainder => |remainder| {
                    if (remainder.mode == .integer_floor) {
                        var magnitudes = [_]c.Z3_ast{
                            try self.integerMagnitude(try self.get(remainder.left)),
                            try self.integerMagnitude(try self.get(remainder.right)),
                        };
                        const total = c.Z3_mk_add(self.context, magnitudes.len, &magnitudes) orelse return error.Z3AstCreationFailed;
                        const limit = try self.translateNumeral(.{ .kind = .integer }, "9007199254740992");
                        try conditions.append(self.allocator, c.Z3_mk_le(self.context, total, limit) orelse return error.Z3AstCreationFailed);
                    }
                    try pending.append(self.allocator, remainder.left);
                    try pending.append(self.allocator, remainder.right);
                },
            }
        }
        if (conditions.items.len == 0) return expression;
        const condition = c.Z3_mk_and(self.context, @intCast(conditions.items.len), conditions.items.ptr) orelse return error.Z3AstCreationFailed;
        const fallback = if (definitionRoundsLikeLuau(self.program, definition.expression))
            try self.luauIntegerResult(expression, definition.value)
        else
            try self.translateSymbolicValue(sort, definition.value);
        try self.region_conditions.append(self.allocator, condition);
        return c.Z3_mk_ite(self.context, condition, expression, fallback) orelse error.Z3AstCreationFailed;
    }

    // Within 2^53 an exact integer result is the Luau double; beyond it the double keeps the sign and is at least 2^53 in magnitude.
    fn luauIntegerResult(self: *Translator, exact: c.Z3_ast, value_id: ir.ValueId) !c.Z3_ast {
        const integer_sort: ir.SolverSort = .{ .kind = .integer };
        const in_range = try self.luauExactRange(exact);
        var name_buffer: [48]u8 = undefined;
        const name = try std.fmt.bufPrintZ(&name_buffer, "rounded_value_{d}", .{value_id.index()});
        const symbol = c.Z3_mk_string_symbol(self.context, name.ptr) orelse return error.Z3SymbolCreationFailed;
        const rounded = c.Z3_mk_const(self.context, symbol, try self.translateSort(integer_sort)) orelse return error.Z3AstCreationFailed;
        const magnitude = try self.integerMagnitude(rounded);
        var above_arguments = [_]c.Z3_ast{ try self.translateNumeral(integer_sort, "9007199254740992"), magnitude };
        const above = c.Z3_mk_add(self.context, above_arguments.len, &above_arguments) orelse return error.Z3AstCreationFailed;
        var below_arguments = [_]c.Z3_ast{ try self.translateNumeral(integer_sort, "-9007199254740992"), magnitude };
        const below = c.Z3_mk_sub(self.context, below_arguments.len, &below_arguments) orelse return error.Z3AstCreationFailed;
        const exact_is_positive = c.Z3_mk_gt(self.context, exact, try self.translateNumeral(integer_sort, "0")) orelse return error.Z3AstCreationFailed;
        const rounded_result = c.Z3_mk_ite(self.context, exact_is_positive, above, below) orelse return error.Z3AstCreationFailed;
        try self.region_conditions.append(self.allocator, in_range);
        return c.Z3_mk_ite(self.context, in_range, exact, rounded_result) orelse error.Z3AstCreationFailed;
    }

    // An exact integer is also a Luau double when it lies between -2^53 and 2^53 inclusive.
    fn luauExactRange(self: *const Translator, exact: c.Z3_ast) !c.Z3_ast {
        const integer_sort: ir.SolverSort = .{ .kind = .integer };
        const above_lower = c.Z3_mk_le(self.context, try self.translateNumeral(integer_sort, "-9007199254740992"), exact) orelse return error.Z3AstCreationFailed;
        const below_upper = c.Z3_mk_le(self.context, exact, try self.translateNumeral(integer_sort, "9007199254740992")) orelse return error.Z3AstCreationFailed;
        var bounds = [_]c.Z3_ast{ above_lower, below_upper };
        return c.Z3_mk_and(self.context, bounds.len, &bounds) orelse error.Z3AstCreationFailed;
    }

    // The magnitude of an integer term: its negation when it is below zero, else the term itself.
    fn integerMagnitude(self: *const Translator, value: c.Z3_ast) !c.Z3_ast {
        const is_negative = c.Z3_mk_lt(self.context, value, try self.translateNumeral(.{ .kind = .integer }, "0")) orelse return error.Z3AstCreationFailed;
        const negated = c.Z3_mk_unary_minus(self.context, value) orelse return error.Z3AstCreationFailed;
        return c.Z3_mk_ite(self.context, is_negative, negated, value) orelse error.Z3AstCreationFailed;
    }

    fn translateNonzero(self: *const Translator, operand: ir.SolverTermId) !c.Z3_ast {
        if (operand.index() >= self.program.solver_terms.len) return error.InvalidSolverTermReference;
        const zero = try self.translateNumeral(self.program.solver_terms[operand.index()].sort, "0");
        const equal = c.Z3_mk_eq(self.context, try self.get(operand), zero) orelse return error.Z3AstCreationFailed;
        return c.Z3_mk_not(self.context, equal) orelse error.Z3AstCreationFailed;
    }

    fn translateDynamicTruthiness(self: *Translator, operand: ir.SolverTermId) !c.Z3_ast {
        const value = try self.get(operand);
        const is_nil = c.Z3_mk_eq(self.context, value, try self.dynamicNil()) orelse return error.Z3AstCreationFailed;
        const is_false = c.Z3_mk_eq(self.context, value, try self.dynamicBoolean(false)) orelse return error.Z3AstCreationFailed;
        var falsy_cases = [_]c.Z3_ast{ is_nil, is_false };
        const falsy = c.Z3_mk_or(self.context, falsy_cases.len, &falsy_cases) orelse return error.Z3AstCreationFailed;
        return c.Z3_mk_not(self.context, falsy) orelse error.Z3AstCreationFailed;
    }

    fn translateDynamicNumberIsNaN(self: *const Translator, operand: ir.SolverTermId) !c.Z3_ast {
        if (solver_equivalence.dynamicTermIsNaN(self.program, operand)) |is_nan| {
            return (if (is_nan) c.Z3_mk_true(self.context) else c.Z3_mk_false(self.context)) orelse error.Z3AstCreationFailed;
        }
        var arguments = [_]c.Z3_ast{try self.get(operand)};
        return c.Z3_mk_app(self.context, self.dynamic_number_is_nan, arguments.len, &arguments) orelse error.Z3AstCreationFailed;
    }

    fn translateDivision(self: *const Translator, division: ir.SolverDivision) !c.Z3_ast {
        const left = try self.get(division.left);
        const right = try self.get(division.right);
        return switch (division.mode) {
            .integer_euclidean => self.translateIntegerEuclideanDivision(left, right),
            .integer_floor => self.translateIntegerFloorDivision(left, right),
            .real => c.Z3_mk_div(self.context, left, right) orelse error.Z3AstCreationFailed,
            .bit_vector_unsigned => c.Z3_mk_bvudiv(self.context, left, right) orelse error.Z3AstCreationFailed,
            .bit_vector_signed => c.Z3_mk_bvsdiv(self.context, left, right) orelse error.Z3AstCreationFailed,
        };
    }

    fn translateIntegerEuclideanDivision(self: *const Translator, left: c.Z3_ast, right: c.Z3_ast) !c.Z3_ast {
        const integer_sort: ir.SolverSort = .{ .kind = .integer };
        const zero = try self.translateNumeral(integer_sort, "0");
        const right_is_negative = c.Z3_mk_lt(self.context, right, zero) orelse return error.Z3AstCreationFailed;
        const positive_divisor_quotient = c.Z3_mk_div(self.context, left, right) orelse return error.Z3AstCreationFailed;
        const negated_right = c.Z3_mk_unary_minus(self.context, right) orelse return error.Z3AstCreationFailed;
        const negative_divisor_magnitude = c.Z3_mk_div(self.context, left, negated_right) orelse return error.Z3AstCreationFailed;
        const negative_divisor_quotient = c.Z3_mk_unary_minus(self.context, negative_divisor_magnitude) orelse return error.Z3AstCreationFailed;
        return c.Z3_mk_ite(self.context, right_is_negative, negative_divisor_quotient, positive_divisor_quotient) orelse error.Z3AstCreationFailed;
    }

    fn translateIntegerFloorDivision(self: *const Translator, left: c.Z3_ast, right: c.Z3_ast) !c.Z3_ast {
        const integer_sort: ir.SolverSort = .{ .kind = .integer };
        const zero = try self.translateNumeral(integer_sort, "0");
        const right_is_negative = c.Z3_mk_lt(self.context, right, zero) orelse return error.Z3AstCreationFailed;
        const positive_divisor_quotient = c.Z3_mk_div(self.context, left, right) orelse return error.Z3AstCreationFailed;
        const negated_left = c.Z3_mk_unary_minus(self.context, left) orelse return error.Z3AstCreationFailed;
        const negated_right = c.Z3_mk_unary_minus(self.context, right) orelse return error.Z3AstCreationFailed;
        const negative_divisor_quotient = c.Z3_mk_div(self.context, negated_left, negated_right) orelse return error.Z3AstCreationFailed;
        return c.Z3_mk_ite(self.context, right_is_negative, negative_divisor_quotient, positive_divisor_quotient) orelse error.Z3AstCreationFailed;
    }

    fn translateRemainder(self: *const Translator, remainder: ir.SolverRemainder) !c.Z3_ast {
        const left = try self.get(remainder.left);
        const right = try self.get(remainder.right);
        return switch (remainder.mode) {
            .integer_euclidean => self.translateIntegerEuclideanRemainder(left, right),
            .integer_floor => self.translateIntegerFloorRemainder(left, right),
            .bit_vector_unsigned => c.Z3_mk_bvurem(self.context, left, right) orelse error.Z3AstCreationFailed,
            .bit_vector_signed_dividend => c.Z3_mk_bvsrem(self.context, left, right) orelse error.Z3AstCreationFailed,
            .bit_vector_signed_divisor => c.Z3_mk_bvsmod(self.context, left, right) orelse error.Z3AstCreationFailed,
        };
    }

    fn translateIntegerEuclideanRemainder(self: *const Translator, left: c.Z3_ast, right: c.Z3_ast) !c.Z3_ast {
        const integer_sort: ir.SolverSort = .{ .kind = .integer };
        const zero = try self.translateNumeral(integer_sort, "0");
        const right_is_negative = c.Z3_mk_lt(self.context, right, zero) orelse return error.Z3AstCreationFailed;
        const positive_divisor_remainder = c.Z3_mk_mod(self.context, left, right) orelse return error.Z3AstCreationFailed;
        const negated_right = c.Z3_mk_unary_minus(self.context, right) orelse return error.Z3AstCreationFailed;
        const negative_divisor_remainder = c.Z3_mk_mod(self.context, left, negated_right) orelse return error.Z3AstCreationFailed;
        return c.Z3_mk_ite(self.context, right_is_negative, negative_divisor_remainder, positive_divisor_remainder) orelse error.Z3AstCreationFailed;
    }

    fn translateIntegerFloorRemainder(self: *const Translator, left: c.Z3_ast, right: c.Z3_ast) !c.Z3_ast {
        const quotient = try self.translateIntegerFloorDivision(left, right);
        var product_arguments = [_]c.Z3_ast{ quotient, right };
        const product = c.Z3_mk_mul(self.context, product_arguments.len, &product_arguments) orelse return error.Z3AstCreationFailed;
        var remainder_arguments = [_]c.Z3_ast{ left, product };
        return c.Z3_mk_sub(self.context, remainder_arguments.len, &remainder_arguments) orelse error.Z3AstCreationFailed;
    }

    fn translateNumeral(self: *const Translator, sort: ir.SolverSort, decimal: []const u8) !c.Z3_ast {
        const terminated = try self.allocator.dupeZ(u8, decimal);
        defer self.allocator.free(terminated);
        return c.Z3_mk_numeral(self.context, terminated.ptr, try self.translateSort(sort)) orelse error.Z3AstCreationFailed;
    }

    fn translateRational(self: *const Translator, rational: ir.SolverRational) !c.Z3_ast {
        const text = try std.fmt.allocPrintSentinel(self.allocator, "{s}/{s}", .{ rational.numerator, rational.denominator }, 0);
        defer self.allocator.free(text);
        return c.Z3_mk_numeral(self.context, text.ptr, c.Z3_mk_real_sort(self.context) orelse return error.Z3SortCreationFailed) orelse error.Z3AstCreationFailed;
    }

    fn translateValue(self: *Translator, sort: ir.SolverSort, value_id: ir.ValueId) !c.Z3_ast {
        return self.translateValueDepth(sort, value_id, 0);
    }

    fn translateValueDepth(self: *Translator, sort: ir.SolverSort, value_id: ir.ValueId, depth: usize) anyerror!c.Z3_ast {
        if (value_id.index() >= self.program.values.len) return error.InvalidValueReference;
        if (depth > self.program.values.len + self.program.instructions.len) return error.InvalidNormalizedValueCycle;
        if (sort.kind == .dynamic_value) return self.translateDynamicValue(value_id, depth);
        if (exactLiteral(self.program, value_id, depth)) |literal| switch (literal) {
            .boolean => |value| if (sort.kind == .boolean) {
                return (if (value) c.Z3_mk_true(self.context) else c.Z3_mk_false(self.context)) orelse error.Z3AstCreationFailed;
            },
            // An integer literal beyond 2^53 stays opaque to the solver.
            .integer => |decimal| if ((sort.kind == .integer or sort.kind == .bit_vector) and exactLuauDecimal(decimal)) {
                if (sort.kind == .integer) return self.translateNumeral(sort, decimal);
                const integer = try self.translateNumeral(.{ .kind = .integer }, decimal);
                return c.Z3_mk_int2bv(self.context, sort.bit_width, integer) orelse error.Z3AstCreationFailed;
            },
            .nil_value, .number, .special_number, .string => {},
        };
        switch (fact_solver.evaluateValue(self.program, value_id)) {
            .boolean => |value| if (sort.kind == .boolean) {
                return (if (value) c.Z3_mk_true(self.context) else c.Z3_mk_false(self.context)) orelse error.Z3AstCreationFailed;
            },
            // An evaluated integer beyond 2^53 stays opaque to the solver.
            .integer => |value| if ((sort.kind == .integer or sort.kind == .bit_vector) and value >= -(1 << 53) and value <= (1 << 53)) {
                const decimal = try std.fmt.allocPrint(self.allocator, "{d}", .{value});
                defer self.allocator.free(decimal);
                if (sort.kind == .integer) return self.translateNumeral(sort, decimal);
                const integer_sort: ir.SolverSort = .{ .kind = .integer };
                const integer = try self.translateNumeral(integer_sort, decimal);
                return c.Z3_mk_int2bv(self.context, sort.bit_width, integer) orelse error.Z3AstCreationFailed;
            },
            .real => |value| if (sort.kind == .real) return self.translateRational(value),
            .bit_vector, .unknown => {},
        }
        if (try self.translateNormalizedValue(sort, value_id, depth)) |translated| return translated;
        return self.translateSymbolicValue(sort, value_id);
    }

    fn translateDynamicValue(self: *Translator, value_id: ir.ValueId, depth: usize) !c.Z3_ast {
        if (self.program.values[value_id.index()].type.kind == .nil_value) return self.dynamicNil();
        if (fact_solver.normalizedValueSource(self.program, value_id)) |source| switch (source) {
            .constant => |constant| switch (constant.literal) {
                .nil_value => return self.dynamicNil(),
                .boolean => |value| return self.dynamicBoolean(value),
                .integer => |value| return self.dynamicExactNumber(.{ .integer = value }),
                .number => |value| return self.dynamicExactNumber(.{ .number = value }),
                .special_number => |value| return self.dynamicExactNumber(.{ .number = value.asF64() }),
                .string => |value| return self.dynamicExactString(value),
            },
            .copy => |copy| return self.translateValueDepth(.{ .kind = .dynamic_value }, copy.source, depth + 1),
            .unary, .binary => {},
        };
        if (solver_equivalence.dynamicValueDescriptor(self.program, value_id)) |descriptor| {
            if (descriptor.exact_boolean) |value| return self.dynamicBoolean(value);
            if (solver_equivalence.dynamicDescriptorExactString(descriptor) != null) return self.dynamicExactStringDescriptor(descriptor);
            if (descriptor.exact_number) |number| return self.dynamicExactNumber(number);
            if (descriptor.function_reference) |target| return self.dynamicFunctionReference(target);
        }
        return self.translateSymbolicValue(.{ .kind = .dynamic_value }, value_id);
    }

    fn dynamicNil(self: *Translator) !c.Z3_ast {
        for (self.dynamic_atoms.items) |atom| {
            const descriptor = atom.descriptor orelse continue;
            if (descriptor.category == .nil_value) return atom.ast;
        }
        const symbol = c.Z3_mk_string_symbol(self.context, "dynamic_nil_value") orelse return error.Z3SymbolCreationFailed;
        const ast = c.Z3_mk_const(self.context, symbol, self.dynamic_sort) orelse return error.Z3AstCreationFailed;
        try self.dynamic_atoms.append(self.allocator, .{
            .ast = ast,
            .descriptor = .{ .category = .nil_value },
        });
        return ast;
    }

    fn dynamicBoolean(self: *Translator, value: bool) !c.Z3_ast {
        for (self.dynamic_atoms.items) |atom| {
            const descriptor = atom.descriptor orelse continue;
            if (descriptor.category == .boolean and descriptor.exact_boolean == value) return atom.ast;
        }
        const name = if (value) "dynamic_boolean_true" else "dynamic_boolean_false";
        const symbol = c.Z3_mk_string_symbol(self.context, name) orelse return error.Z3SymbolCreationFailed;
        const ast = c.Z3_mk_const(self.context, symbol, self.dynamic_sort) orelse return error.Z3AstCreationFailed;
        try self.dynamic_atoms.append(self.allocator, .{
            .ast = ast,
            .descriptor = .{ .category = .boolean, .exact_boolean = value },
        });
        return ast;
    }

    fn ensureDynamicBooleans(self: *Translator) !void {
        _ = try self.dynamicBoolean(false);
        _ = try self.dynamicBoolean(true);
    }

    fn dynamicExactNumber(self: *Translator, value: solver_equivalence.DynamicNumber) !c.Z3_ast {
        const descriptor: solver_equivalence.DynamicDescriptor = .{
            .category = .number,
            .exact_number = value,
        };
        var literal_index: usize = 0;
        for (self.dynamic_atoms.items) |atom| {
            const existing = atom.descriptor orelse continue;
            if (existing.exact_number == null) continue;
            if (solver_equivalence.dynamicDescriptorsEquivalent(existing, descriptor)) return atom.ast;
            literal_index += 1;
        }
        var name_buffer: [64]u8 = undefined;
        const name = try std.fmt.bufPrintZ(&name_buffer, "dynamic_number_literal_{d}", .{literal_index});
        const symbol = c.Z3_mk_string_symbol(self.context, name.ptr) orelse return error.Z3SymbolCreationFailed;
        const ast = c.Z3_mk_const(self.context, symbol, self.dynamic_sort) orelse return error.Z3AstCreationFailed;
        try self.dynamic_atoms.append(self.allocator, .{ .ast = ast, .descriptor = descriptor });
        return ast;
    }

    fn dynamicExactString(self: *Translator, value: []const u8) !c.Z3_ast {
        return self.dynamicExactStringDescriptor(.{ .category = .string, .exact_string = value });
    }

    fn dynamicExactStringDescriptor(self: *Translator, descriptor: solver_equivalence.DynamicDescriptor) !c.Z3_ast {
        if (solver_equivalence.dynamicDescriptorExactString(descriptor) == null) return error.InvalidDynamicStringDescriptor;
        var literal_index: usize = 0;
        for (self.dynamic_atoms.items) |atom| {
            const existing = atom.descriptor orelse continue;
            if (solver_equivalence.dynamicDescriptorExactString(existing) == null) continue;
            if (solver_equivalence.dynamicDescriptorRelation(existing, descriptor) == .equivalent) return atom.ast;
            literal_index += 1;
        }
        var name_buffer: [64]u8 = undefined;
        const name = try std.fmt.bufPrintZ(&name_buffer, "dynamic_string_literal_{d}", .{literal_index});
        const symbol = c.Z3_mk_string_symbol(self.context, name.ptr) orelse return error.Z3SymbolCreationFailed;
        const ast = c.Z3_mk_const(self.context, symbol, self.dynamic_sort) orelse return error.Z3AstCreationFailed;
        try self.dynamic_atoms.append(self.allocator, .{
            .ast = ast,
            .descriptor = descriptor,
        });
        return ast;
    }

    fn dynamicFunctionReference(self: *Translator, target: ir.FunctionId) !c.Z3_ast {
        const descriptor: solver_equivalence.DynamicDescriptor = .{
            .category = .function_value,
            .function_reference = target,
        };
        for (self.dynamic_atoms.items) |atom| {
            const existing = atom.descriptor orelse continue;
            if (solver_equivalence.dynamicDescriptorsEquivalent(existing, descriptor)) return atom.ast;
        }
        var name_buffer: [64]u8 = undefined;
        const name = try std.fmt.bufPrintZ(&name_buffer, "dynamic_function_reference_{d}", .{target.index()});
        const symbol = c.Z3_mk_string_symbol(self.context, name.ptr) orelse return error.Z3SymbolCreationFailed;
        const ast = c.Z3_mk_const(self.context, symbol, self.dynamic_sort) orelse return error.Z3AstCreationFailed;
        try self.dynamic_atoms.append(self.allocator, .{ .ast = ast, .descriptor = descriptor });
        return ast;
    }

    fn translateNormalizedValue(self: *Translator, sort: ir.SolverSort, value_id: ir.ValueId, depth: usize) !?c.Z3_ast {
        const source = fact_solver.normalizedValueSource(self.program, value_id) orelse return null;
        return switch (source) {
            .constant => null,
            .copy => |copy| try self.translateValueDepth(sort, copy.source, depth + 1),
            .unary => |unary| try self.translateNormalizedUnary(sort, unary, depth + 1),
            .binary => |binary| try self.translateNormalizedBinary(sort, binary, value_id, depth + 1),
        };
    }

    fn translateNormalizedUnary(
        self: *Translator,
        sort: ir.SolverSort,
        unary: @FieldType(fact_solver.NormalizedValueSource, "unary"),
        depth: usize,
    ) !?c.Z3_ast {
        return switch (unary.operator) {
            .logical_not => if (sort.kind == .boolean and self.valueHasScalarSort(unary.operand, .boolean))
                c.Z3_mk_not(self.context, try self.translateValueDepth(.{ .kind = .boolean }, unary.operand, depth)) orelse error.Z3AstCreationFailed
            else
                null,
            .negate => if (sort.kind == .integer and self.valueHasScalarSort(unary.operand, .integer))
                c.Z3_mk_unary_minus(self.context, try self.translateValueDepth(.{ .kind = .integer }, unary.operand, depth)) orelse error.Z3AstCreationFailed
            else
                null,
            .length, .bit_not => null,
        };
    }

    fn translateNormalizedBinary(
        self: *Translator,
        result_sort: ir.SolverSort,
        binary: @FieldType(fact_solver.NormalizedValueSource, "binary"),
        value_id: ir.ValueId,
        depth: usize,
    ) !?c.Z3_ast {
        const operator = normalized_value.solverBinaryOperator(binary.operator) orelse return null;
        const operand_sort = self.normalizedOperandSort(result_sort, binary) orelse return null;
        const left = try self.translateValueDepth(operand_sort, binary.left, depth);
        const right = try self.translateValueDepth(operand_sort, binary.right, depth);
        const exact = try self.translateBinaryAsts(operator, operand_sort, left, right);
        // Integer add, subtract and multiply beyond 2^53 take the value Luau doubles round them to.
        return switch (operator) {
            .add, .subtract, .multiply => if (operand_sort.kind == .integer) try self.luauIntegerResult(exact, value_id) else exact,
            else => exact,
        };
    }

    fn normalizedOperandSort(
        self: *const Translator,
        result_sort: ir.SolverSort,
        binary: @FieldType(fact_solver.NormalizedValueSource, "binary"),
    ) ?ir.SolverSort {
        const boolean_sort: ir.SolverSort = .{ .kind = .boolean };
        const integer_sort: ir.SolverSort = .{ .kind = .integer };
        return switch (binary.operator) {
            .logical_and, .logical_or => if (result_sort.kind == .boolean and
                self.valueHasScalarSort(binary.left, .boolean) and
                self.valueHasScalarSort(binary.right, .boolean))
                boolean_sort
            else
                null,
            .add, .subtract, .multiply => if (result_sort.kind == .integer and
                self.valueHasScalarSort(binary.left, .integer) and
                self.valueHasScalarSort(binary.right, .integer))
                integer_sort
            else
                null,
            .equal, .not_equal => blk: {
                if (result_sort.kind != .boolean) break :blk null;
                const left = self.scalarSort(binary.left) orelse break :blk null;
                const right = self.scalarSort(binary.right) orelse break :blk null;
                break :blk if (sameSort(left, right)) left else null;
            },
            .less, .less_equal, .greater, .greater_equal => if (result_sort.kind == .boolean and
                self.valueHasScalarSort(binary.left, .integer) and
                self.valueHasScalarSort(binary.right, .integer))
                integer_sort
            else
                null,
            .divide, .floor_divide, .modulo, .power, .concat, .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => null,
        };
    }

    fn scalarSort(self: *const Translator, value_id: ir.ValueId) ?ir.SolverSort {
        if (value_id.index() >= self.program.values.len) return null;
        return switch (self.program.values[value_id.index()].type.kind) {
            .boolean => .{ .kind = .boolean },
            .integer => .{ .kind = .integer },
            else => null,
        };
    }

    fn valueHasScalarSort(self: *const Translator, value_id: ir.ValueId, kind: ir.SolverSortKind) bool {
        const sort = self.scalarSort(value_id) orelse return false;
        return sort.kind == kind;
    }

    fn translateSymbolicValue(self: *Translator, sort: ir.SolverSort, value_id: ir.ValueId) !c.Z3_ast {
        var name_buffer: [48]u8 = undefined;
        const name = try std.fmt.bufPrintZ(&name_buffer, "value_{d}", .{value_id.index()});
        const symbol = c.Z3_mk_string_symbol(self.context, name.ptr) orelse return error.Z3SymbolCreationFailed;
        const ast = c.Z3_mk_const(self.context, symbol, try self.translateSort(sort)) orelse return error.Z3AstCreationFailed;
        if (sort.kind == .dynamic_value) {
            const descriptor = solver_equivalence.dynamicValueDescriptor(self.program, value_id);
            if (descriptor != null and descriptor.?.category == .boolean and descriptor.?.exact_boolean == null) {
                try self.ensureDynamicBooleans();
            }
            try self.registerDynamicAtom(ast, descriptor);
        }
        return ast;
    }

    fn registerDynamicAtom(self: *Translator, ast: c.Z3_ast, descriptor: ?solver_equivalence.DynamicDescriptor) !void {
        for (self.dynamic_atoms.items) |atom| if (c.Z3_is_eq_ast(self.context, atom.ast, ast)) return;
        try self.dynamic_atoms.append(self.allocator, .{ .ast = ast, .descriptor = descriptor });
    }

    fn translateSemanticAtom(self: *const Translator, sort: ir.SolverSort, atom: ir.SemanticAtom) !c.Z3_ast {
        if (sort.kind != .boolean) return error.SemanticAtomRequiresBooleanSort;
        var name_buffer: [96]u8 = undefined;
        const name = switch (atom) {
            .instruction_effects => |instruction_id| blk: {
                if (instruction_id.index() >= self.program.instructions.len) return error.InvalidInstructionReference;
                break :blk try std.fmt.bufPrintZ(&name_buffer, "semantic_instruction_effects_{d}", .{instruction_id.index()});
            },
            .no_metamethod_dispatch => |instruction_id| blk: {
                if (instruction_id.index() >= self.program.instructions.len) return error.InvalidInstructionReference;
                break :blk try std.fmt.bufPrintZ(&name_buffer, "semantic_no_metamethod_dispatch_{d}", .{instruction_id.index()});
            },
            .primitive_operator_domain => |instruction_id| blk: {
                if (instruction_id.index() >= self.program.instructions.len) return error.InvalidInstructionReference;
                break :blk try std.fmt.bufPrintZ(&name_buffer, "semantic_primitive_operator_domain_{d}", .{instruction_id.index()});
            },
        };
        const symbol = c.Z3_mk_string_symbol(self.context, name.ptr) orelse return error.Z3SymbolCreationFailed;
        return c.Z3_mk_const(self.context, symbol, try self.translateSort(sort)) orelse error.Z3AstCreationFailed;
    }

    fn translateSort(self: *const Translator, sort: ir.SolverSort) !c.Z3_sort {
        return switch (sort.kind) {
            .boolean => c.Z3_mk_bool_sort(self.context) orelse error.Z3SortCreationFailed,
            .integer => c.Z3_mk_int_sort(self.context) orelse error.Z3SortCreationFailed,
            .real => c.Z3_mk_real_sort(self.context) orelse error.Z3SortCreationFailed,
            .bit_vector => if (sort.bit_width == 0)
                error.InvalidBitVectorWidth
            else
                c.Z3_mk_bv_sort(self.context, sort.bit_width) orelse error.Z3SortCreationFailed,
            .dynamic_value => self.dynamic_sort,
        };
    }

    fn translateBinary(self: *const Translator, result_sort: ir.SolverSort, binary: ir.SolverBinary) !c.Z3_ast {
        _ = result_sort;
        const left = try self.get(binary.left);
        const right = try self.get(binary.right);
        const operand_sort = self.program.solver_terms[binary.left.index()].sort;
        return self.translateBinaryAsts(binary.operator, operand_sort, left, right);
    }

    fn translateBinaryAsts(
        self: *const Translator,
        operator: ir.SolverBinaryOperator,
        operand_sort: ir.SolverSort,
        left: c.Z3_ast,
        right: c.Z3_ast,
    ) !c.Z3_ast {
        var arguments = [_]c.Z3_ast{ left, right };

        return switch (operator) {
            .equal => c.Z3_mk_eq(self.context, left, right) orelse error.Z3AstCreationFailed,
            .not_equal => blk: {
                const equal = c.Z3_mk_eq(self.context, left, right) orelse return error.Z3AstCreationFailed;
                break :blk c.Z3_mk_not(self.context, equal) orelse error.Z3AstCreationFailed;
            },
            .less => try self.translateComparison(.less, operand_sort, left, right),
            .less_equal => try self.translateComparison(.less_equal, operand_sort, left, right),
            .greater => try self.translateComparison(.greater, operand_sort, left, right),
            .greater_equal => try self.translateComparison(.greater_equal, operand_sort, left, right),
            .logical_and => c.Z3_mk_and(self.context, arguments.len, &arguments) orelse error.Z3AstCreationFailed,
            .logical_or => c.Z3_mk_or(self.context, arguments.len, &arguments) orelse error.Z3AstCreationFailed,
            .add => if (operand_sort.kind == .bit_vector)
                c.Z3_mk_bvadd(self.context, left, right) orelse error.Z3AstCreationFailed
            else
                c.Z3_mk_add(self.context, arguments.len, &arguments) orelse error.Z3AstCreationFailed,
            .subtract => if (operand_sort.kind == .bit_vector)
                c.Z3_mk_bvsub(self.context, left, right) orelse error.Z3AstCreationFailed
            else
                c.Z3_mk_sub(self.context, arguments.len, &arguments) orelse error.Z3AstCreationFailed,
            .multiply => if (operand_sort.kind == .bit_vector)
                c.Z3_mk_bvmul(self.context, left, right) orelse error.Z3AstCreationFailed
            else
                c.Z3_mk_mul(self.context, arguments.len, &arguments) orelse error.Z3AstCreationFailed,
            .bit_and => c.Z3_mk_bvand(self.context, left, right) orelse error.Z3AstCreationFailed,
            .bit_or => c.Z3_mk_bvor(self.context, left, right) orelse error.Z3AstCreationFailed,
            .bit_xor => c.Z3_mk_bvxor(self.context, left, right) orelse error.Z3AstCreationFailed,
            .shift_left => c.Z3_mk_bvshl(self.context, left, right) orelse error.Z3AstCreationFailed,
            .shift_right => (if (operand_sort.signed) c.Z3_mk_bvashr(self.context, left, right) else c.Z3_mk_bvlshr(self.context, left, right)) orelse error.Z3AstCreationFailed,
        };
    }

    const Comparison = enum { less, less_equal, greater, greater_equal };

    fn translateComparison(self: *const Translator, comparison: Comparison, sort: ir.SolverSort, left: c.Z3_ast, right: c.Z3_ast) !c.Z3_ast {
        if (sort.kind == .bit_vector) {
            return switch (comparison) {
                .less => (if (sort.signed) c.Z3_mk_bvslt(self.context, left, right) else c.Z3_mk_bvult(self.context, left, right)) orelse error.Z3AstCreationFailed,
                .less_equal => (if (sort.signed) c.Z3_mk_bvsle(self.context, left, right) else c.Z3_mk_bvule(self.context, left, right)) orelse error.Z3AstCreationFailed,
                .greater => (if (sort.signed) c.Z3_mk_bvsgt(self.context, left, right) else c.Z3_mk_bvugt(self.context, left, right)) orelse error.Z3AstCreationFailed,
                .greater_equal => (if (sort.signed) c.Z3_mk_bvsge(self.context, left, right) else c.Z3_mk_bvuge(self.context, left, right)) orelse error.Z3AstCreationFailed,
            };
        }
        return switch (comparison) {
            .less => c.Z3_mk_lt(self.context, left, right) orelse error.Z3AstCreationFailed,
            .less_equal => c.Z3_mk_le(self.context, left, right) orelse error.Z3AstCreationFailed,
            .greater => c.Z3_mk_gt(self.context, left, right) orelse error.Z3AstCreationFailed,
            .greater_equal => c.Z3_mk_ge(self.context, left, right) orelse error.Z3AstCreationFailed,
        };
    }
};

fn sameSort(left: ir.SolverSort, right: ir.SolverSort) bool {
    return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed;
}

fn exactLiteral(program: *const ir.Program, value_id: ir.ValueId, depth: usize) ?ir.Literal {
    if (depth > program.values.len) return null;
    const source = fact_solver.normalizedValueSource(program, value_id) orelse return null;
    return switch (source) {
        .constant => |constant| constant.literal,
        .copy => |copy| exactLiteral(program, copy.source, depth + 1),
        .unary, .binary => null,
    };
}

// An integer literal is a Luau double exactly when it lies within 2^53 in magnitude.
fn exactLuauDecimal(decimal: []const u8) bool {
    const value = numerals.parseCanonicalSigned(i64, decimal) orelse return false;
    return value >= -(1 << 53) and value <= (1 << 53);
}

// One integer add, subtract or multiply over values, definitions or exact literals rounds like one Luau operation.
fn definitionRoundsLikeLuau(program: *const ir.Program, expression: ir.SolverTermId) bool {
    if (expression.index() >= program.solver_terms.len) return false;
    const binary = switch (program.solver_terms[expression.index()].operation) {
        .binary => |operation| operation,
        else => return false,
    };
    if (binary.operator != .add and binary.operator != .subtract and binary.operator != .multiply) return false;
    for ([_]ir.SolverTermId{ binary.left, binary.right }) |operand| {
        if (operand.index() >= program.solver_terms.len) return false;
        switch (program.solver_terms[operand.index()].operation) {
            .value, .value_definition => {},
            .integer_literal => |decimal| if (!exactLuauDecimal(decimal)) return false,
            else => return false,
        }
    }
    return program.solver_terms[binary.left.index()].sort.kind == .integer;
}
