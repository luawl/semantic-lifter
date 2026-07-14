const std = @import("std");

fn EntityId(comptime label: []const u8) type {
    return enum(u32) {
        _,

        pub fn fromIndex(index_value: usize) @This() {
            return @enumFromInt(@as(u32, @intCast(index_value)));
        }

        pub fn index(self: @This()) usize {
            return @intFromEnum(self);
        }

        pub fn entityLabel(_: @This()) []const u8 {
            return label;
        }
    };
}

pub const FunctionId = EntityId("function");
pub const BlockId = EntityId("block");
pub const InstructionId = EntityId("instruction");
pub const ValueId = EntityId("value");
pub const ValuePackId = EntityId("value-pack");
pub const PlaceId = EntityId("place");
pub const CaptureId = EntityId("capture");
pub const ExternalBindingId = EntityId("external-binding");
pub const EvidenceId = EntityId("evidence");
pub const SolverTermId = EntityId("solver-term");
pub const ConstraintId = EntityId("constraint");
pub const QueryId = EntityId("query");
pub const SolverModelId = EntityId("solver-model");
pub const UnsatCoreId = EntityId("unsat-core");
pub const CertificateId = EntityId("certificate");
pub const EdgeRewriteId = EntityId("edge-rewrite");
pub const NodeSplitGroupId = EntityId("node-split-group");
pub const ClaimId = EntityId("claim");
pub const ObligationId = EntityId("obligation");

pub const SchemaVersion = enum {
    lifter_ir_v1,
};

pub const SourceSemantics = enum {
    luau,
};

pub const TypeKind = enum {
    dynamic,
    nil_value,
    boolean,
    integer,
    number,
    string,
    table,
    function,
    thread,
    userdata,
    tuple,
};

pub const ValueType = struct {
    /// Numeric widths and signedness are proven value-domain refinements under
    /// `source_semantics`; they do not silently change operation semantics to
    /// machine wrapping or narrower floating-point rounding. Such behavior
    /// must be explicit in the operation or solver view that requires it.
    kind: TypeKind = .dynamic,
    bit_width: u16 = 0,
    signed: bool = false,

    pub const dynamic: ValueType = .{};
    pub const boolean: ValueType = .{ .kind = .boolean };
    pub const integer: ValueType = .{ .kind = .integer, .bit_width = 64, .signed = true };
    pub const number: ValueType = .{ .kind = .number, .bit_width = 64 };
    pub const string: ValueType = .{ .kind = .string };
    pub const function: ValueType = .{ .kind = .function };

    pub fn knownLuauTruthiness(self: ValueType) ?bool {
        return switch (self.kind) {
            .nil_value => false,
            .integer, .number, .string, .table, .function, .thread, .userdata => true,
            .dynamic, .boolean, .tuple => null,
        };
    }
};

pub const SpecialNumber = enum {
    nan,
    positive_infinity,
    negative_infinity,

    pub fn asF64(self: SpecialNumber) f64 {
        return switch (self) {
            .nan => std.math.nan(f64),
            .positive_infinity => std.math.inf(f64),
            .negative_infinity => -std.math.inf(f64),
        };
    }
};

const SerializedLiteral = union(enum) {
    nil_value: void,
    boolean: bool,
    integer: []const u8,
    number: f64,
    special_number: SpecialNumber,
    string: []const u8,
    string_bytes: []const u8,
};

const SerializedStringBytes = union(enum) {
    string_bytes: []const u8,
};

fn isLowerHex(byte: u8) bool {
    return (byte >= '0' and byte <= '9') or (byte >= 'a' and byte <= 'f');
}

fn decodeStringBytes(allocator: std.mem.Allocator, encoded: []const u8) ![]const u8 {
    if (encoded.len % 2 != 0) return error.UnexpectedToken;
    for (encoded) |byte| if (!isLowerHex(byte)) return error.UnexpectedToken;
    const bytes = try allocator.alloc(u8, encoded.len / 2);
    errdefer allocator.free(bytes);
    _ = std.fmt.hexToBytes(bytes, encoded) catch return error.UnexpectedToken;
    if (std.unicode.utf8ValidateSlice(bytes)) return error.UnexpectedToken;
    return bytes;
}

fn writeStringBytes(writer: anytype, bytes: []const u8) !void {
    try writer.beginWriteRaw();
    try writer.writer.writeAll("\"");
    for (bytes) |byte| try writer.writer.print("{x:0>2}", .{byte});
    try writer.writer.writeAll("\"");
    writer.endWriteRaw();
}

pub const Literal = union(enum) {
    nil_value: void,
    boolean: bool,
    integer: []const u8,
    number: f64,
    special_number: SpecialNumber,
    string: []const u8,

    pub fn jsonParse(allocator: std.mem.Allocator, source: anytype, options: std.json.ParseOptions) !Literal {
        const serialized = try std.json.innerParse(SerializedLiteral, allocator, source, options);
        return switch (serialized) {
            .nil_value => .{ .nil_value = {} },
            .boolean => |value| .{ .boolean = value },
            .integer => |value| .{ .integer = value },
            .number => |value| .{ .number = value },
            .special_number => |value| .{ .special_number = value },
            .string => |value| if (std.unicode.utf8ValidateSlice(value))
                .{ .string = value }
            else
                error.UnexpectedToken,
            .string_bytes => |value| .{ .string = try decodeStringBytes(allocator, value) },
        };
    }

    pub fn jsonStringify(self: Literal, writer: anytype) !void {
        try writer.beginObject();
        switch (self) {
            .nil_value => {
                try writer.objectField("nil_value");
                try writer.beginObject();
                try writer.endObject();
            },
            .boolean => |value| {
                try writer.objectField("boolean");
                try writer.write(value);
            },
            .integer => |value| {
                try writer.objectField("integer");
                try writer.write(value);
            },
            .number => |value| {
                try writer.objectField("number");
                try writer.write(value);
            },
            .special_number => |value| {
                try writer.objectField("special_number");
                try writer.write(value);
            },
            .string => |value| if (std.unicode.utf8ValidateSlice(value)) {
                try writer.objectField("string");
                try writer.write(value);
            } else {
                try writer.objectField("string_bytes");
                try writeStringBytes(writer, value);
            },
        }
        try writer.endObject();
    }
};

pub const UnaryOperator = enum {
    logical_not,
    negate,
    length,
    bit_not,
};

pub const BinaryOperator = enum {
    add,
    subtract,
    multiply,
    divide,
    floor_divide,
    modulo,
    power,
    concat,
    equal,
    not_equal,
    less,
    less_equal,
    greater,
    greater_equal,
    logical_and,
    logical_or,
    bit_and,
    bit_or,
    bit_xor,
    shift_left,
    shift_right,
};

pub const EffectPrecision = enum {
    exact,
    conservative,
    unknown,
};

pub const EffectSummary = struct {
    precision: EffectPrecision = .unknown,
    reads_memory: bool = false,
    writes_memory: bool = false,
    may_throw: bool = false,
    may_yield: bool = false,
    invokes_unknown_code: bool = false,

    pub const pure: EffectSummary = .{ .precision = .exact };
    pub const place_read: EffectSummary = .{ .precision = .exact, .reads_memory = true };
    pub const place_write: EffectSummary = .{ .precision = .exact, .writes_memory = true };
    pub const raw_table_read: EffectSummary = .{ .precision = .exact, .reads_memory = true, .may_throw = true };
    pub const raw_table_write: EffectSummary = .{ .precision = .exact, .writes_memory = true, .may_throw = true };
    pub const semantic_table_read: EffectSummary = .{ .precision = .conservative, .reads_memory = true, .writes_memory = true, .may_throw = true, .may_yield = true, .invokes_unknown_code = true };
    pub const semantic_table_write: EffectSummary = .{ .precision = .conservative, .reads_memory = true, .writes_memory = true, .may_throw = true, .may_yield = true, .invokes_unknown_code = true };
    pub const semantic_environment_read: EffectSummary = semantic_table_read;
    pub const semantic_environment_write: EffectSummary = semantic_table_write;
    pub const protected_invocation: EffectSummary = .{ .precision = .conservative, .reads_memory = true, .writes_memory = true, .may_throw = true, .may_yield = true, .invokes_unknown_code = true };
    pub const coroutine_create: EffectSummary = .{ .precision = .exact, .may_throw = true };
    pub const coroutine_resume: EffectSummary = protected_invocation;
    pub const coroutine_yield: EffectSummary = protected_invocation;
    pub const dynamic_call: EffectSummary = protected_invocation;
    pub const namecall: EffectSummary = dynamic_call;
    pub const numeric_for_next: EffectSummary = .{ .precision = .exact, .may_throw = true };
    pub const generic_for_next: EffectSummary = dynamic_call;
    pub const table_constructor: EffectSummary = .{ .precision = .exact, .writes_memory = true, .may_throw = true };
    pub const string_interpolation: EffectSummary = dynamic_call;
};

pub const ResultArity = union(enum) {
    fixed: u16,
    variadic: void,
};

pub const Call = struct {
    callee: ValueId,
    arguments: []const ValueId,
    argument_pack: ?ValuePackId = null,
    result_arity: ResultArity,
};

/// Calls a callee with a fixed prefix followed by one table read for each
/// value in an explicit numeric range. The range is evaluated once, reads are
/// ordered by the numeric iteration, nil results remain argument positions,
/// and an optional counter place is incremented after each successful read.
pub const CallRepeatedTableGet = struct {
    callee: ValueId,
    prefix_arguments: []const ValueId,
    table: ValueId,
    key: ValueId,
    from: ValueId,
    to: ValueId,
    step: ValueId,
    counter: ?PlaceId = null,
    result_arity: ResultArity,
};

/// Native Luau colon dispatch. The receiver and argument values are evaluated
/// before this operation; method lookup and invocation remain one host-visible
/// NAMECALL boundary with implicit self.
pub const Namecall = struct {
    receiver: ValueId,
    method: []const u8,
    arguments: []const ValueId,
    argument_pack: ?ValuePackId = null,
    result_arity: ResultArity,
};

pub const ProtectedCall = struct {
    callee: ValueId,
    error_handler: ?ValueId = null,
    arguments: []const ValueId,
    argument_pack: ?ValuePackId = null,
    result_arity: ResultArity,
};

pub const CoroutineCreate = struct {
    callee: ValueId,
};

pub const CoroutineResume = struct {
    thread: ValueId,
    arguments: []const ValueId,
    argument_pack: ?ValuePackId = null,
    result_arity: ResultArity,
};

pub const CoroutineYield = struct {
    arguments: []const ValueId,
    argument_pack: ?ValuePackId = null,
    result_arity: ResultArity,
};

pub const Unary = struct {
    operator: UnaryOperator,
    operand: ValueId,
    mode: OperatorMode = .semantic,
};

pub const Binary = struct {
    operator: BinaryOperator,
    left: ValueId,
    right: ValueId,
    mode: OperatorMode = .semantic,
    /// Required for shifts and absent for every other binary operator.
    shift_behavior: ?ShiftBehavior = null,
};

pub const ShiftBehavior = enum {
    /// Preserve the pinned Luau `bit32` displacement conversion exactly.
    luau_bit32,
    /// Counts at or above the operand width produce zero.
    zero_saturating,
};

pub const OperatorMode = enum {
    semantic,
    /// Operands already satisfy the fixed primitive domain described by their
    /// value types; no dynamic dispatch or coercion remains.
    primitive,
};

pub const TableAccessMode = enum {
    semantic,
    raw,
};

pub const TableGet = struct {
    table: ValueId,
    key: ValueId,
    mode: TableAccessMode = .semantic,
};

pub const TableSet = struct {
    table: ValueId,
    key: ValueId,
    value: ValueId,
    mode: TableAccessMode = .semantic,
};

/// Writes every result in `pack` to consecutive integer keys beginning at
/// `first_index`. Writes are raw and preserve the pack's runtime count,
/// including nil holes.
pub const TableSetPack = struct {
    table: ValueId,
    first_index: u32,
    pack: ValuePackId,
};

pub const TableConstructorField = union(enum) {
    list: ValueId,
    keyed: struct {
        key: ValueId,
        value: ValueId,
    },
};

/// Ordered Luau table-constructor fields. `tail_pack`, when present, is the
/// final list field and contributes every runtime result, including nil holes.
pub const TableConstructor = struct {
    fields: []const TableConstructorField,
    tail_pack: ?ValuePackId = null,
};

const SerializedStringSegment = struct {
    bytes: []const u8,

    pub fn jsonParse(allocator: std.mem.Allocator, source: anytype, options: std.json.ParseOptions) !SerializedStringSegment {
        return switch (try source.peekNextTokenType()) {
            .string => blk: {
                const value = try std.json.innerParse([]const u8, allocator, source, options);
                if (!std.unicode.utf8ValidateSlice(value)) return error.UnexpectedToken;
                break :blk .{ .bytes = value };
            },
            .object_begin => blk: {
                const value = try std.json.innerParse(SerializedStringBytes, allocator, source, options);
                break :blk .{ .bytes = try decodeStringBytes(allocator, value.string_bytes) };
            },
            else => error.UnexpectedToken,
        };
    }
};

const SerializedStringInterpolation = struct {
    segments: []const SerializedStringSegment,
    values: []const ValueId,
};

pub const StringInterpolation = struct {
    segments: []const []const u8,
    values: []const ValueId,

    pub fn jsonParse(allocator: std.mem.Allocator, source: anytype, options: std.json.ParseOptions) !StringInterpolation {
        const serialized = try std.json.innerParse(SerializedStringInterpolation, allocator, source, options);
        const segments = try allocator.alloc([]const u8, serialized.segments.len);
        for (serialized.segments, segments) |segment, *destination| destination.* = segment.bytes;
        return .{ .segments = segments, .values = serialized.values };
    }

    pub fn jsonStringify(self: StringInterpolation, writer: anytype) !void {
        try writer.beginObject();
        try writer.objectField("segments");
        try writer.beginArray();
        for (self.segments) |segment| {
            if (std.unicode.utf8ValidateSlice(segment)) {
                try writer.write(segment);
            } else {
                try writer.beginObject();
                try writer.objectField("string_bytes");
                try writeStringBytes(writer, segment);
                try writer.endObject();
            }
        }
        try writer.endArray();
        try writer.objectField("values");
        try writer.write(self.values);
        try writer.endObject();
    }
};

pub const EnvironmentTarget = union(enum) {
    ambient: void,
    value: ValueId,
};

pub const EnvironmentGet = struct {
    target: EnvironmentTarget,
    name: []const u8,
    mode: TableAccessMode = .semantic,
};

pub const EnvironmentSet = struct {
    target: EnvironmentTarget,
    name: []const u8,
    value: ValueId,
    mode: TableAccessMode = .semantic,
};

pub const PlaceWrite = struct {
    place: PlaceId,
    value: ValueId,
};

pub const NumericForMode = enum {
    luau_numeric,
    semantic_normalized,
};

/// One direction-sensitive numeric iteration transition. `luau_numeric`
/// models Luau's native numeric-for protocol: the initial transition coerces
/// `control`, `limit`, and `step` to numbers and tests without advancing, while
/// later transitions advance by the normalized step. `semantic_normalized`
/// always performs the explicit dynamic sequence `control + step`, `step <= 0`,
/// then the selected inclusive bound comparison; it does not coerce operands
/// and ignores `initial`. Results are `[has_value, limit, step, control]`.
pub const NumericForNext = struct {
    control: ValueId,
    limit: ValueId,
    step: ValueId,
    initial: ValueId,
    mode: NumericForMode = .luau_numeric,

    pub fn jsonStringify(self: NumericForNext, writer: anytype) !void {
        try writer.beginObject();
        try writer.objectField("control");
        try writer.write(self.control);
        try writer.objectField("limit");
        try writer.write(self.limit);
        try writer.objectField("step");
        try writer.write(self.step);
        try writer.objectField("initial");
        try writer.write(self.initial);
        if (self.mode != .luau_numeric) {
            try writer.objectField("mode");
            try writer.write(self.mode);
        }
        try writer.endObject();
    }
};

/// One transition of Luau's generalized iteration protocol. The initial
/// transition performs `__iter`, callable, or builtin-table preparation before
/// obtaining the first values. Later transitions reuse the prepared iterator
/// and state with the previous first result as control. Results are
/// `[has_value, prepared_iterator, prepared_state, variables...]`; the first
/// variable is also the next control value.
pub const GenericForNext = struct {
    iterator: ValueId,
    state: ValueId,
    control: ValueId,
    initial: ValueId,
    variable_count: u16,
};

pub const CaptureBinding = union(enum) {
    value: ValueId,
    place: PlaceId,
};

pub const Closure = struct {
    function: FunctionId,
    bindings: []const CaptureBinding,
};

pub const Operation = union(enum) {
    constant: Literal,
    copy: ValueId,
    unary: Unary,
    binary: Binary,
    call: Call,
    call_repeated_table_get: CallRepeatedTableGet,
    namecall: Namecall,
    protected_call: ProtectedCall,
    coroutine_create: CoroutineCreate,
    coroutine_resume: CoroutineResume,
    coroutine_yield: CoroutineYield,
    environment_get: EnvironmentGet,
    environment_set: EnvironmentSet,
    table_get: TableGet,
    table_set: TableSet,
    table_set_pack: TableSetPack,
    make_table: void,
    make_table_literal: TableConstructor,
    string_interpolate: StringInterpolation,
    make_closure: Closure,
    function_ref: FunctionId,
    place_read: PlaceId,
    place_write: PlaceWrite,
    pack_values: []const ValueId,
    adjust_pack: ValuePackId,
    numeric_for_next: NumericForNext,
    generic_for_next: GenericForNext,
};

pub const ValueOrigin = union(enum) {
    parameter: u32,
    block_parameter: struct {
        block: BlockId,
        index: u32,
    },
    instruction_result: struct {
        instruction: InstructionId,
        index: u32,
    },
    capture: CaptureId,
};

pub const Value = struct {
    id: ValueId,
    function: FunctionId,
    type: ValueType = .dynamic,
    name_hint: ?[]const u8 = null,
    origin: ValueOrigin,
};

pub const PlaceOrigin = union(enum) {
    local: u32,
    instruction: InstructionId,
    capture: CaptureId,
};

pub const Place = struct {
    id: PlaceId,
    function: FunctionId,
    type: ValueType = .dynamic,
    name_hint: ?[]const u8 = null,
    origin: PlaceOrigin,
    evidence: []const EvidenceId = &.{},
};

pub const CaptureKind = union(enum) {
    immutable_value: ValueId,
    shared_place: PlaceId,
};

pub const Capture = struct {
    id: CaptureId,
    function: FunctionId,
    kind: CaptureKind,
    evidence: []const EvidenceId = &.{},
};

pub const ExternalBindingKind = enum {
    immutable_value,
    shared_place,
};

/// One host-supplied slot used to construct the entry closure. Reusing an ID
/// in `Program.entry_bindings` preserves external value or place identity.
pub const ExternalBinding = struct {
    id: ExternalBindingId,
    kind: ExternalBindingKind,
    type: ValueType = .dynamic,
    evidence: []const EvidenceId = &.{},
};

pub const ValuePackOrigin = union(enum) {
    varargs: FunctionId,
    instruction_result: InstructionId,
};

pub const PackTail = enum {
    closed,
    open,
};

pub const PackShape = struct {
    prefix: []const ValueType = &.{},
    tail: PackTail = .open,

    pub const open_unknown: PackShape = .{};
};

pub const ValuePack = struct {
    id: ValuePackId,
    function: FunctionId,
    origin: ValuePackOrigin,
    shape: PackShape = .open_unknown,
    evidence: []const EvidenceId = &.{},
};

pub const Instruction = struct {
    id: InstructionId,
    block: BlockId,
    operation: Operation,
    results: []const ValueId,
    pack_result: ?ValuePackId = null,
    effects: EffectSummary,
    evidence: []const EvidenceId = &.{},
    claims: []const ClaimId = &.{},
};

pub const Edge = struct {
    target: BlockId,
    arguments: []const ValueId = &.{},
};

pub const Branch = struct {
    condition: ValueId,
    then_edge: Edge,
    else_edge: Edge,
};

pub const ExpandedReturn = struct {
    values: []const ValueId,
    pack: ValuePackId,
};

pub const ThrowError = struct {
    value: ValueId,
    level: u32,
    dynamic_level: ?ValueId = null,
};

pub const Terminator = union(enum) {
    jump: Edge,
    branch: Branch,
    return_values: []const ValueId,
    return_pack: ValuePackId,
    return_expanded: ExpandedReturn,
    throw_error: ThrowError,
    unreachable_block: void,
};

pub const Block = struct {
    id: BlockId,
    function: FunctionId,
    name_hint: ?[]const u8 = null,
    parameters: []const ValueId = &.{},
    instructions: []const InstructionId = &.{},
    terminator: Terminator,
    evidence: []const EvidenceId = &.{},
};

pub const Function = struct {
    id: FunctionId,
    name_hint: ?[]const u8 = null,
    lexical_parent: ?FunctionId = null,
    parameters: []const ValueId = &.{},
    captures: []const CaptureId = &.{},
    local_places: []const PlaceId = &.{},
    blocks: []const BlockId,
    entry_block: BlockId,
    is_variadic: bool = false,
    vararg_pack: ?ValuePackId = null,
    evidence: []const EvidenceId = &.{},
};

pub const EvidenceKind = enum {
    source_span,
    decoded_record,
    dynamic_fixture,
    frontend_proof,
    solver_certificate,
    conformance_oracle,
    structural_derivation,
};

pub const Evidence = struct {
    id: EvidenceId,
    kind: EvidenceKind,
    locator: []const u8,
    digest: ?[]const u8 = null,
};

pub const SolverSortKind = enum {
    boolean,
    integer,
    bit_vector,
    real,
    dynamic_value,
};

pub const SolverSort = struct {
    kind: SolverSortKind,
    bit_width: u16 = 0,
    signed: bool = false,
};

pub const SolverBinaryOperator = enum {
    equal,
    not_equal,
    less,
    less_equal,
    greater,
    greater_equal,
    logical_and,
    logical_or,
    add,
    subtract,
    multiply,
    bit_and,
    bit_or,
    bit_xor,
    shift_left,
    shift_right,
};

pub const SolverBinary = struct {
    operator: SolverBinaryOperator,
    left: SolverTermId,
    right: SolverTermId,
};

pub const SolverValueDefinition = struct {
    value: ValueId,
    expression: SolverTermId,
    /// Optional condition under which the solver expression is semantically
    /// identical to the admitted IR value. Every query using this term must
    /// establish the condition through its assumptions.
    valid_when: ?SolverTermId = null,
};

pub const SolverIfThenElse = struct {
    condition: SolverTermId,
    then_term: SolverTermId,
    else_term: SolverTermId,
};

pub const SolverBitVectorExtract = struct {
    operand: SolverTermId,
    high: u16,
    low: u16,
};

pub const SolverBitVectorConcat = struct {
    high: SolverTermId,
    low: SolverTermId,
};

pub const SolverBitVectorExtension = enum {
    zero,
    sign,
};

pub const SolverBitVectorExtend = struct {
    operand: SolverTermId,
    extra_bits: u16,
    mode: SolverBitVectorExtension,
};

pub const SolverBitVectorRotation = enum {
    left,
    right,
};

pub const SolverBitVectorRotate = struct {
    operand: SolverTermId,
    amount: SolverTermId,
    direction: SolverBitVectorRotation,
};

pub const SolverBitVectorToInteger = struct {
    operand: SolverTermId,
    signed: bool,
};

pub const SolverDivisionMode = enum {
    integer_euclidean,
    integer_floor,
    real,
    bit_vector_unsigned,
    bit_vector_signed,
};

pub const SolverDivision = struct {
    mode: SolverDivisionMode,
    left: SolverTermId,
    right: SolverTermId,
    defined_by: SolverTermId,
};

pub const SolverRemainderMode = enum {
    integer_euclidean,
    integer_floor,
    bit_vector_unsigned,
    bit_vector_signed_dividend,
    bit_vector_signed_divisor,
};

pub const SolverRemainder = struct {
    mode: SolverRemainderMode,
    left: SolverTermId,
    right: SolverTermId,
    defined_by: SolverTermId,
};

pub const BitVectorLiteral = struct {
    value: []const u8,
    bit_width: u16,
};

pub const SemanticAtom = union(enum) {
    instruction_effects: InstructionId,
    no_metamethod_dispatch: InstructionId,
    primitive_operator_domain: InstructionId,
};

pub const SolverTermOperation = union(enum) {
    value: ValueId,
    value_definition: SolverValueDefinition,
    semantic_atom: SemanticAtom,
    dynamic_truthiness: SolverTermId,
    dynamic_number_is_nan: SolverTermId,
    boolean_literal: bool,
    integer_literal: []const u8,
    real_literal: SolverRational,
    bit_vector_literal: BitVectorLiteral,
    logical_not: SolverTermId,
    binary: SolverBinary,
    if_then_else: SolverIfThenElse,
    bit_vector_not: SolverTermId,
    bit_vector_extract: SolverBitVectorExtract,
    bit_vector_concat: SolverBitVectorConcat,
    bit_vector_extend: SolverBitVectorExtend,
    bit_vector_rotate: SolverBitVectorRotate,
    integer_to_bit_vector: SolverTermId,
    bit_vector_to_integer: SolverBitVectorToInteger,
    arithmetic_negate: SolverTermId,
    is_nonzero: SolverTermId,
    division: SolverDivision,
    remainder: SolverRemainder,
};

pub const SolverTerm = struct {
    id: SolverTermId,
    sort: SolverSort,
    operation: SolverTermOperation,
};

pub const ConstraintScope = union(enum) {
    explicit_only: void,
    program: void,
    function: FunctionId,
    block: BlockId,
    edge: CfgEdgeRef,
};

pub const CfgEdgeKind = enum {
    jump,
    branch_then,
    branch_else,
};

pub const CfgEdgeRef = struct {
    source: BlockId,
    kind: CfgEdgeKind,
    target: BlockId,
};

pub const EdgeRewriteRule = enum {
    proved_branch,
    forwarding_jump,
    node_split,
    clone_fold,
};

pub const CfgEdgeRewrite = struct {
    id: EdgeRewriteId,
    source: BlockId,
    kind: CfgEdgeKind,
    from: Edge,
    to: Edge,
    rule: EdgeRewriteRule = .proved_branch,
    certificate: ?CertificateId = null,
    node_split_group: ?NodeSplitGroupId = null,

    pub fn jsonStringify(self: CfgEdgeRewrite, writer: anytype) !void {
        try writer.beginObject();
        try writer.objectField("id");
        try writer.write(self.id);
        try writer.objectField("source");
        try writer.write(self.source);
        try writer.objectField("kind");
        try writer.write(self.kind);
        try writer.objectField("from");
        try writer.write(self.from);
        try writer.objectField("to");
        try writer.write(self.to);
        try writer.objectField("rule");
        try writer.write(self.rule);
        try writer.objectField("certificate");
        try writer.write(self.certificate);
        if (self.node_split_group) |group| {
            try writer.objectField("node_split_group");
            try writer.write(group);
        }
        try writer.endObject();
    }
};

pub const Constraint = struct {
    id: ConstraintId,
    predicate: SolverTermId,
    evidence: []const EvidenceId = &.{},
    scope: ConstraintScope = .{ .explicit_only = {} },
    path_rewrites: []const EdgeRewriteId = &.{},
};

pub const QueryKind = enum {
    prove_true,
    prove_false,
    prove_equivalent,
    prove_unreachable,
    find_model,
};

pub const SolverQuery = struct {
    id: QueryId,
    kind: QueryKind,
    assumptions: []const ConstraintId = &.{},
    path_rewrites: []const EdgeRewriteId = &.{},
    goal: SolverTermId,
};

pub const SolverEngine = enum {
    internal_facts,
    z3,
    imported,
};

pub const SolverRational = struct {
    numerator: []const u8,
    denominator: []const u8,
};

pub const SolverModelValue = union(enum) {
    boolean: bool,
    integer: []const u8,
    real: SolverRational,
    bit_vector: BitVectorLiteral,
    dynamic_identity: u32,
};

pub const SolverModelBinding = struct {
    term: SolverTermId,
    value: SolverModelValue,
};

pub const SolverModel = struct {
    id: SolverModelId,
    query: QueryId,
    bindings: []const SolverModelBinding,
    evidence: []const EvidenceId = &.{},
};

pub const UnsatCore = struct {
    id: UnsatCoreId,
    query: QueryId,
    constraints: []const ConstraintId,
    evidence: []const EvidenceId = &.{},
};

pub const SolverResolution = enum {
    proved,
    disproved,
    unknown,
};

pub const SolverCertificate = struct {
    id: CertificateId,
    query: QueryId,
    engine: SolverEngine,
    resolution: SolverResolution,
    evidence: []const EvidenceId = &.{},
    certificate_digest: ?[]const u8 = null,
    model: ?SolverModelId = null,
    unsat_core: ?UnsatCoreId = null,
};

pub const EntityRef = union(enum) {
    program: void,
    function: FunctionId,
    block: BlockId,
    instruction: InstructionId,
    value: ValueId,
    value_pack: ValuePackId,
    place: PlaceId,
    capture: CaptureId,
    external_binding: ExternalBindingId,
};

pub const ControlBranchSubject = struct {
    block: BlockId,
    branch: Branch,
};

pub const ObligationSubject = union(enum) {
    program: void,
    function: FunctionId,
    block: BlockId,
    instruction: InstructionId,
    value: ValueId,
    value_pack: ValuePackId,
    place: PlaceId,
    capture: CaptureId,
    external_binding: ExternalBindingId,
    control_branch: ControlBranchSubject,
};

pub const ClaimStatus = enum {
    unproven,
    proved,
    disproved,
};

pub const ClaimPurpose = union(enum) {
    generic_predicate: void,
    effect_summary: EffectSummary,
    no_metamethod_dispatch: EffectSummary,
    primitive_operator_domain: EffectSummary,
};

pub const Claim = struct {
    id: ClaimId,
    subject: EntityRef,
    predicate: SolverTermId,
    purpose: ClaimPurpose = .{ .generic_predicate = {} },
    status: ClaimStatus,
    required_for_emission: bool = false,
    evidence: []const EvidenceId = &.{},
    query: ?QueryId = null,
    certificate: ?CertificateId = null,
};

pub const ObligationKind = enum {
    missing_semantics,
    unresolved_identity,
    unknown_effects,
    effect_proof,
    dispatch_proof,
    primitive_domain,
    unknown_arity,
    alias_proof,
    control_structure,
    closure_ownership,
    numeric_domain,
    target_support,
};

pub const ObligationStatus = enum {
    open,
    discharged,
};

pub const ObligationRequirement = struct {
    kind: QueryKind,
    predicate: SolverTermId,

    pub fn fromQuery(query: SolverQuery) ObligationRequirement {
        return .{ .kind = query.kind, .predicate = query.goal };
    }
};

pub const AdmissionProfile = enum {
    core,
    readable_luau,
};

pub const Obligation = struct {
    id: ObligationId,
    kind: ObligationKind,
    subject: ObligationSubject,
    status: ObligationStatus,
    blocks_profile: AdmissionProfile,
    detail: []const u8,
    evidence: []const EvidenceId = &.{},
    requirement: ?ObligationRequirement = null,
    query: ?QueryId = null,
    certificate: ?CertificateId = null,

    pub fn jsonStringify(self: Obligation, writer: anytype) !void {
        try writer.beginObject();
        try writer.objectField("id");
        try writer.write(self.id);
        try writer.objectField("kind");
        try writer.write(self.kind);
        try writer.objectField("subject");
        try writer.write(self.subject);
        try writer.objectField("status");
        try writer.write(self.status);
        try writer.objectField("blocks_profile");
        try writer.write(self.blocks_profile);
        try writer.objectField("detail");
        try writer.write(self.detail);
        try writer.objectField("evidence");
        try writer.write(self.evidence);
        if (self.requirement) |requirement| {
            try writer.objectField("requirement");
            try writer.write(requirement);
        }
        try writer.objectField("query");
        try writer.write(self.query);
        try writer.objectField("certificate");
        try writer.write(self.certificate);
        try writer.endObject();
    }
};

pub const Program = struct {
    schema_version: SchemaVersion = .lifter_ir_v1,
    program_id: []const u8,
    source_semantics: SourceSemantics = .luau,
    entry_function: FunctionId,
    entry_bindings: []const ExternalBindingId = &.{},
    external_bindings: []const ExternalBinding = &.{},
    functions: []const Function,
    blocks: []const Block,
    instructions: []const Instruction,
    values: []const Value,
    value_packs: []const ValuePack = &.{},
    places: []const Place = &.{},
    captures: []const Capture = &.{},
    evidence: []const Evidence = &.{},
    solver_terms: []const SolverTerm = &.{},
    constraints: []const Constraint = &.{},
    queries: []const SolverQuery = &.{},
    solver_models: []const SolverModel = &.{},
    unsat_cores: []const UnsatCore = &.{},
    certificates: []const SolverCertificate = &.{},
    edge_rewrites: []const CfgEdgeRewrite = &.{},
    claims: []const Claim = &.{},
    obligations: []const Obligation = &.{},
};

test "entity ids remain type-safe and indexable" {
    const function_id = FunctionId.fromIndex(4);
    const value_id = ValueId.fromIndex(4);
    const pack_id = ValuePackId.fromIndex(4);
    try std.testing.expectEqual(@as(usize, 4), function_id.index());
    try std.testing.expectEqual(@as(usize, 4), value_id.index());
    try std.testing.expectEqual(@as(usize, 4), pack_id.index());
    try std.testing.expectEqualStrings("function", function_id.entityLabel());
    try std.testing.expectEqualStrings("value", value_id.entityLabel());
    try std.testing.expectEqualStrings("value-pack", pack_id.entityLabel());
}
