--!strict

-- A reusable Luau construction surface for the Zig-owned semantic IR contract.
-- This module owns canonical IDs and reverse links, but Zig remains the
-- authority for semantic validation and admission.

local JsonCodec = require("./json_codec")

local LifterIR = {}

type Record = { [string]: any }
type RecordArray = { Record }
type IdArray = { number }

local function newArray<T>(): { T }
	return JsonCodec.newArray() :: { T }
end

local function copyArray<T>(values: { T }?): { T }
	local result: { T } = newArray()
	if values ~= nil then
		for _, value in values do
			table.insert(result, value)
		end
	end
	return result
end

function LifterIR.encodeJson(value: any, pretty: boolean?): string
	return JsonCodec.encode(value, pretty)
end

local function tagged(name: string, payload: any): Record
	return { [name] = payload }
end

local function stringBytesHex(value: string): string
	local encoded = table.create(#value)
	for index = 1, #value do
		encoded[index] = string.format("%02x", string.byte(value, index))
	end
	return table.concat(encoded)
end

local function transportString(value: string): any
	if utf8.len(value) ~= nil then
		return value
	end
	return tagged("string_bytes", stringBytesHex(value))
end

local function assertDenseId(id: number, label: string)
	assert(type(id) == "number" and id >= 0 and id % 1 == 0, `{label} ID must be a non-negative integer`)
end

local function assertCanonicalDecimal(value: string, signed: boolean)
	local digits = value
	if string.sub(value, 1, 1) == "-" then
		assert(signed, "unsigned decimal must not be negative")
		digits = string.sub(value, 2)
		assert(string.sub(digits, 1, 1) ~= "0", "signed decimal must not use -0 or leading zeroes")
	end
	assert(digits ~= "", "decimal must contain digits")
	assert(string.match(digits, "^%d+$") ~= nil, "decimal must contain only base-10 digits")
	assert(#digits == 1 or string.sub(digits, 1, 1) ~= "0", "decimal must not contain leading zeroes")
end

local function assertBitWidth(bitWidth: number, label: string)
	assert(bitWidth % 1 == 0 and bitWidth >= 1 and bitWidth <= 65535, `{label} must be an integer from 1 through 65535`)
end

local function assertBitIndex(bitIndex: number, label: string)
	assert(bitIndex % 1 == 0 and bitIndex >= 0 and bitIndex <= 65535, `{label} must be an integer from 0 through 65535`)
end

local function containsValue(values: any, expected: string): boolean
	for _, value in values do
		if value == expected then
			return true
		end
	end
	return false
end

local function makeValueType(kind: string, bitWidth: number?, signed: boolean?): Record
	-- Width/sign fields refine source values. They do not request implicit
	-- machine wrapping or narrower floating-point operation semantics.
	return {
		kind = kind,
		bit_width = bitWidth or 0,
		signed = signed or false,
	}
end

LifterIR.Types = table.freeze({
	dynamic = function(): Record
		return makeValueType("dynamic")
	end,
	nilValue = function(): Record
		return makeValueType("nil_value")
	end,
	boolean = function(): Record
		return makeValueType("boolean")
	end,
	integer = function(bitWidth: number?, signed: boolean?): Record
		local width = bitWidth or 64
		assertBitWidth(width, "integer value bit width")
		return makeValueType("integer", width, if signed == nil then true else signed)
	end,
	number = function(bitWidth: number?): Record
		local width = bitWidth or 64
		assert(width == 32 or width == 64, "number value bit width must be 32 or 64")
		return makeValueType("number", width)
	end,
	string = function(): Record
		return makeValueType("string")
	end,
	table = function(): Record
		return makeValueType("table")
	end,
	functionValue = function(): Record
		return makeValueType("function")
	end,
	thread = function(): Record
		return makeValueType("thread")
	end,
	userdata = function(): Record
		return makeValueType("userdata")
	end,
	tuple = function(): Record
		return makeValueType("tuple")
	end,
})

local function makeEffects(precision: string, options: Record?): Record
	local source: Record = options or ({} :: Record)
	return {
		precision = precision,
		reads_memory = source.reads_memory == true,
		writes_memory = source.writes_memory == true,
		may_throw = source.may_throw == true,
		may_yield = source.may_yield == true,
		invokes_unknown_code = source.invokes_unknown_code == true,
	}
end

LifterIR.Effects = table.freeze({
	pure = function(): Record
		return makeEffects("exact")
	end,
	placeRead = function(): Record
		return makeEffects("exact", { reads_memory = true })
	end,
	placeWrite = function(): Record
		return makeEffects("exact", { writes_memory = true })
	end,
	rawTableRead = function(): Record
		return makeEffects("exact", { reads_memory = true, may_throw = true })
	end,
	rawTableWrite = function(): Record
		return makeEffects("exact", { writes_memory = true, may_throw = true })
	end,
	semanticTableRead = function(): Record
		return makeEffects("conservative", {
			reads_memory = true,
			writes_memory = true,
			may_throw = true,
			may_yield = true,
			invokes_unknown_code = true,
		})
	end,
	semanticTableWrite = function(): Record
		return makeEffects("conservative", {
			reads_memory = true,
			writes_memory = true,
			may_throw = true,
			may_yield = true,
			invokes_unknown_code = true,
		})
	end,
	protectedInvocation = function(): Record
		return makeEffects("conservative", {
			reads_memory = true,
			writes_memory = true,
			may_throw = true,
			may_yield = true,
			invokes_unknown_code = true,
		})
	end,
	coroutineCreate = function(): Record
		return makeEffects("exact", { may_throw = true })
	end,
	coroutineResume = function(): Record
		return LifterIR.Effects.protectedInvocation()
	end,
	coroutineYield = function(): Record
		return LifterIR.Effects.protectedInvocation()
	end,
	dynamicCall = function(): Record
		return LifterIR.Effects.protectedInvocation()
	end,
	namecall = function(): Record
		return LifterIR.Effects.dynamicCall()
	end,
	numericForNext = function(): Record
		return makeEffects("exact", { may_throw = true })
	end,
	genericForNext = function(): Record
		return LifterIR.Effects.dynamicCall()
	end,
	tableConstructor = function(): Record
		return makeEffects("exact", { writes_memory = true, may_throw = true })
	end,
	stringInterpolation = function(): Record
		return LifterIR.Effects.dynamicCall()
	end,
	exact = function(options: Record?): Record
		return makeEffects("exact", options)
	end,
	conservative = function(options: Record?): Record
		return makeEffects("conservative", options)
	end,
	unknown = function(options: Record?): Record
		return makeEffects("unknown", options)
	end,
})

LifterIR.Literal = table.freeze({
	nilValue = function(): Record
		return tagged("nil_value", {})
	end,
	boolean = function(value: boolean): Record
		return tagged("boolean", value)
	end,
	integer = function(value: string): Record
		assertCanonicalDecimal(value, true)
		return tagged("integer", value)
	end,
	number = function(value: number): Record
		return tagged("number", value)
	end,
	specialNumber = function(value: string): Record
		assert(
			value == "nan" or value == "positive_infinity" or value == "negative_infinity",
			"unknown special number literal"
		)
		return tagged("special_number", value)
	end,
	string = function(value: string): Record
		local transported = transportString(value)
		return if type(transported) == "string" then tagged("string", transported) else transported :: Record
	end,
})

LifterIR.ResultArity = table.freeze({
	fixed = function(count: number): Record
		assertDenseId(count, "result count")
		return tagged("fixed", count)
	end,
	variadic = function(): Record
		return tagged("variadic", {})
	end,
})

local shiftBehaviors = table.freeze({
	luau_bit32 = true,
	zero_saturating = true,
})

LifterIR.ShiftBehavior = table.freeze({
	luauBit32 = "luau_bit32",
	zeroSaturating = "zero_saturating",
})

LifterIR.NumericForMode = table.freeze({
	luauNumeric = "luau_numeric",
	semanticNormalized = "semantic_normalized",
})

LifterIR.Operation = table.freeze({
	constant = function(literal: Record): Record
		return tagged("constant", literal)
	end,
	copy = function(value: number): Record
		return tagged("copy", value)
	end,
	unary = function(operator: string, operand: number, mode: string?): Record
		return tagged("unary", { operator = operator, operand = operand, mode = mode or "semantic" })
	end,
	binary = function(operator: string, left: number, right: number, mode: string?, shiftBehavior: string?): Record
		local isShift = operator == "shift_left" or operator == "shift_right"
		if isShift then
			assert(shiftBehavior ~= nil and shiftBehaviors[shiftBehavior] == true, "shift operation requires explicit behavior")
		else
			assert(shiftBehavior == nil, "nonshift operation cannot carry shift behavior")
		end
		local binary: Record = { operator = operator, left = left, right = right, mode = mode or "semantic" }
		if shiftBehavior ~= nil then
			binary.shift_behavior = shiftBehavior
		end
		return tagged("binary", binary)
	end,
	call = function(callee: number, arguments: IdArray, resultArity: Record, argumentPack: number?): Record
		local call: Record = {
			callee = callee,
			arguments = copyArray(arguments),
			result_arity = resultArity,
		}
		if argumentPack ~= nil then
			call.argument_pack = argumentPack
		end
		return tagged("call", call)
	end,
	callRepeatedTableGet = function(
		callee: number,
		prefixArguments: IdArray,
		tableValue: number,
		key: number,
		from: number,
		to: number,
		step: number,
		counter: number?,
		resultArity: Record
	): Record
		local call: Record = {
			callee = callee,
			prefix_arguments = copyArray(prefixArguments),
			table = tableValue,
			key = key,
			from = from,
			to = to,
			step = step,
			result_arity = resultArity,
		}
		if counter ~= nil then
			call.counter = counter
		end
		return tagged("call_repeated_table_get", call)
	end,
	namecall = function(
		receiver: number,
		method: string,
		arguments: IdArray,
		resultArity: Record,
		argumentPack: number?
	): Record
		assert(method ~= "", "namecall method must not be empty")
		local invocation: Record = {
			receiver = receiver,
			method = method,
			arguments = copyArray(arguments),
			result_arity = resultArity,
		}
		if argumentPack ~= nil then
			invocation.argument_pack = argumentPack
		end
		return tagged("namecall", invocation)
	end,
	protectedCall = function(
		callee: number,
		errorHandler: number?,
		arguments: IdArray,
		resultArity: Record,
		argumentPack: number?
	): Record
		local call: Record = {
			callee = callee,
			arguments = copyArray(arguments),
			result_arity = resultArity,
		}
		if errorHandler ~= nil then
			call.error_handler = errorHandler
		end
		if argumentPack ~= nil then
			call.argument_pack = argumentPack
		end
		return tagged("protected_call", call)
	end,
	coroutineCreate = function(callee: number): Record
		return tagged("coroutine_create", { callee = callee })
	end,
	coroutineResume = function(thread: number, arguments: IdArray, resultArity: Record, argumentPack: number?): Record
		local resume: Record = {
			thread = thread,
			arguments = copyArray(arguments),
			result_arity = resultArity,
		}
		if argumentPack ~= nil then
			resume.argument_pack = argumentPack
		end
		return tagged("coroutine_resume", resume)
	end,
	coroutineYield = function(arguments: IdArray, resultArity: Record, argumentPack: number?): Record
		local yieldOperation: Record = {
			arguments = copyArray(arguments),
			result_arity = resultArity,
		}
		if argumentPack ~= nil then
			yieldOperation.argument_pack = argumentPack
		end
		return tagged("coroutine_yield", yieldOperation)
	end,
	packValues = function(values: IdArray): Record
		return tagged("pack_values", copyArray(values))
	end,
	environmentGet = function(target: Record, name: string, mode: string?): Record
		return tagged("environment_get", { target = target, name = name, mode = mode or "semantic" })
	end,
	environmentSet = function(target: Record, name: string, value: number, mode: string?): Record
		return tagged("environment_set", {
			target = target,
			name = name,
			value = value,
			mode = mode or "semantic",
		})
	end,
	tableGet = function(tableValue: number, key: number, mode: string?): Record
		return tagged("table_get", { table = tableValue, key = key, mode = mode or "semantic" })
	end,
	tableSet = function(tableValue: number, key: number, value: number, mode: string?): Record
		return tagged("table_set", { table = tableValue, key = key, value = value, mode = mode or "semantic" })
	end,
	tableSetPack = function(tableValue: number, firstIndex: number, pack: number): Record
		assert(firstIndex >= 0 and firstIndex % 1 == 0, "table pack first index must be a nonnegative integer")
		return tagged("table_set_pack", { table = tableValue, first_index = firstIndex, pack = pack })
	end,
	makeTable = function(): Record
		return tagged("make_table", {})
	end,
	makeTableLiteral = function(fields: RecordArray, tailPack: number?): Record
		local constructor: Record = { fields = copyArray(fields) }
		if tailPack ~= nil then
			constructor.tail_pack = tailPack
		end
		return tagged("make_table_literal", constructor)
	end,
	stringInterpolate = function(segments: { string }, values: IdArray): Record
		local transportedSegments: { any } = newArray()
		for _, segment in segments do
			table.insert(transportedSegments, transportString(segment))
		end
		return tagged("string_interpolate", {
			segments = transportedSegments,
			values = copyArray(values),
		})
	end,
	makeClosure = function(functionId: number, bindings: RecordArray): Record
		return tagged("make_closure", { ["function"] = functionId, bindings = copyArray(bindings) })
	end,
	functionRef = function(functionId: number): Record
		return tagged("function_ref", functionId)
	end,
	placeRead = function(placeId: number): Record
		return tagged("place_read", placeId)
	end,
	placeWrite = function(placeId: number, valueId: number): Record
		return tagged("place_write", { place = placeId, value = valueId })
	end,
	adjustPack = function(packId: number): Record
		return tagged("adjust_pack", packId)
	end,
	numericForNext = function(control: number, limit: number, step: number, initial: number, mode: string?): Record
		local transition: Record = {
			control = control,
			limit = limit,
			step = step,
			initial = initial,
		}
		if mode ~= nil and mode ~= LifterIR.NumericForMode.luauNumeric then
			assert(mode == LifterIR.NumericForMode.semanticNormalized, "unknown numeric-for transition mode")
			transition.mode = mode
		end
		return tagged("numeric_for_next", transition)
	end,
	genericForNext = function(
		iterator: number,
		state: number,
		control: number,
		initial: number,
		variableCount: number
	): Record
		assertDenseId(variableCount, "generic-for variable count")
		return tagged("generic_for_next", {
			iterator = iterator,
			state = state,
			control = control,
			initial = initial,
			variable_count = variableCount,
		})
	end,
})

LifterIR.TableConstructorField = table.freeze({
	list = function(valueId: number): Record
		return tagged("list", valueId)
	end,
	keyed = function(keyId: number, valueId: number): Record
		return tagged("keyed", { key = keyId, value = valueId })
	end,
})

LifterIR.Origin = table.freeze({
	parameter = function(index: number): Record
		return tagged("parameter", index)
	end,
	blockParameter = function(block: number, index: number): Record
		return tagged("block_parameter", { block = block, index = index })
	end,
	instructionResult = function(instruction: number, index: number): Record
		return tagged("instruction_result", { instruction = instruction, index = index })
	end,
	capture = function(captureId: number): Record
		return tagged("capture", captureId)
	end,
})

LifterIR.EnvironmentTarget = table.freeze({
	ambient = function(): Record
		return tagged("ambient", {})
	end,
	value = function(valueId: number): Record
		return tagged("value", valueId)
	end,
})

LifterIR.PlaceOrigin = table.freeze({
	localPlace = function(index: number): Record
		return tagged("local", index)
	end,
	instruction = function(instructionId: number): Record
		return tagged("instruction", instructionId)
	end,
	capture = function(captureId: number): Record
		return tagged("capture", captureId)
	end,
})

LifterIR.CaptureKind = table.freeze({
	immutableValue = function(valueId: number): Record
		return tagged("immutable_value", valueId)
	end,
	sharedPlace = function(placeId: number): Record
		return tagged("shared_place", placeId)
	end,
})

LifterIR.CaptureBinding = table.freeze({
	value = function(valueId: number): Record
		return tagged("value", valueId)
	end,
	place = function(placeId: number): Record
		return tagged("place", placeId)
	end,
})

LifterIR.ExternalBindingKind = table.freeze({
	immutableValue = "immutable_value",
	sharedPlace = "shared_place",
})

LifterIR.PackOrigin = table.freeze({
	varargs = function(functionId: number): Record
		return tagged("varargs", functionId)
	end,
	instructionResult = function(instructionId: number): Record
		return tagged("instruction_result", instructionId)
	end,
})

LifterIR.PackShape = table.freeze({
	open = function(prefix: RecordArray?): Record
		return { prefix = copyArray(prefix), tail = "open" }
	end,
	closed = function(values: RecordArray?): Record
		return { prefix = copyArray(values), tail = "closed" }
	end,
})

LifterIR.Edge = function(target: number, arguments: IdArray?): Record
	return { target = target, arguments = copyArray(arguments) }
end

LifterIR.Terminator = table.freeze({
	jump = function(edge: Record): Record
		return tagged("jump", edge)
	end,
	branch = function(condition: number, thenEdge: Record, elseEdge: Record): Record
		return tagged("branch", {
			condition = condition,
			then_edge = thenEdge,
			else_edge = elseEdge,
		})
	end,
	returnValues = function(values: IdArray): Record
		return tagged("return_values", copyArray(values))
	end,
	returnPack = function(packId: number): Record
		return tagged("return_pack", packId)
	end,
	returnExpanded = function(values: IdArray, packId: number): Record
		return tagged("return_expanded", { values = copyArray(values), pack = packId })
	end,
	throwError = function(value: number, level: number, dynamicLevel: number?): Record
		local throwError: Record = { value = value, level = level }
		if dynamicLevel ~= nil then
			throwError.dynamic_level = dynamicLevel
		end
		return tagged("throw_error", throwError)
	end,
	unreachable = function(): Record
		return tagged("unreachable_block", {})
	end,
})

local function makeSolverSort(kind: string, bitWidth: number?, signed: boolean?): Record
	return {
		kind = kind,
		bit_width = bitWidth or 0,
		signed = signed or false,
	}
end

LifterIR.SolverSort = table.freeze({
	boolean = function(): Record
		return makeSolverSort("boolean")
	end,
	integer = function(): Record
		return makeSolverSort("integer")
	end,
	bitVector = function(bitWidth: number, signed: boolean?): Record
		assertBitWidth(bitWidth, "solver bit-vector width")
		return makeSolverSort("bit_vector", bitWidth, signed)
	end,
	real = function(): Record
		return makeSolverSort("real")
	end,
	dynamicValue = function(): Record
		return makeSolverSort("dynamic_value")
	end,
})

LifterIR.SemanticAtom = table.freeze({
	instructionEffects = function(instructionId: number): Record
		return tagged("instruction_effects", instructionId)
	end,
	noMetamethodDispatch = function(instructionId: number): Record
		return tagged("no_metamethod_dispatch", instructionId)
	end,
	primitiveOperatorDomain = function(instructionId: number): Record
		return tagged("primitive_operator_domain", instructionId)
	end,
})

local solverBinaryOperators = table.freeze({
	"equal",
	"not_equal",
	"less",
	"less_equal",
	"greater",
	"greater_equal",
	"logical_and",
	"logical_or",
	"add",
	"subtract",
	"multiply",
	"bit_and",
	"bit_or",
	"bit_xor",
	"shift_left",
	"shift_right",
})

LifterIR.SolverTerm = table.freeze({
	value = function(valueId: number): Record
		return tagged("value", valueId)
	end,
	valueDefinition = function(valueId: number, expression: number, validWhen: number?): Record
		return tagged("value_definition", { value = valueId, expression = expression, valid_when = validWhen })
	end,
	semanticAtom = function(atom: Record): Record
		return tagged("semantic_atom", atom)
	end,
	dynamicTruthiness = function(operand: number): Record
		return tagged("dynamic_truthiness", operand)
	end,
	dynamicNumberIsNaN = function(operand: number): Record
		return tagged("dynamic_number_is_nan", operand)
	end,
	booleanLiteral = function(value: boolean): Record
		return tagged("boolean_literal", value)
	end,
	integerLiteral = function(value: string): Record
		assertCanonicalDecimal(value, true)
		return tagged("integer_literal", value)
	end,
	realLiteral = function(numerator: string, denominator: string): Record
		assertCanonicalDecimal(numerator, true)
		assertCanonicalDecimal(denominator, false)
		assert(denominator ~= "0", "solver rational denominator must not be zero")
		return tagged("real_literal", { numerator = numerator, denominator = denominator })
	end,
	bitVectorLiteral = function(value: string, bitWidth: number): Record
		assertCanonicalDecimal(value, false)
		assertBitWidth(bitWidth, "solver bit-vector literal width")
		return tagged("bit_vector_literal", { value = value, bit_width = bitWidth })
	end,
	logicalNot = function(operand: number): Record
		return tagged("logical_not", operand)
	end,
	binary = function(operator: string, left: number, right: number): Record
		assert(containsValue(solverBinaryOperators, operator), `unknown or partial solver binary operator {operator}`)
		return tagged("binary", { operator = operator, left = left, right = right })
	end,
	ifThenElse = function(condition: number, thenTerm: number, elseTerm: number): Record
		return tagged("if_then_else", {
			condition = condition,
			then_term = thenTerm,
			else_term = elseTerm,
		})
	end,
	bitVectorNot = function(operand: number): Record
		return tagged("bit_vector_not", operand)
	end,
	bitVectorExtract = function(operand: number, high: number, low: number): Record
		assertBitIndex(high, "solver bit-vector extract high index")
		assertBitIndex(low, "solver bit-vector extract low index")
		assert(low <= high, "solver bit-vector extract low index must not exceed its high index")
		return tagged("bit_vector_extract", { operand = operand, high = high, low = low })
	end,
	bitVectorConcat = function(high: number, low: number): Record
		return tagged("bit_vector_concat", { high = high, low = low })
	end,
	bitVectorExtend = function(operand: number, extraBits: number, mode: string): Record
		assertBitWidth(extraBits, "solver bit-vector extension width")
		assert(mode == "zero" or mode == "sign", "solver bit-vector extension mode must be zero or sign")
		return tagged("bit_vector_extend", { operand = operand, extra_bits = extraBits, mode = mode })
	end,
	bitVectorRotate = function(operand: number, amount: number, direction: string): Record
		assert(direction == "left" or direction == "right", "solver bit-vector rotation direction must be left or right")
		return tagged("bit_vector_rotate", { operand = operand, amount = amount, direction = direction })
	end,
	integerToBitVector = function(operand: number): Record
		return tagged("integer_to_bit_vector", operand)
	end,
	bitVectorToInteger = function(operand: number, signed: boolean): Record
		return tagged("bit_vector_to_integer", { operand = operand, signed = signed })
	end,
	arithmeticNegate = function(operand: number): Record
		return tagged("arithmetic_negate", operand)
	end,
	isNonzero = function(operand: number): Record
		return tagged("is_nonzero", operand)
	end,
	division = function(mode: string, left: number, right: number, definedBy: number): Record
		assert(
			mode == "integer_euclidean"
				or mode == "integer_floor"
				or mode == "real"
				or mode == "bit_vector_unsigned"
				or mode == "bit_vector_signed",
			"unknown solver division mode"
		)
		return tagged("division", { mode = mode, left = left, right = right, defined_by = definedBy })
	end,
	remainder = function(mode: string, left: number, right: number, definedBy: number): Record
		assert(
			mode == "integer_euclidean"
				or mode == "integer_floor"
				or mode == "bit_vector_unsigned"
				or mode == "bit_vector_signed_dividend"
				or mode == "bit_vector_signed_divisor",
			"unknown solver remainder mode"
		)
		return tagged("remainder", { mode = mode, left = left, right = right, defined_by = definedBy })
	end,
})

LifterIR.ConstraintScope = table.freeze({
	explicitOnly = function(): Record
		return tagged("explicit_only", {})
	end,
	program = function(): Record
		return tagged("program", {})
	end,
	functionValue = function(functionId: number): Record
		return tagged("function", functionId)
	end,
	block = function(blockId: number): Record
		return tagged("block", blockId)
	end,
	edge = function(sourceBlockId: number, kind: string, targetBlockId: number): Record
		assertDenseId(sourceBlockId, "edge source block")
		assertDenseId(targetBlockId, "edge target block")
		assert(kind == "jump" or kind == "branch_then" or kind == "branch_else", "invalid CFG edge kind")
		return tagged("edge", { source = sourceBlockId, kind = kind, target = targetBlockId })
	end,
})

LifterIR.SolverModelValue = table.freeze({
	boolean = function(value: boolean): Record
		return tagged("boolean", value)
	end,
	integer = function(value: string): Record
		assertCanonicalDecimal(value, true)
		return tagged("integer", value)
	end,
	real = function(numerator: string, denominator: string): Record
		assertCanonicalDecimal(numerator, true)
		assertCanonicalDecimal(denominator, false)
		assert(denominator ~= "0", "solver rational denominator must not be zero")
		return tagged("real", { numerator = numerator, denominator = denominator })
	end,
	bitVector = function(value: string, bitWidth: number): Record
		assertCanonicalDecimal(value, false)
		assertBitWidth(bitWidth, "solver model bit-vector width")
		return tagged("bit_vector", { value = value, bit_width = bitWidth })
	end,
	dynamicIdentity = function(identity: number): Record
		assertDenseId(identity, "solver model dynamic identity")
		assert(identity <= 4294967295, "solver model dynamic identity must fit an unsigned 32-bit integer")
		return tagged("dynamic_identity", identity)
	end,
})

function LifterIR.SolverModelBinding(term: number, value: Record): Record
	return { term = term, value = value }
end

LifterIR.Entity = table.freeze({
	program = function(): Record
		return tagged("program", {})
	end,
	functionEntity = function(id: number): Record
		return tagged("function", id)
	end,
	block = function(id: number): Record
		return tagged("block", id)
	end,
	instruction = function(id: number): Record
		return tagged("instruction", id)
	end,
	value = function(id: number): Record
		return tagged("value", id)
	end,
	valuePack = function(id: number): Record
		return tagged("value_pack", id)
	end,
	place = function(id: number): Record
		return tagged("place", id)
	end,
	capture = function(id: number): Record
		return tagged("capture", id)
	end,
	externalBinding = function(id: number): Record
		return tagged("external_binding", id)
	end,
})

return table.freeze(LifterIR)
