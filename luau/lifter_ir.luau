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

export type ResultSpec = {
	type: Record?,
	name_hint: string?,
}

export type FunctionOptions = {
	name_hint: string?,
	lexical_parent: number?,
	is_variadic: boolean?,
	evidence: IdArray?,
}

export type BlockOptions = {
	name_hint: string?,
	evidence: IdArray?,
}

export type InstructionOptions = {
	effects: Record?,
	evidence: IdArray?,
	claims: IdArray?,
	result_pack_shape: Record?,
}

type BuilderState = {
	program: Record,
	_function_finalized: { boolean },
	_block_finalized: { boolean },
	_finished: boolean,
}

local Builder = {}
Builder.__index = Builder

export type Builder = typeof(setmetatable({} :: BuilderState, Builder))

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

local function getEntity(collection: RecordArray, id: number, label: string): Record
	assertDenseId(id, label)
	local entity = collection[id + 1]
	assert(entity ~= nil, `{label} ID {id} is out of range`)
	return entity
end

local function assertBitWidth(bitWidth: number, label: string)
	assert(bitWidth % 1 == 0 and bitWidth >= 1 and bitWidth <= 65535, `{label} must be an integer from 1 through 65535`)
end

local function assertBitIndex(bitIndex: number, label: string)
	assert(bitIndex % 1 == 0 and bitIndex >= 0 and bitIndex <= 65535, `{label} must be an integer from 0 through 65535`)
end

local function withOptionalName(record: Record, nameHint: string?)
	if nameHint ~= nil then
		record.name_hint = nameHint
	end
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

LifterIR.ObligationKind = table.freeze({
	missingSemantics = "missing_semantics",
	unresolvedIdentity = "unresolved_identity",
	unknownEffects = "unknown_effects",
	effectProof = "effect_proof",
	dispatchProof = "dispatch_proof",
	primitiveDomain = "primitive_domain",
	unknownArity = "unknown_arity",
	aliasProof = "alias_proof",
	controlStructure = "control_structure",
	closureOwnership = "closure_ownership",
	numericDomain = "numeric_domain",
	targetSupport = "target_support",
})

LifterIR.ObligationStatus = table.freeze({
	open = "open",
	discharged = "discharged",
})

LifterIR.AdmissionProfile = table.freeze({
	core = "core",
	readableLuau = "readable_luau",
})

LifterIR.ClaimPurpose = table.freeze({
	genericPredicate = function(): Record
		return tagged("generic_predicate", {})
	end,
	effectSummary = function(effects: Record): Record
		return tagged("effect_summary", effects)
	end,
	noMetamethodDispatch = function(effects: Record): Record
		return tagged("no_metamethod_dispatch", effects)
	end,
	primitiveOperatorDomain = function(effects: Record): Record
		return tagged("primitive_operator_domain", effects)
	end,
})

function Builder.new(programId: string): Builder
	assert(programId ~= "", "program ID must not be empty")
	return setmetatable({
		program = {
			schema_version = "lifter_ir_v1",
			program_id = programId,
			source_semantics = "luau",
			entry_bindings = newArray(),
			external_bindings = newArray(),
			functions = newArray(),
			blocks = newArray(),
			instructions = newArray(),
			values = newArray(),
			value_packs = newArray(),
			places = newArray(),
			captures = newArray(),
			evidence = newArray(),
			solver_terms = newArray(),
			constraints = newArray(),
			queries = newArray(),
			solver_models = newArray(),
			unsat_cores = newArray(),
			certificates = newArray(),
			edge_rewrites = newArray(),
			claims = newArray(),
			obligations = newArray(),
		},
		_function_finalized = newArray(),
		_block_finalized = newArray(),
		_finished = false,
	}, Builder)
end

function Builder:_assertMutable()
	assert(not self._finished, "builder is already finished")
end

function Builder:_function(id: number): Record
	return getEntity(self.program.functions, id, "function")
end

function Builder:_block(id: number): Record
	return getEntity(self.program.blocks, id, "block")
end

function Builder:_instruction(id: number): Record
	return getEntity(self.program.instructions, id, "instruction")
end

function Builder:_value(id: number): Record
	return getEntity(self.program.values, id, "value")
end

function Builder:_valuePack(id: number): Record
	return getEntity(self.program.value_packs, id, "value pack")
end

function Builder:_place(id: number): Record
	return getEntity(self.program.places, id, "place")
end

function Builder:_capture(id: number): Record
	return getEntity(self.program.captures, id, "capture")
end

function Builder:_externalBinding(id: number): Record
	return getEntity(self.program.external_bindings, id, "external binding")
end

function Builder:_assertFunctionOpen(id: number): Record
	local record = self:_function(id)
	assert(not self._function_finalized[id + 1], `function {id} is already finalized`)
	return record
end

function Builder:_assertBlockOpen(id: number): Record
	local record = self:_block(id)
	assert(not self._block_finalized[id + 1], `block {id} is already finalized`)
	return record
end

function Builder:_addValue(functionId: number, valueType: Record?, nameHint: string?, origin: Record): number
	local id = #self.program.values
	local record: Record = {
		id = id,
		["function"] = functionId,
		type = valueType or LifterIR.Types.dynamic(),
		origin = origin,
	}
	withOptionalName(record, nameHint)
	table.insert(self.program.values, record)
	return id
end

function Builder:_addValuePack(functionId: number, origin: Record, evidence: IdArray?, shape: Record?): number
	local id = #self.program.value_packs
	table.insert(self.program.value_packs, {
		id = id,
		["function"] = functionId,
		origin = origin,
		shape = shape or LifterIR.PackShape.open(),
		evidence = copyArray(evidence),
	})
	return id
end

function Builder:_addPlace(
	functionId: number,
	valueType: Record?,
	nameHint: string?,
	origin: Record,
	evidence: IdArray?
): number
	local id = #self.program.places
	local record: Record = {
		id = id,
		["function"] = functionId,
		type = valueType or LifterIR.Types.dynamic(),
		origin = origin,
		evidence = copyArray(evidence),
	}
	withOptionalName(record, nameHint)
	table.insert(self.program.places, record)
	return id
end

function Builder:addEvidence(kind: string, locator: string, digest: string?): number
	self:_assertMutable()
	assert(locator ~= "", "evidence locator must not be empty")
	local id = #self.program.evidence
	local record: Record = { id = id, kind = kind, locator = locator }
	if digest ~= nil then
		assert(digest ~= "", "evidence digest must not be empty")
		record.digest = digest
	end
	table.insert(self.program.evidence, record)
	return id
end

function Builder:reserveFunction(options: FunctionOptions?): number
	self:_assertMutable()
	local source: FunctionOptions = options or ({} :: FunctionOptions)
	local id = #self.program.functions
	local record: Record = {
		id = id,
		parameters = newArray(),
		captures = newArray(),
		local_places = newArray(),
		blocks = newArray(),
		entry_block = -1,
		is_variadic = source.is_variadic == true,
		evidence = copyArray(source.evidence),
	}
	if source.lexical_parent ~= nil then
		self:_function(source.lexical_parent)
		record.lexical_parent = source.lexical_parent
	end
	withOptionalName(record, source.name_hint)
	table.insert(self.program.functions, record)
	table.insert(self._function_finalized, false)
	return id
end

function Builder:reserveBlock(functionId: number, options: BlockOptions?): number
	self:_assertMutable()
	local owner = self:_assertFunctionOpen(functionId)
	local source: BlockOptions = options or ({} :: BlockOptions)
	local id = #self.program.blocks
	local record: Record = {
		id = id,
		["function"] = functionId,
		parameters = newArray(),
		instructions = newArray(),
		evidence = copyArray(source.evidence),
	}
	withOptionalName(record, source.name_hint)
	table.insert(self.program.blocks, record)
	table.insert(self._block_finalized, false)
	table.insert(owner.blocks, id)
	return id
end

function Builder:setEntryFunction(functionId: number)
	self:_assertMutable()
	self:_function(functionId)
	self.program.entry_function = functionId
end

function Builder:setEntryBindings(bindingIds: IdArray)
	self:_assertMutable()
	for _, bindingId in bindingIds do
		self:_externalBinding(bindingId)
	end
	self.program.entry_bindings = copyArray(bindingIds)
end

function Builder:addExternalValueBinding(valueType: Record?, evidence: IdArray?): number
	self:_assertMutable()
	local id = #self.program.external_bindings
	table.insert(self.program.external_bindings, {
		id = id,
		kind = LifterIR.ExternalBindingKind.immutableValue,
		type = valueType or LifterIR.Types.dynamic(),
		evidence = copyArray(evidence),
	})
	return id
end

function Builder:addExternalPlaceBinding(valueType: Record?, evidence: IdArray?): number
	self:_assertMutable()
	local id = #self.program.external_bindings
	table.insert(self.program.external_bindings, {
		id = id,
		kind = LifterIR.ExternalBindingKind.sharedPlace,
		type = valueType or LifterIR.Types.dynamic(),
		evidence = copyArray(evidence),
	})
	return id
end

function Builder:setFunctionEntry(functionId: number, blockId: number)
	self:_assertMutable()
	local functionRecord = self:_assertFunctionOpen(functionId)
	local blockRecord = self:_block(blockId)
	assert(blockRecord["function"] == functionId, `block {blockId} is not owned by function {functionId}`)
	functionRecord.entry_block = blockId
end

function Builder:addParameter(functionId: number, valueType: Record?, nameHint: string?): number
	self:_assertMutable()
	local functionRecord = self:_assertFunctionOpen(functionId)
	local index = #functionRecord.parameters
	local valueId = self:_addValue(functionId, valueType, nameHint, LifterIR.Origin.parameter(index))
	table.insert(functionRecord.parameters, valueId)
	return valueId
end

function Builder:addVarargPack(functionId: number, evidence: IdArray?): number
	self:_assertMutable()
	local functionRecord = self:_assertFunctionOpen(functionId)
	assert(functionRecord.is_variadic == true, `function {functionId} is not variadic`)
	assert(functionRecord.vararg_pack == nil, `function {functionId} already has a vararg pack`)
	local packId = self:_addValuePack(functionId, LifterIR.PackOrigin.varargs(functionId), evidence)
	functionRecord.vararg_pack = packId
	return packId
end

function Builder:addValueCapture(
	functionId: number,
	valueType: Record?,
	nameHint: string?,
	evidence: IdArray?
): (number, number)
	self:_assertMutable()
	local functionRecord = self:_assertFunctionOpen(functionId)
	local captureId = #self.program.captures
	local valueId = self:_addValue(functionId, valueType, nameHint, LifterIR.Origin.capture(captureId))
	table.insert(self.program.captures, {
		id = captureId,
		["function"] = functionId,
		kind = LifterIR.CaptureKind.immutableValue(valueId),
		evidence = copyArray(evidence),
	})
	table.insert(functionRecord.captures, captureId)
	return valueId, captureId
end

function Builder:addLocalPlace(
	functionId: number,
	valueType: Record?,
	nameHint: string?,
	evidence: IdArray?
): number
	self:_assertMutable()
	local functionRecord = self:_assertFunctionOpen(functionId)
	local index = #functionRecord.local_places
	local placeId = self:_addPlace(functionId, valueType, nameHint, LifterIR.PlaceOrigin.localPlace(index), evidence)
	table.insert(functionRecord.local_places, placeId)
	return placeId
end

function Builder:addPlaceCapture(
	functionId: number,
	valueType: Record?,
	nameHint: string?,
	evidence: IdArray?
): (number, number)
	self:_assertMutable()
	local functionRecord = self:_assertFunctionOpen(functionId)
	local captureId = #self.program.captures
	local placeId = self:_addPlace(functionId, valueType, nameHint, LifterIR.PlaceOrigin.capture(captureId), evidence)
	table.insert(self.program.captures, {
		id = captureId,
		["function"] = functionId,
		kind = LifterIR.CaptureKind.sharedPlace(placeId),
		evidence = copyArray(evidence),
	})
	table.insert(functionRecord.captures, captureId)
	return placeId, captureId
end

function Builder:addBlockParameter(blockId: number, valueType: Record?, nameHint: string?): number
	self:_assertMutable()
	local blockRecord = self:_assertBlockOpen(blockId)
	local index = #blockRecord.parameters
	local valueId = self:_addValue(blockRecord["function"], valueType, nameHint, LifterIR.Origin.blockParameter(blockId, index))
	table.insert(blockRecord.parameters, valueId)
	return valueId
end

function Builder:refineBlockParameterType(valueId: number, valueType: Record)
	self:_assertMutable()
	local value = self:_value(valueId)
	assert(value.origin.block_parameter ~= nil, `value {valueId} is not a block parameter`)
	local parameter = value.origin.block_parameter :: { block: number, index: number }
	local block = self:_assertBlockOpen(parameter.block)
	assert(block.parameters[parameter.index + 1] == valueId, `value {valueId} is not block {parameter.block} parameter {parameter.index}`)
	assert(value.type.kind == "dynamic", `block parameter {valueId} already has a refined type`)
	assert(valueType.kind ~= "dynamic", `block parameter {valueId} refinement must add a concrete type`)
	value.type = valueType
end

function Builder:_appendInstruction(
	blockId: number,
	operation: Record,
	resultSpecs: { ResultSpec },
	options: InstructionOptions?,
	packResult: number?
): (number, IdArray)
	self:_assertMutable()
	local blockRecord = self:_assertBlockOpen(blockId)
	local source: InstructionOptions = options or ({} :: InstructionOptions)
	local instructionId = #self.program.instructions
	local resultIds: IdArray = newArray()

	for index, spec in resultSpecs do
		local valueId = self:_addValue(
			blockRecord["function"],
			spec.type,
			spec.name_hint,
			LifterIR.Origin.instructionResult(instructionId, index - 1)
		)
		table.insert(resultIds, valueId)
	end

	local record: Record = {
		id = instructionId,
		block = blockId,
		operation = operation,
		results = resultIds,
		effects = source.effects or LifterIR.Effects.unknown(),
		evidence = copyArray(source.evidence),
		claims = copyArray(source.claims),
	}
	if packResult ~= nil then
		record.pack_result = packResult
	end
	table.insert(self.program.instructions, record)
	table.insert(blockRecord.instructions, instructionId)
	return instructionId, resultIds
end

function Builder:addInstruction(
	blockId: number,
	operation: Record,
	resultSpecs: { ResultSpec },
	options: InstructionOptions?
): (number, IdArray)
	return self:_appendInstruction(blockId, operation, resultSpecs, options, nil)
end

function Builder:addValuePack(blockId: number, values: IdArray, options: InstructionOptions?): (number, number)
	self:_assertMutable()
	assert(#values > 0, "value pack construction must not be empty")
	local blockRecord = self:_assertBlockOpen(blockId)
	local valueTypes: RecordArray = newArray()
	for _, valueId in values do
		local value = self:_value(valueId)
		assert(value["function"] == blockRecord["function"], "value pack operand belongs to another function")
		table.insert(valueTypes, value.type)
	end
	local source: InstructionOptions = options or ({} :: InstructionOptions)
	local instructionId = #self.program.instructions
	local packId = self:_addValuePack(
		blockRecord["function"],
		LifterIR.PackOrigin.instructionResult(instructionId),
		source.evidence,
		LifterIR.PackShape.closed(valueTypes)
	)
	local actualOptions: InstructionOptions = {
		effects = source.effects or LifterIR.Effects.pure(),
		evidence = source.evidence,
		claims = source.claims,
	}
	local noResults: { ResultSpec } = newArray()
	local actualInstructionId, results = self:_appendInstruction(
		blockId,
		LifterIR.Operation.packValues(values),
		noResults,
		actualOptions,
		packId
	)
	assert(actualInstructionId == instructionId and #results == 0, "value pack allocation lost canonical order")
	return actualInstructionId, packId
end

function Builder:addAllocatedPlace(
	blockId: number,
	initialValue: number,
	valueType: Record?,
	nameHint: string?,
	evidence: IdArray?
): (number, number)
	self:_assertMutable()
	local blockRecord = self:_assertBlockOpen(blockId)
	local functionId = blockRecord["function"]
	local initial = self:_value(initialValue)
	assert(initial["function"] == functionId, "allocated place initializer belongs to another function")
	local instructionId = #self.program.instructions
	local placeId = self:_addPlace(
		functionId,
		valueType,
		nameHint,
		LifterIR.PlaceOrigin.instruction(instructionId),
		evidence
	)
	table.insert(self:_assertFunctionOpen(functionId).local_places, placeId)
	local actualInstructionId, results = self:_appendInstruction(
		blockId,
		LifterIR.Operation.placeWrite(placeId, initialValue),
		{},
		{ effects = LifterIR.Effects.placeWrite(), evidence = evidence },
		nil
	)
	assert(actualInstructionId == instructionId and #results == 0, "allocated place lost canonical instruction order")
	return placeId, instructionId
end

function Builder:addOpenCall(
	blockId: number,
	callee: number,
	arguments: IdArray,
	options: InstructionOptions?,
	argumentPack: number?
): (number, number)
	local source: InstructionOptions = options or ({} :: InstructionOptions)
	return self:_addOpenInvocation(
		blockId,
		LifterIR.Operation.call(callee, arguments, LifterIR.ResultArity.variadic(), argumentPack),
		source.result_pack_shape or LifterIR.PackShape.open(),
		options
	)
end

function Builder:addOpenNamecall(
	blockId: number,
	receiver: number,
	method: string,
	arguments: IdArray,
	options: InstructionOptions?,
	argumentPack: number?
): (number, number)
	local source: InstructionOptions = options or ({} :: InstructionOptions)
	return self:_addOpenInvocation(
		blockId,
		LifterIR.Operation.namecall(receiver, method, arguments, LifterIR.ResultArity.variadic(), argumentPack),
		source.result_pack_shape or LifterIR.PackShape.open(),
		options
	)
end

function Builder:addOpenProtectedCall(
	blockId: number,
	callee: number,
	errorHandler: number?,
	arguments: IdArray,
	options: InstructionOptions?,
	argumentPack: number?
): (number, number)
	local source: InstructionOptions = options or ({} :: InstructionOptions)
	return self:_addOpenInvocation(
		blockId,
		LifterIR.Operation.protectedCall(callee, errorHandler, arguments, LifterIR.ResultArity.variadic(), argumentPack),
		source.result_pack_shape or LifterIR.PackShape.open({ LifterIR.Types.boolean() }),
		options
	)
end

function Builder:addOpenCoroutineResume(
	blockId: number,
	thread: number,
	arguments: IdArray,
	options: InstructionOptions?,
	argumentPack: number?
): (number, number)
	local source: InstructionOptions = options or ({} :: InstructionOptions)
	return self:_addOpenInvocation(
		blockId,
		LifterIR.Operation.coroutineResume(thread, arguments, LifterIR.ResultArity.variadic(), argumentPack),
		source.result_pack_shape or LifterIR.PackShape.open({ LifterIR.Types.boolean() }),
		options
	)
end

function Builder:addOpenCoroutineYield(
	blockId: number,
	arguments: IdArray,
	options: InstructionOptions?,
	argumentPack: number?
): (number, number)
	local source: InstructionOptions = options or ({} :: InstructionOptions)
	return self:_addOpenInvocation(
		blockId,
		LifterIR.Operation.coroutineYield(arguments, LifterIR.ResultArity.variadic(), argumentPack),
		source.result_pack_shape or LifterIR.PackShape.open(),
		options
	)
end

function Builder:_addOpenInvocation(
	blockId: number,
	operation: Record,
	shape: Record,
	options: InstructionOptions?
): (number, number)
	self:_assertMutable()
	local blockRecord = self:_assertBlockOpen(blockId)
	local source: InstructionOptions = options or ({} :: InstructionOptions)
	local instructionId = #self.program.instructions
	local packId = self:_addValuePack(
		blockRecord["function"],
		LifterIR.PackOrigin.instructionResult(instructionId),
		source.evidence,
		shape
	)
	local noResults: { ResultSpec } = newArray()
	local actualInstructionId, resultIds = self:_appendInstruction(
		blockId,
		operation,
		noResults,
		options,
		packId
	)
	assert(actualInstructionId == instructionId and #resultIds == 0, "open invocation allocation lost canonical order")
	return actualInstructionId, packId
end

function Builder:addInstructionClaim(instructionId: number, claimId: number)
	self:_assertMutable()
	getEntity(self.program.claims, claimId, "claim")
	local claims = self:_instruction(instructionId).claims
	for _, existingClaimId in claims do
		assert(existingClaimId ~= claimId, `instruction {instructionId} already references claim {claimId}`)
	end
	table.insert(claims, claimId)
end

function Builder:addBlockEvidence(blockId: number, evidenceIds: IdArray)
	self:_assertMutable()
	local evidence = self:_assertBlockOpen(blockId).evidence
	for _, evidenceId in evidenceIds do
		getEntity(self.program.evidence, evidenceId, "evidence")
		if not table.find(evidence, evidenceId) then
			table.insert(evidence, evidenceId)
		end
	end
	table.sort(evidence)
end

function Builder:finalizeBlock(blockId: number, terminator: Record)
	self:_assertMutable()
	local blockRecord = self:_assertBlockOpen(blockId)
	blockRecord.terminator = terminator
	self._block_finalized[blockId + 1] = true
end

function Builder:finalizeFunction(functionId: number)
	self:_assertMutable()
	local functionRecord = self:_assertFunctionOpen(functionId)
	assert(#functionRecord.blocks > 0, `function {functionId} has no blocks`)
	assert(functionRecord.entry_block >= 0, `function {functionId} has no entry block`)
	local blockIds: { number } = functionRecord.blocks
	for _, blockId in blockIds do
		assert(self._block_finalized[blockId + 1], `function {functionId} contains unfinished block {blockId}`)
	end
	self._function_finalized[functionId + 1] = true
end

function Builder:addSolverTerm(sort: Record, operation: Record): number
	self:_assertMutable()
	local id = #self.program.solver_terms
	table.insert(self.program.solver_terms, { id = id, sort = sort, operation = operation })
	return id
end

function Builder:addConstraint(predicate: number, evidence: IdArray?, scope: Record?, pathRewrites: IdArray?): number
	self:_assertMutable()
	local id = #self.program.constraints
	table.insert(self.program.constraints, {
		id = id,
		predicate = predicate,
		evidence = copyArray(evidence),
		scope = scope or LifterIR.ConstraintScope.explicitOnly(),
		path_rewrites = copyArray(pathRewrites),
	})
	return id
end

function Builder:addQuery(kind: string, assumptions: IdArray, goal: number, pathRewrites: IdArray?): number
	self:_assertMutable()
	local id = #self.program.queries
	table.insert(self.program.queries, {
		id = id,
		kind = kind,
		assumptions = copyArray(assumptions),
		path_rewrites = copyArray(pathRewrites),
		goal = goal,
	})
	return id
end

function Builder:addSolverModel(query: number, bindings: RecordArray, evidence: IdArray?): number
	self:_assertMutable()
	local id = #self.program.solver_models
	table.insert(self.program.solver_models, {
		id = id,
		query = query,
		bindings = copyArray(bindings),
		evidence = copyArray(evidence),
	})
	return id
end

function Builder:addUnsatCore(query: number, constraints: IdArray, evidence: IdArray?): number
	self:_assertMutable()
	local id = #self.program.unsat_cores
	table.insert(self.program.unsat_cores, {
		id = id,
		query = query,
		constraints = copyArray(constraints),
		evidence = copyArray(evidence),
	})
	return id
end

function Builder:addCertificate(
	query: number,
	engine: string,
	resolution: string,
	evidence: IdArray?,
	certificateDigest: string?,
	model: number?,
	unsatCore: number?
): number
	self:_assertMutable()
	local id = #self.program.certificates
	local record: Record = {
		id = id,
		query = query,
		engine = engine,
		resolution = resolution,
		evidence = copyArray(evidence),
	}
	if certificateDigest ~= nil then
		record.certificate_digest = certificateDigest
	end
	if model ~= nil then
		record.model = model
	end
	if unsatCore ~= nil then
		record.unsat_core = unsatCore
	end
	table.insert(self.program.certificates, record)
	return id
end

function Builder:addClaim(
	subject: Record,
	predicate: number,
	status: string,
	requiredForEmission: boolean?,
	evidence: IdArray?,
	certificate: number?,
	purpose: Record?,
	query: number?
): number
	self:_assertMutable()
	local id = #self.program.claims
	local record: Record = {
		id = id,
		subject = subject,
		predicate = predicate,
		purpose = purpose or LifterIR.ClaimPurpose.genericPredicate(),
		status = status,
		required_for_emission = requiredForEmission == true,
		evidence = copyArray(evidence),
	}
	if certificate ~= nil then
		record.certificate = certificate
	end
	if query ~= nil then
		record.query = query
	end
	table.insert(self.program.claims, record)
	return id
end

function Builder:addObligation(
	kind: string,
	subject: Record,
	status: string,
	blocksProfile: string,
	detail: string,
	query: number?,
	certificate: number?,
	evidence: IdArray?
): number
	self:_assertMutable()
	assert(containsValue(LifterIR.ObligationKind, kind), `unknown obligation kind {kind}`)
	assert(containsValue(LifterIR.ObligationStatus, status), `unknown obligation status {status}`)
	assert(containsValue(LifterIR.AdmissionProfile, blocksProfile), `unknown admission profile {blocksProfile}`)
	assert(detail ~= "", "obligation detail must not be empty")
	local id = #self.program.obligations
	local record: Record = {
		id = id,
		kind = kind,
		subject = subject,
		status = status,
		blocks_profile = blocksProfile,
		detail = detail,
		evidence = copyArray(evidence),
	}
	if query ~= nil then
		local queryRecord = self.program.queries[query + 1]
		assert(queryRecord ~= nil and queryRecord.id == query, `invalid obligation query {query}`)
		record.requirement = {
			kind = queryRecord.kind,
			predicate = queryRecord.goal,
		}
		record.query = query
	end
	if certificate ~= nil then
		record.certificate = certificate
	end
	table.insert(self.program.obligations, record)
	return id
end

function Builder:finish(): Record
	self:_assertMutable()
	assert(type(self.program.entry_function) == "number", "entry function is not set")
	local entry = self:_function(self.program.entry_function)
	assert(
		#self.program.entry_bindings == #entry.captures,
		"entry capture and external binding counts differ"
	)
	local usedExternalBindings: { boolean } = newArray()
	for index, captureId in entry.captures do
		local capture = self:_capture(captureId)
		local bindingId: number = self.program.entry_bindings[index]
		local binding = self:_externalBinding(bindingId)
		local captureIsValue = capture.kind.immutable_value ~= nil
		local expectedKind = if captureIsValue
			then LifterIR.ExternalBindingKind.immutableValue
			else LifterIR.ExternalBindingKind.sharedPlace
		assert(binding.kind == expectedKind, `entry capture {captureId} has the wrong external binding kind`)
		usedExternalBindings[bindingId + 1] = true
	end
	for index in self.program.external_bindings do
		assert(usedExternalBindings[index] == true, `external binding {index - 1} is not used by the entry closure`)
	end
	for index, finalized in self._block_finalized do
		assert(finalized, `block {index - 1} is not finalized`)
	end
	for index, finalized in self._function_finalized do
		assert(finalized, `function {index - 1} is not finalized`)
	end
	self._finished = true
	return self.program
end

LifterIR.Builder = Builder

return table.freeze(LifterIR)
