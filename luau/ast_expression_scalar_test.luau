--!strict

local AstExpressionScalar = require("./ast_expression_scalar")
local AstFrontend = require("./ast_frontend")
local LifterIR = require("./lifter_ir")

type Case = {
	statement: any,
	code: string,
	label: string,
	location: string?,
}

type IntegerCase = {
	value: any,
	decimal: string,
	wide: boolean,
	signed: boolean,
}

local function deadStatement(statement: any): any
	return {
		root = {
			type = "AstStatBlock",
			body = ({ { type = "AstStatReturn", list = {} }, statement } :: { any }),
		},
	}
end

local function deadExpression(expression: any): any
	return deadStatement({ type = "AstStatReturn", list = ({ expression } :: { any }) })
end

local function expectProblem(case: Case)
	local document = deadStatement(case.statement)
	local result = AstFrontend.tryLift(document, { program_id = case.label, source_name = case.label })
	assert(result.program == nil and #result.diagnostics == 1, `{case.label} did not reject at the frontend boundary`)
	assert(result.diagnostics[1].code == case.code, `{case.label} changed frontend diagnostic code`)
	if case.location ~= nil then
		assert(result.diagnostics[1].location == case.location, `{case.label} lost its source location`)
	end
end

local malformedCases: { Case } = {
	{
		statement = { type = "AstStatReturn", list = { { type = "AstExprConstantBool", value = "true", location = "scalar-bool" } } },
		code = "malformed_boolean_literal",
		label = "dead-boolean-payload-admission",
		location = "scalar-bool",
	},
	{
		statement = { type = "AstStatReturn", list = { { type = "AstExprConstantNumber", value = "1" } } },
		code = "malformed_number_literal",
		label = "dead-number-payload-admission",
	},
	{
		statement = { type = "AstStatReturn", list = { { type = "AstExprConstantInteger", value = "01" } } },
		code = "malformed_integer_literal",
		label = "dead-integer-payload-admission",
	},
	{
		statement = { type = "AstStatReturn", list = { { type = "AstExprConstantString", value = false } } },
		code = "malformed_string_literal",
		label = "dead-string-payload-admission",
	},
	{
		statement = { type = "AstStatReturn", list = { { type = "AstExprGlobal", global = "" } } },
		code = "malformed_global_expression",
		label = "dead-global-name-admission",
	},
	{
		statement = { type = "AstStatReturn", list = { {
			type = "AstExprIndexName",
			expr = { type = "AstExprGlobal", global = "tableValue" },
		} } },
		code = "malformed_index_name",
		label = "dead-index-name-admission",
	},
	{
		statement = { type = "AstStatReturn", list = { {
			type = "AstExprUnary",
			op = "Unsupported",
			expr = { type = "AstExprConstantInteger", value = 1 },
		} } },
		code = "unsupported_unary_operator",
		label = "dead-unary-operator-admission",
	},
	{
		statement = { type = "AstStatReturn", list = { {
			type = "AstExprBinary",
			op = "Unsupported",
			left = { type = "AstExprConstantInteger", value = 1 },
			right = { type = "AstExprConstantInteger", value = 2 },
		} } },
		code = "unsupported_binary_operator",
		label = "dead-binary-operator-admission",
	},
	{
		statement = { type = "AstStatReturn", list = { { type = "AstExprInterpString", expressions = {} } } },
		code = "malformed_ast",
		label = "dead-interpolation-segments-admission",
	},
	{
		statement = { type = "AstStatReturn", list = { {
			type = "AstExprInterpString",
			strings = ({ "value: ", false } :: { any }),
			expressions = { { type = "AstExprConstantInteger", value = 1 } },
		} } },
		code = "malformed_interpolation",
		label = "dead-interpolation-segment-admission",
	},
	{
		statement = { type = "AstStatReturn", list = { {
			type = "AstExprInterpString",
			strings = { "value: " },
			expressions = { { type = "AstExprConstantInteger", value = 1 } },
		} } },
		code = "malformed_interpolation",
		label = "dead-interpolation-arity-admission",
	},
	{
		statement = {
			type = "AstStatCompoundAssign",
			var = { type = "AstExprGlobal", global = "value" },
			value = { type = "AstExprConstantInteger", value = 1 },
		},
		code = "malformed_compound_assignment",
		label = "dead-compound-operator-shape-admission",
	},
	{
		statement = {
			type = "AstStatCompoundAssign",
			op = "Unsupported",
			var = { type = "AstExprGlobal", global = "value" },
			value = { type = "AstExprConstantInteger", value = 1 },
		},
		code = "unsupported_binary_operator",
		label = "dead-compound-operator-admission",
	},
	{
		statement = {
			type = "AstStatCompoundAssign",
			op = "And",
			var = { type = "AstExprGlobal", global = "value" },
			value = { type = "AstExprConstantInteger", value = 1 },
		},
		code = "unsupported_compound_short_circuit",
		label = "dead-compound-short-circuit-admission",
	},
}

for _, case in malformedCases do
	expectProblem(case)
end

local parserError = { type = "AstExprError", location = "scalar-parser-error" }
expectProblem({
	statement = {
		type = "AstStatReturn",
		list = { { type = "AstExprUnary", op = "Unsupported", expr = parserError } },
	},
	code = "unsupported_unary_operator",
	label = "unary-operator-preorder-admission",
})
expectProblem({
	statement = {
		type = "AstStatReturn",
		list = { {
			type = "AstExprBinary",
			op = "Unsupported",
			left = parserError,
			right = { type = "AstExprConstantInteger", value = 1 },
		} },
	},
	code = "malformed_source_expression",
	label = "binary-operator-postorder-admission",
})
expectProblem({
	statement = {
		type = "AstStatCompoundAssign",
		op = "Unsupported",
		var = { type = "AstExprGlobal", global = "value" },
		value = parserError,
	},
	code = "malformed_source_expression",
	label = "compound-operator-postorder-admission",
})

local integerCases: { IntegerCase } = {
	{ value = 1, decimal = "1", wide = false, signed = false },
	{ value = "0", decimal = "0", wide = true, signed = false },
	{ value = "-1", decimal = "-1", wide = true, signed = true },
	{ value = "18446744073709551615", decimal = "18446744073709551615", wide = true, signed = false },
}
for _, integerCase in integerCases do
	local integerValue, integerProblem = AstExpressionScalar.integerValue({
		type = "AstExprConstantInteger",
		value = integerCase.value,
	})
	assert(integerProblem == nil and integerValue ~= nil, "canonical integer scalar was rejected")
	local normalized = integerValue :: AstExpressionScalar.IntegerValue
	assert(
		normalized.decimal == integerCase.decimal
			and normalized.wide == integerCase.wide
			and normalized.signed == integerCase.signed,
		"integer scalar normalization changed"
	)
end

local specialNumberCases = {
	{ label = "nan", value = 0 / 0 },
	{ label = "positive_infinity", value = math.huge },
	{ label = "negative_infinity", value = -math.huge },
}
local specialNumberFailures = {}
for _, case in specialNumberCases do
	local label = `special-number-{case.label}`
	local result = AstFrontend.tryLift({ root = {
		type = "AstStatBlock",
		body = { { type = "AstStatReturn", list = { { type = "AstExprConstantNumber", value = case.value } } } },
	} }, { program_id = label, source_name = label })
	local operation = if result.program == nil then nil else (result.program :: any).instructions[1].operation.constant
	local encoded = if result.program == nil then false else pcall(LifterIR.encodeJson, result.program)
	if result.program == nil
		or #result.diagnostics ~= 0
		or AstExpressionScalar.specialNumberName(case.value) ~= case.label
		or operation.special_number ~= case.label
		or not encoded
	then
		table.insert(specialNumberFailures, label)
	end
end
assert(#specialNumberFailures == 0, `special number lowering mismatches: {table.concat(specialNumberFailures, ", ")}`)
for _, finiteNumber in { 0, -0.0, 1.5 } do
	assert(AstExpressionScalar.specialNumberName(finiteNumber) == nil, "finite number was classified as special")
end
local negativeZeroResult = AstFrontend.tryLift({ root = {
	type = "AstStatBlock",
	body = { { type = "AstStatReturn", list = { { type = "AstExprConstantNumber", value = -0.0 } } } },
} }, { program_id = "negative-zero-number", source_name = "negative-zero-number" })
assert(negativeZeroResult.program ~= nil and #negativeZeroResult.diagnostics == 0, "negative zero did not lower")
local negativeZeroLiteral = (negativeZeroResult.program :: any).instructions[1].operation.constant.number
assert(negativeZeroLiteral == 0 and 1 / negativeZeroLiteral == -math.huge, "negative zero lost its sign")
assert(pcall(LifterIR.encodeJson, negativeZeroResult.program), "negative zero did not encode as JSON")

local arbitraryByte = string.char(0xff)
local arbitraryByteResult = AstFrontend.tryLift({ root = {
	type = "AstStatBlock",
	body = { { type = "AstStatReturn", list = { { type = "AstExprConstantString", value = arbitraryByte } } } },
} }, { program_id = "arbitrary-byte-string", source_name = "arbitrary-byte-string" })
assert(arbitraryByteResult.program ~= nil and #arbitraryByteResult.diagnostics == 0, "arbitrary byte string did not lower")
local arbitraryByteLiteral = (arbitraryByteResult.program :: any).instructions[1].operation.constant.string_bytes
assert(arbitraryByteLiteral == "ff", "arbitrary byte string did not use canonical transport")
local arbitraryByteJson = LifterIR.encodeJson(arbitraryByteResult.program)
assert(utf8.len(arbitraryByteJson) ~= nil, "arbitrary byte string produced invalid UTF-8 JSON")
assert(string.find(arbitraryByteJson, '"string_bytes":"ff"', 1, true) ~= nil, "arbitrary byte transport was not serialized")
assert(not pcall(LifterIR.encodeJson, { invalid_text = arbitraryByte }), "JSON codec admitted invalid UTF-8 text")

local arbitrarySegmentResult = AstFrontend.tryLift({ root = {
	type = "AstStatBlock",
	body = { { type = "AstStatReturn", list = { {
		type = "AstExprInterpString",
		strings = { arbitraryByte, "" },
		expressions = { { type = "AstExprConstantInteger", value = 1 } },
	} } } },
} }, { program_id = "arbitrary-byte-interpolation", source_name = "arbitrary-byte-interpolation" })
assert(arbitrarySegmentResult.program ~= nil and #arbitrarySegmentResult.diagnostics == 0, "arbitrary interpolation byte did not lower")
local arbitrarySegment: any = nil
for _, instruction in (arbitrarySegmentResult.program :: any).instructions do
	if instruction.operation.string_interpolate ~= nil then
		arbitrarySegment = instruction.operation.string_interpolate.segments[1]
	end
end
assert(arbitrarySegment ~= nil and arbitrarySegment.string_bytes == "ff", "interpolation byte did not use canonical transport")
assert(utf8.len(LifterIR.encodeJson(arbitrarySegmentResult.program)) ~= nil, "interpolation byte produced invalid UTF-8 JSON")

for _, text in { "\0", utf8.char(0xe9) } do
	local literal = LifterIR.Literal.string(text)
	assert(literal.string == text and literal.string_bytes == nil, "valid UTF-8 string used byte transport")
	assert(utf8.len(LifterIR.encodeJson(literal)) ~= nil, "valid UTF-8 string produced invalid JSON")
end

local validInterpolation = AstFrontend.tryLift(deadExpression({
	type = "AstExprInterpString",
	strings = { "value: ", "" },
	expressions = { { type = "AstExprConstantInteger", value = 1 } },
}), { program_id = "valid-dead-interpolation", source_name = "valid-dead-interpolation" })
assert(validInterpolation.program ~= nil and #validInterpolation.diagnostics == 0, "valid dead interpolation was rejected")

local function sourceDocument(statement: any): any
	return { root = { type = "AstStatBlock", body = ({ statement } :: { any }) } }
end

local function functionWithVararg(value: any, present: boolean): any
	local expression: any = {
		type = "AstExprFunction",
		location = "runtime-function-flag",
		args = {},
		body = { type = "AstStatBlock", body = {} },
	}
	if present then
		expression.vararg = value
	end
	return { type = "AstStatReturn", list = { expression } }
end

local function callWithSelf(value: any, present: boolean): any
	local callee: any = { type = "AstExprGlobal", global = "callee" }
	if value == true then
		callee = {
			type = "AstExprIndexName",
			expr = { type = "AstExprGlobal", global = "receiver" },
			index = "method",
		}
	end
	local expression: any = {
		type = "AstExprCall",
		location = "runtime-call-flag",
		func = callee,
		args = {},
	}
	if present then
		expression.self = value
	end
	return { type = "AstStatExpr", expr = expression }
end

local malformedFlagCases = {
	{
		label = "function-vararg-flag",
		code = "malformed_function",
		location = "runtime-function-flag",
		statement = functionWithVararg("true", true),
	},
	{
		label = "call-self-flag",
		code = "malformed_call",
		location = "runtime-call-flag",
		statement = callWithSelf("true", true),
	},
}
local malformedFlagFailures = {}
for _, case in malformedFlagCases do
	for _, dead in { false, true } do
		local document = if dead then deadStatement(case.statement) else sourceDocument(case.statement)
		local label = `{if dead then "dead" else "reachable"}-{case.label}-admission`
		local result = AstFrontend.tryLift(document, { program_id = label, source_name = label })
		if result.program ~= nil
			or #result.diagnostics ~= 1
			or result.diagnostics[1].code ~= case.code
			or result.diagnostics[1].location ~= case.location
		then
			table.insert(malformedFlagFailures, label)
		end
	end
end
assert(#malformedFlagFailures == 0, `runtime flag admission mismatches: {table.concat(malformedFlagFailures, ", ")}`)

for _, variant in {
	{ label = "absent", value = false, present = false },
	{ label = "false", value = false, present = true },
	{ label = "true", value = true, present = true },
} do
	for _, statement in { functionWithVararg(variant.value, variant.present), callWithSelf(variant.value, variant.present) } do
		local label = `valid-runtime-flag-{variant.label}`
		local result = AstFrontend.tryLift(sourceDocument(statement), { program_id = label, source_name = label })
		assert(result.program ~= nil and #result.diagnostics == 0, `{label} was rejected`)
	end
end

local malformedMethodCases: { { label: string, statement: any } } = {
	{
		label = "method-callee-shape",
		statement = { type = "AstStatExpr", expr = {
			type = "AstExprCall",
			location = "method-callee-shape",
			self = true,
			func = { type = "AstExprGlobal", global = "callee" },
			args = {},
		} },
	},
	{
		label = "method-name-shape",
		statement = { type = "AstStatExpr", expr = {
			type = "AstExprCall",
			location = "method-name-shape",
			self = true,
			func = {
				type = "AstExprIndexName",
				expr = { type = "AstExprGlobal", global = "receiver" },
				index = "",
			},
			args = {},
		} },
	},
}
local malformedMethodFailures = {}
for _, case in malformedMethodCases do
	for _, dead in { false, true } do
		local methodDocument = if dead then deadStatement(case.statement) else sourceDocument(case.statement)
		local label = `{if dead then "dead" else "reachable"}-{case.label}-admission`
		local result = AstFrontend.tryLift(methodDocument, { program_id = label, source_name = label })
		if result.program ~= nil
			or #result.diagnostics ~= 1
			or result.diagnostics[1].code ~= "malformed_method_call"
			or result.diagnostics[1].location ~= case.label
		then
			table.insert(malformedMethodFailures, label)
		end
	end
end
assert(#malformedMethodFailures == 0, `method-call shape mismatches: {table.concat(malformedMethodFailures, ", ")}`)

local malformedMethodReceiver = { type = "AstStatExpr", expr = {
	type = "AstExprCall",
	location = "method-receiver-call",
	self = true,
	func = {
		type = "AstExprIndexName",
		expr = { type = "AstExprError", location = "method-receiver-error" },
		index = "method",
	},
	args = {},
} }
for _, methodDocument in { sourceDocument(malformedMethodReceiver), deadStatement(malformedMethodReceiver) } do
	local result = AstFrontend.tryLift(methodDocument, {
		program_id = "method-receiver-diagnostic-order",
		source_name = "method-receiver-diagnostic-order",
	})
	assert(result.program == nil and #result.diagnostics == 1, "malformed method receiver did not reject")
	assert(result.diagnostics[1].code == "malformed_source_expression", "method receiver diagnostic code changed")
	assert(result.diagnostics[1].location == "method-receiver-error", "method receiver diagnostic location changed")
end

return true
