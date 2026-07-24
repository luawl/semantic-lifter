--!strict

-- Pure scalar validation and normalization shared by AST admission and
-- expression lowering.

local AstExpressionScalar = {}

type Record = { [string]: any }

export type Problem = {
	code: string,
	node: Record,
	detail: string,
}

export type IntegerValue = {
	decimal: string,
	wide: boolean,
	signed: boolean,
}

export type InterpolationValue = {
	segments: { string },
	expressions: { any },
}

export type SpecialNumberName = "nan" | "positive_infinity" | "negative_infinity"

local binaryOperators: { [string]: string } = table.freeze({
	Add = "add",
	Sub = "subtract",
	Mul = "multiply",
	Div = "divide",
	FloorDiv = "floor_divide",
	Mod = "modulo",
	Pow = "power",
	Concat = "concat",
	CompareEq = "equal",
	CompareNe = "not_equal",
	CompareLt = "less",
	CompareLe = "less_equal",
	CompareGt = "greater",
	CompareGe = "greater_equal",
})

local unaryOperators: { [string]: string } = table.freeze({
	Not = "logical_not",
	Minus = "negate",
	Len = "length",
})

local function problem(code: string, node: Record, detail: string): Problem
	return { code = code, node = node, detail = detail }
end

local function optionalBoolean(node: Record, field: string, code: string, detail: string): (boolean?, Problem?)
	local value = node[field]
	if value == nil then
		return false, nil
	elseif type(value) ~= "boolean" then
		return nil, problem(code, node, detail)
	end
	return value, nil
end

function AstExpressionScalar.binaryOperator(value: any): string?
	return if type(value) == "string" then binaryOperators[value] else nil
end

function AstExpressionScalar.unaryOperator(value: any): string?
	return if type(value) == "string" then unaryOperators[value] else nil
end

function AstExpressionScalar.booleanValue(node: Record): (boolean?, Problem?)
	if type(node.value) ~= "boolean" then
		return nil, problem("malformed_boolean_literal", node, "boolean literal has no Boolean value")
	end
	return node.value, nil
end

function AstExpressionScalar.numberValue(node: Record): (number?, Problem?)
	if type(node.value) ~= "number" then
		return nil, problem("malformed_number_literal", node, "number literal has no numeric value")
	end
	return node.value, nil
end

function AstExpressionScalar.specialNumberName(value: number): SpecialNumberName?
	if value ~= value then
		return "nan"
	elseif value == math.huge then
		return "positive_infinity"
	elseif value == -math.huge then
		return "negative_infinity"
	end
	return nil
end

function AstExpressionScalar.integerValue(node: Record): (IntegerValue?, Problem?)
	local value = node.value
	if type(value) == "string" then
		local digits = value
		if string.sub(digits, 1, 1) == "-" then
			digits = string.sub(digits, 2)
		end
		if digits == ""
			or string.match(digits, "^%d+$") == nil
			or (#digits > 1 and string.sub(digits, 1, 1) == "0")
			or value == "-0"
		then
			return nil, problem("malformed_integer_literal", node, "integer literal is not canonical signed decimal")
		end
		return { decimal = value, wide = true, signed = string.sub(value, 1, 1) == "-" }, nil
	elseif type(value) == "number" and value % 1 == 0 and math.abs(value) <= 9007199254740991 then
		return { decimal = string.format("%.0f", value), wide = false, signed = value < 0 }, nil
	end
	return nil, problem("malformed_integer_literal", node, "integer literal has no exact numeric value")
end

function AstExpressionScalar.stringValue(node: Record): (string?, Problem?)
	if type(node.value) ~= "string" then
		return nil, problem("malformed_string_literal", node, "string literal has no string value")
	end
	return node.value, nil
end

function AstExpressionScalar.globalName(node: Record): (string?, Problem?)
	if type(node.global) ~= "string" or node.global == "" then
		return nil, problem("malformed_global_expression", node, "global expression has no name")
	end
	return node.global, nil
end

function AstExpressionScalar.indexName(node: Record): (string?, Problem?)
	if type(node.index) ~= "string" or node.index == "" then
		return nil, problem("malformed_index_name", node, "named index is missing its field name")
	end
	return node.index, nil
end

function AstExpressionScalar.functionIsVariadic(node: Record): (boolean?, Problem?)
	return optionalBoolean(node, "vararg", "malformed_function", "function vararg flag is not Boolean")
end

function AstExpressionScalar.callUsesSelf(node: Record): (boolean?, Problem?)
	return optionalBoolean(node, "self", "malformed_call", "call self flag is not Boolean")
end

function AstExpressionScalar.callMethodName(node: Record): (string?, Problem?)
	local usesSelf, flagProblem = AstExpressionScalar.callUsesSelf(node)
	if flagProblem ~= nil then
		return nil, flagProblem
	elseif not usesSelf then
		return nil, nil
	end
	local functionValue = node.func
	if type(functionValue) ~= "table" or functionValue.type ~= "AstExprIndexName" then
		return nil, problem(
			"malformed_method_call",
			node,
			"method call callee does not have a static colon-dispatch name"
		)
	end
	if type(functionValue.index) ~= "string" or functionValue.index == "" then
		return nil, problem("malformed_method_call", node, "method call has no static dispatch name")
	end
	return functionValue.index, nil
end

function AstExpressionScalar.interpolationValue(node: Record): (InterpolationValue?, Problem?)
	if type(node.strings) ~= "table" then
		return nil, problem("malformed_ast", node, "expected array field strings")
	end
	if type(node.expressions) ~= "table" then
		return nil, problem("malformed_ast", node, "expected array field expressions")
	end
	local expressions = node.expressions :: { any }
	local segmentValues = node.strings :: { any }
	if #segmentValues ~= #expressions + 1 then
		return nil, problem("malformed_interpolation", node, "interpolation segment/value arity is inconsistent")
	end
	local segments: { string } = {}
	for _, segment in segmentValues do
		if type(segment) ~= "string" then
			return nil, problem("malformed_interpolation", node, "interpolation segment is not a string")
		end
		table.insert(segments, segment)
	end
	return { segments = segments, expressions = expressions }, nil
end

function AstExpressionScalar.compoundOperatorName(node: Record): (string?, Problem?)
	if type(node.op) ~= "string" then
		return nil, problem("malformed_compound_assignment", node, "compound assignment is missing its operator")
	end
	return node.op, nil
end

function AstExpressionScalar.binaryOperatorProblem(node: Record, value: any, compound: boolean): Problem?
	if compound and (value == "And" or value == "Or") then
		return problem(
			"unsupported_compound_short_circuit",
			node,
			"compound assignment cannot use a short-circuit operator"
		)
	end
	if value ~= "And" and value ~= "Or" and AstExpressionScalar.binaryOperator(value) == nil then
		return problem("unsupported_binary_operator", node, `binary operator {tostring(value)} is not mapped`)
	end
	return nil
end

function AstExpressionScalar.validatePreorder(node: Record): Problem?
	if node.type == "AstExprConstantBool" then
		local _, valueProblem = AstExpressionScalar.booleanValue(node)
		return valueProblem
	elseif node.type == "AstExprConstantNumber" then
		local _, valueProblem = AstExpressionScalar.numberValue(node)
		return valueProblem
	elseif node.type == "AstExprConstantInteger" then
		local _, valueProblem = AstExpressionScalar.integerValue(node)
		return valueProblem
	elseif node.type == "AstExprConstantString" then
		local _, valueProblem = AstExpressionScalar.stringValue(node)
		return valueProblem
	elseif node.type == "AstExprGlobal" then
		local _, valueProblem = AstExpressionScalar.globalName(node)
		return valueProblem
	elseif node.type == "AstExprIndexName" then
		local _, valueProblem = AstExpressionScalar.indexName(node)
		return valueProblem
	elseif node.type == "AstExprFunction" then
		local _, valueProblem = AstExpressionScalar.functionIsVariadic(node)
		return valueProblem
	elseif node.type == "AstExprCall" then
		local _, valueProblem = AstExpressionScalar.callMethodName(node)
		return valueProblem
	elseif node.type == "AstExprInterpString" then
		local _, valueProblem = AstExpressionScalar.interpolationValue(node)
		return valueProblem
	elseif node.type == "AstExprUnary" and AstExpressionScalar.unaryOperator(node.op) == nil then
		return problem("unsupported_unary_operator", node, `unary operator {tostring(node.op)} is not mapped`)
	elseif node.type == "AstStatCompoundAssign" then
		local _, valueProblem = AstExpressionScalar.compoundOperatorName(node)
		return valueProblem
	end
	return nil
end

function AstExpressionScalar.validatePostorder(node: Record): Problem?
	if node.type == "AstExprBinary" then
		return AstExpressionScalar.binaryOperatorProblem(node, node.op, false)
	elseif node.type == "AstStatCompoundAssign" and type(node.op) == "string" then
		return AstExpressionScalar.binaryOperatorProblem(node, node.op, true)
	end
	return nil
end

return table.freeze(AstExpressionScalar)
