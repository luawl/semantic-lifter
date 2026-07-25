--!strict

-- Matches authenticated origins against their exact source expression shape.
-- Invocation, return, and snapshot traversal belong to target_origin_matcher.

local InvocationFrame = require("./invocation_frame")

local TargetOriginExpressionMatcher = {}

type Record = InvocationFrame.Record
export type LocalMatcher = (Record, Record) -> boolean

local unwrapExpression = InvocationFrame.unwrapExpression

local function matchesValueOrigin(value: any, origin: Record, matchesLocal: LocalMatcher): boolean
	local expression = unwrapExpression(value, "target value origin expression")
	if origin.kind == "local_value" or origin.kind == "local_place" then
		return matchesLocal(expression, origin)
	elseif origin.kind == "environment" then
		return expression.type == "AstExprGlobal" and expression.global == origin.name
	end
	return false
end

local function matchesAccessKey(value: any, origin: Record, matchesLocal: LocalMatcher): boolean
	local expression = unwrapExpression(value, "target access key expression")
	if origin.kind == "source_expression" then
		return expression == origin.expression
	elseif origin.kind == "constant_string" then
		return expression.type == "AstExprConstantString" and expression.value == origin.value
	elseif origin.kind == "constant_boolean" then
		return expression.type == "AstExprConstantBool" and expression.value == origin.value
	elseif origin.kind == "constant_number" then
		local sourceValue = expression.value
		if expression.type == "AstExprConstantNumber" and type(sourceValue) == "number" then
			return sourceValue == origin.value
		elseif expression.type == "AstExprConstantInteger" then
			if type(sourceValue) == "number" then
				return sourceValue == origin.value
			elseif type(sourceValue) == "string" then
				return tonumber(sourceValue) == origin.value
			end
		end
		return false
	end
	return matchesValueOrigin(expression, origin, matchesLocal)
end

local function matchesIndexedAccess(
	value: any,
	tableOrigin: Record,
	keyOrigin: Record,
	matchesLocal: LocalMatcher
): boolean
	local expression = unwrapExpression(value, "target table access expression")
	if expression.type == "AstExprIndexName" then
		return keyOrigin.kind == "constant_string"
			and expression.index == keyOrigin.value
			and matchesValueOrigin(expression.expr, tableOrigin, matchesLocal)
	elseif expression.type == "AstExprIndexExpr" then
		return matchesValueOrigin(expression.expr, tableOrigin, matchesLocal)
			and matchesAccessKey(expression.index, keyOrigin, matchesLocal)
	end
	return false
end

local function matchesAccessPathAt(value: any, origin: Record, keyIndex: number, matchesLocal: LocalMatcher): boolean
	if keyIndex == 0 then
		return matchesValueOrigin(value, origin.root_origin, matchesLocal)
	end
	local expression = unwrapExpression(value, "target access path expression")
	local keyOrigin = origin.key_origins[keyIndex]
	if type(keyOrigin) ~= "table" then
		return false
	elseif expression.type == "AstExprIndexName" then
		return keyOrigin.kind == "constant_string"
			and expression.index == keyOrigin.value
			and matchesAccessPathAt(expression.expr, origin, keyIndex - 1, matchesLocal)
	elseif expression.type == "AstExprIndexExpr" then
		return matchesAccessPathAt(expression.expr, origin, keyIndex - 1, matchesLocal)
			and matchesAccessKey(expression.index, keyOrigin, matchesLocal)
	end
	return false
end

local function intrinsicPath(value: any): string?
	local expression = unwrapExpression(value, "target intrinsic expression")
	if expression.type == "AstExprGlobal" and type(expression.global) == "string" then
		return expression.global
	elseif expression.type == "AstExprIndexName" and type(expression.index) == "string" then
		local receiver = unwrapExpression(expression.expr, "target intrinsic receiver")
		if receiver.type == "AstExprGlobal" and type(receiver.global) == "string" then
			return receiver.global .. "." .. expression.index
		end
	end
	return nil
end

function TargetOriginExpressionMatcher.matchesDirect(
	value: any,
	origin: Record,
	matchesLocal: LocalMatcher
): boolean
	if origin.kind == "intrinsic" then
		return intrinsicPath(value) == origin.path
	elseif origin.kind == "closure_value" then
		local expression = unwrapExpression(value, "target closure origin expression")
		return expression.type == "AstExprFunction" and expression == origin.expression
	elseif origin.kind == "local_value" or origin.kind == "local_place" or origin.kind == "environment" then
		return matchesValueOrigin(value, origin, matchesLocal)
	elseif origin.kind == "table_get" then
		return matchesIndexedAccess(value, origin.table_origin, origin.key_origin, matchesLocal)
	elseif origin.kind == "access_path" and type(origin.key_origins) == "table" then
		return matchesAccessPathAt(value, origin, #origin.key_origins, matchesLocal)
	end
	return false
end

return table.freeze(TargetOriginExpressionMatcher)
