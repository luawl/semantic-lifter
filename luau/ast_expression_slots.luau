--!strict

-- Runtime-expression slots consumed by the current source frontend. This map
-- classifies only existing children; complete per-node field schemas remain a
-- separate admission concern.

local AstExpressionSlots = {}

type Record = { [string]: any }

export type Kind = "expression" | "expression_array" | "table_item_array" | "table_item"
export type Surface = "assignment_target" | "call_statement" | "function_statement_target"

export type Role = {
	kind: Kind,
	code: string,
	detail: string,
	exact_tag: string?,
	exact_tag_detail: string?,
	member_code: string?,
	member_detail: string?,
	missing_owner: boolean?,
	surface: Surface?,
	member_surface: Surface?,
}

export type Problem = {
	code: string,
	node: Record?,
	detail: string,
}

local function expression(code: string, detail: string, missingOwner: boolean?, surface: Surface?): Role
	return { kind = "expression", code = code, detail = detail, missing_owner = missingOwner, surface = surface }
end

local function exactExpression(code: string, detail: string, exactTag: string, exactTagDetail: string): Role
	local role = expression(code, detail)
	role.exact_tag = exactTag
	role.exact_tag_detail = exactTagDetail
	return role
end

local function expressionArray(field: string, memberCode: string, memberDetail: string, memberSurface: Surface?): Role
	return {
		kind = "expression_array",
		code = "malformed_ast",
		detail = `expected array field {field}`,
		member_code = memberCode,
		member_detail = memberDetail,
		missing_owner = true,
		member_surface = memberSurface,
	}
end

local directSlots: { [string]: { [string]: Role } } = {
	AstStatLocalFunction = {
		func = exactExpression(
			"malformed_local_function",
			"local function is missing its function expression",
			"AstExprFunction",
			"local function value is not a function expression"
		),
	},
	AstStatFunction = {
		name = expression(
			"malformed_function_statement",
			"function statement is missing its assignment target",
			nil,
			"function_statement_target"
		),
		func = exactExpression(
			"malformed_function_statement",
			"function statement is missing its function expression",
			"AstExprFunction",
			"function statement value is not a function expression"
		),
	},
	AstStatCompoundAssign = {
		var = expression(
			"malformed_compound_assignment",
			"compound assignment is missing its target",
			nil,
			"assignment_target"
		),
		value = expression("malformed_compound_assignment", "compound assignment is missing its value"),
	},
	AstStatIf = { condition = expression("malformed_if", "if statement is missing its condition") },
	AstStatWhile = { condition = expression("malformed_while", "while statement is missing its condition") },
	AstStatRepeat = { condition = expression("malformed_repeat", "repeat statement is missing its condition") },
	AstStatFor = {
		from = expression("malformed_numeric_for", "numeric for is missing its initial value", true),
		to = expression("malformed_numeric_for", "numeric for is missing its limit", true),
		step = expression("malformed_numeric_for", "numeric for step is not an AST expression"),
	},
	AstStatExpr = {
		expr = expression(
			"malformed_expression_statement",
			"expression statement is missing its expression",
			nil,
			"call_statement"
		),
	},
	AstExprGroup = { expr = expression("malformed_group", "group is missing its expression") },
	AstExprTypeAssertion = {
		expr = expression("malformed_type_assertion", "type assertion is missing its runtime expression"),
	},
	AstExprInstantiate = {
		expr = expression("malformed_instantiation", "generic instantiation is missing its runtime expression"),
	},
	AstExprIndexExpr = {
		expr = expression("malformed_index", "index expression is missing its table"),
		index = expression("malformed_index", "index expression is missing its key"),
	},
	AstExprIndexName = { expr = expression("malformed_index", "named index is missing its table") },
	AstExprBinary = {
		left = expression("malformed_binary", "binary expression is missing its left operand"),
		right = expression("malformed_binary", "binary expression is missing its right operand"),
	},
	AstExprUnary = { expr = expression("malformed_unary", "unary expression is missing its operand") },
	AstExprCall = { func = expression("malformed_call", "call is missing its callee") },
	AstExprIfElse = {
		condition = expression("malformed_if_expression", "if expression is missing its condition"),
		trueExpr = expression("malformed_if_expression", "if expression is missing its true value"),
		falseExpr = expression("malformed_if_expression", "if expression is missing its false value"),
	},
}

local arraySlots: { [string]: { [string]: Role } } = {
	AstStatReturn = {
		list = expressionArray("list", "malformed_return", "return expression is not an AST node"),
	},
	AstStatLocal = {
		values = expressionArray("values", "malformed_local_declaration", "value-list member is not an AST node"),
	},
	AstStatAssign = {
		vars = expressionArray(
			"vars",
			"malformed_assignment",
			"assignment target is not an AST node",
			"assignment_target"
		),
		values = expressionArray("values", "malformed_assignment", "value-list member is not an AST node"),
	},
	AstStatForIn = {
		values = expressionArray("values", "malformed_generic_for", "value-list member is not an AST node"),
	},
	AstExprCall = {
		args = expressionArray("args", "malformed_call", "call argument is not an AST node"),
	},
	AstExprInterpString = {
		expressions = expressionArray(
			"expressions",
			"malformed_interpolation",
			"interpolation value is not an AST expression"
		),
	},
	AstExprTable = {
		items = {
			kind = "table_item_array",
			code = "malformed_ast",
			detail = "expected array field items",
			member_code = "malformed_table_item",
			member_detail = "table item is not an AST node",
			missing_owner = true,
		},
	},
}

local requiredSlotOrder: { [string]: { string } } = {
	AstStatReturn = { "list" },
	AstStatLocal = { "values" },
	AstStatLocalFunction = { "func" },
	AstStatFunction = { "name", "func" },
	AstStatAssign = { "vars", "values" },
	AstStatCompoundAssign = { "var", "value" },
	AstStatIf = { "condition" },
	AstStatWhile = { "condition" },
	AstStatRepeat = { "condition" },
	AstStatFor = { "from", "to" },
	AstStatForIn = { "values" },
	AstStatExpr = { "expr" },
	AstExprGroup = { "expr" },
	AstExprTypeAssertion = { "expr" },
	AstExprInstantiate = { "expr" },
	AstExprIndexExpr = { "expr", "index" },
	AstExprIndexName = { "expr" },
	AstExprTable = { "items" },
	AstExprInterpString = { "expressions" },
	AstExprBinary = { "left", "right" },
	AstExprUnary = { "expr" },
	AstExprCall = { "func", "args" },
	AstExprIfElse = { "condition", "trueExpr", "falseExpr" },
}

local supportedExpressionTags: { [string]: boolean } = table.freeze({
	AstExprGroup = true,
	AstExprTypeAssertion = true,
	AstExprInstantiate = true,
	AstExprConstantNil = true,
	AstExprConstantBool = true,
	AstExprConstantNumber = true,
	AstExprConstantInteger = true,
	AstExprConstantString = true,
	AstExprLocal = true,
	AstExprGlobal = true,
	AstExprIndexExpr = true,
	AstExprIndexName = true,
	AstExprTable = true,
	AstExprInterpString = true,
	AstExprBinary = true,
	AstExprUnary = true,
	AstExprCall = true,
	AstExprVarargs = true,
	AstExprFunction = true,
	AstExprIfElse = true,
	AstExprError = true,
})

local supportedAssignmentTargets: { [string]: boolean } = table.freeze({
	AstExprLocal = true,
	AstExprGlobal = true,
	AstExprIndexExpr = true,
	AstExprIndexName = true,
})

local supportedFunctionStatementTargets: { [string]: boolean } = table.freeze({
	AstExprLocal = true,
	AstExprGlobal = true,
	AstExprIndexName = true,
})

function AstExpressionSlots.childRole(parentRole: Role?, parent: Record, key: any, child: any): Role?
	if parentRole ~= nil and type(key) == "number" then
		if parentRole.kind == "expression_array" then
			return expression(
				parentRole.member_code :: string,
				parentRole.member_detail :: string,
				nil,
				parentRole.member_surface
			)
		elseif parentRole.kind == "table_item_array" then
			return {
				kind = "table_item",
				code = parentRole.member_code :: string,
				detail = parentRole.member_detail :: string,
			}
		end
	end
	if parentRole ~= nil and parentRole.kind == "table_item" then
		if key == "value" and (parent.kind == "list" or parent.kind == "item" or parent.kind == "record" or parent.kind == "general") then
			return expression("malformed_table_item", "table item is missing its value")
		elseif key == "key" and parent.kind == "record" then
			return exactExpression(
				"malformed_table_item",
				"keyed table item is missing its key",
				"AstExprConstantString",
				"record table item key is not a string literal"
			)
		elseif key == "key" and parent.kind == "general" then
			return expression("malformed_table_item", "keyed table item is missing its key")
		end
	end
	if type(key) ~= "string" or type(parent.type) ~= "string" then
		return nil
	end
	if parent.type == "AstExprBinary" and (parent.op == "And" or parent.op == "Or") then
		if key == "left" then
			return expression("malformed_short_circuit", "short-circuit expression is missing its left operand")
		elseif key == "right" then
			return expression("malformed_short_circuit", "short-circuit expression is missing its right operand")
		end
	end
	local direct = directSlots[parent.type]
	if direct ~= nil and direct[key] ~= nil then
		return direct[key]
	end
	local array = arraySlots[parent.type]
	if array ~= nil then
		return array[key]
	end
	return nil
end

function AstExpressionSlots.scalarProblem(role: Role, owner: Record?): Problem
	return { code = role.code, node = if role.missing_owner == true then owner else nil, detail = role.detail }
end

local function slotPredecessorsReady(record: Record, field: string): boolean
	if record.type == "AstStatLocal" and field == "values" then
		return type(record.vars) == "table"
	elseif record.type == "AstStatLocalFunction" and field == "func" then
		return type(record.name) == "table"
	elseif record.type == "AstStatForIn" and field == "values" then
		return type(record.vars) == "table" and #(record.vars :: { any }) > 0
	elseif record.type == "AstExprInterpString" and field == "expressions" then
		return type(record.strings) == "table"
	elseif (record.type == "AstStatWhile" or record.type == "AstStatRepeat") and field == "condition" then
		return type(record.body) == "table"
	end
	return true
end

function AstExpressionSlots.validateRole(role: Role?, record: Record, owner: Record?): Problem?
	if role ~= nil and role.kind == "expression" then
		if type(record.type) ~= "string" then
			return { code = "malformed_ast", node = record, detail = "AST node is missing its type tag" }
		end
		if role.exact_tag ~= nil and record.type ~= role.exact_tag then
			return {
				code = role.code,
				node = record,
				detail = role.exact_tag_detail :: string,
			}
		elseif role.surface == "function_statement_target" and supportedFunctionStatementTargets[record.type] ~= true then
			return {
				code = role.code,
				node = record,
				detail = "function statement target must be a local, global, or named index",
			}
		elseif role.surface == "assignment_target" and supportedAssignmentTargets[record.type] ~= true then
			return {
				code = "unsupported_assignment_target",
				node = record,
				detail = `assignment target node {record.type} is not supported`,
			}
		elseif role.surface == "call_statement" and record.type ~= "AstExprCall" then
			return {
				code = "unsupported_expression_statement",
				node = owner or record,
				detail = "only call expressions are valid standalone expressions",
			}
		elseif supportedExpressionTags[record.type] ~= true then
			return {
				code = "unsupported_expression",
				node = record,
				detail = `expression node {record.type} is not supported by this frontend slice`,
			}
		end
	elseif role ~= nil and role.kind == "table_item" then
		if record.type ~= "AstExprTableItem" then
			return {
				code = "malformed_table_item",
				node = record,
				detail = "table item is not an AstExprTableItem",
			}
		elseif record.kind ~= "list" and record.kind ~= "item" and record.kind ~= "record" and record.kind ~= "general" then
			return {
				code = "unsupported_table_item_kind",
				node = record,
				detail = `table item kind {tostring(record.kind)} is not mapped`,
			}
		elseif (record.kind == "list" or record.kind == "item") and record.key ~= nil then
			return {
				code = "malformed_table_item",
				node = record,
				detail = "list table item must not carry a key expression",
			}
		end
	end
	return nil
end

function AstExpressionSlots.validateRequired(role: Role?, record: Record): Problem?
	if role ~= nil and role.kind == "table_item" then
		local itemFields: { string } = if record.kind == "record" or record.kind == "general"
			then { "key", "value" }
			else { "value" }
		for _, field in itemFields do
			if record[field] == nil then
				local fieldRole = AstExpressionSlots.childRole(role, record, field, nil)
				return AstExpressionSlots.scalarProblem(fieldRole :: Role, record)
			end
		end
	end
	if type(record.type) == "string" then
		local fields = requiredSlotOrder[record.type]
		if fields ~= nil then
			for _, field in fields do
				if record[field] == nil and slotPredecessorsReady(record, field) then
					local fieldRole = AstExpressionSlots.childRole(role, record, field, nil)
					return AstExpressionSlots.scalarProblem(fieldRole :: Role, record)
				end
			end
		end
	end
	return nil
end

function AstExpressionSlots.isSupportedRuntimeExpression(value: any): boolean
	if type(value) ~= "table" then
		return false
	end
	local record = value :: Record
	return type(record.type) == "string"
		and record.type ~= "AstExprError"
		and supportedExpressionTags[record.type] == true
		and AstExpressionSlots.validateRequired(nil, record) == nil
end

return table.freeze(AstExpressionSlots)
