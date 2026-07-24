--!strict

-- Statement-valued and block-valued source AST slots consumed by the current
-- frontend. Type and declaration metadata are intentionally outside this map.

local AstStatementSlots = {}

type Record = { [string]: any }

export type Kind = "statement" | "block" | "statement_array" | "else_body"

export type Role = {
	kind: Kind,
	code: string,
	detail: string,
	member_code: string?,
	member_detail: string?,
	missing_owner: boolean?,
}

export type Problem = {
	code: string,
	node: Record?,
	detail: string,
}

local function block(code: string, detail: string, missingOwner: boolean?): Role
	return { kind = "block", code = code, detail = detail, missing_owner = missingOwner }
end

local directSlots: { [string]: { [string]: Role } } = {
	AstStatIf = {
		thenbody = block("malformed_if", "if statement is missing its then body"),
		elsebody = { kind = "else_body", code = "malformed_ast", detail = "else body is missing its type tag" },
	},
	AstStatWhile = { body = block("malformed_while", "while statement is missing its body") },
	AstStatRepeat = { body = block("malformed_repeat", "repeat statement is missing its body") },
	AstStatFor = { body = block("malformed_numeric_for", "numeric for is missing its body", true) },
	AstStatForIn = { body = block("malformed_generic_for", "generic for is missing its body") },
	AstExprFunction = { body = block("malformed_function", "function is missing its body") },
	AstStatBlock = {
		body = {
			kind = "statement_array",
			code = "malformed_ast",
			detail = "expected array field body",
			member_code = "malformed_statement",
			member_detail = "block member is not an AST node",
			missing_owner = true,
		},
	},
}

local requiredSlotOrder: { [string]: { string } } = {
	AstStatIf = { "thenbody" },
	AstStatWhile = { "body" },
	AstStatRepeat = { "body" },
	AstStatFor = { "body" },
	AstStatForIn = { "body" },
	AstExprFunction = { "body" },
	AstStatBlock = { "body" },
}

local supportedStatementTags: { [string]: boolean } = table.freeze({
	AstStatLocal = true,
	AstStatLocalFunction = true,
	AstStatFunction = true,
	AstStatAssign = true,
	AstStatCompoundAssign = true,
	AstStatIf = true,
	AstStatWhile = true,
	AstStatRepeat = true,
	AstStatFor = true,
	AstStatForIn = true,
	AstStatContinue = true,
	AstStatBreak = true,
	AstStatReturn = true,
	AstStatBlock = true,
	AstStatTypeAlias = true,
	AstStatTypeFunction = true,
	AstStatDeclareClass = true,
	AstStatDeclareGlobal = true,
	AstStatDeclareFunction = true,
	AstStatDeclareExternType = true,
	AstStatError = true,
	AstStatExpr = true,
})

function AstStatementSlots.childRole(parentRole: Role?, parent: Record, key: any, child: any): Role?
	if parentRole ~= nil and parentRole.kind == "statement_array" and type(key) == "number" then
		return {
			kind = "statement",
			code = parentRole.member_code :: string,
			detail = parentRole.member_detail :: string,
		}
	end
	if type(key) ~= "string" or type(parent.type) ~= "string" then
		return nil
	end
	local slots = directSlots[parent.type]
	if slots ~= nil then
		return slots[key]
	end
	return nil
end

function AstStatementSlots.scalarProblem(role: Role, owner: Record?): Problem
	return { code = role.code, node = if role.missing_owner == true then owner else nil, detail = role.detail }
end

function AstStatementSlots.validateRole(role: Role?, record: Record): Problem?
	if role ~= nil and role.kind == "statement" then
		if type(record.type) ~= "string" then
			return { code = "malformed_ast", node = record, detail = "AST node is missing its type tag" }
		elseif supportedStatementTags[record.type] ~= true then
			return {
				code = "unsupported_statement",
				node = record,
				detail = `statement node {record.type} is not supported by this frontend slice`,
			}
		end
	elseif role ~= nil and role.kind == "block" then
		if type(record.type) ~= "string" then
			return { code = "malformed_ast", node = record, detail = "AST node is missing its type tag" }
		elseif record.type ~= "AstStatBlock" then
			return { code = "malformed_block", node = record, detail = "expected an AstStatBlock" }
		end
	elseif role ~= nil and role.kind == "else_body" then
		if type(record.type) ~= "string" then
			return { code = "malformed_ast", node = record, detail = "else body is missing its type tag" }
		elseif record.type ~= "AstStatBlock" and record.type ~= "AstStatIf" then
			return { code = "unsupported_else_body", node = record, detail = "else body must be a block or nested if" }
		end
	end

	return nil
end

local function slotPredecessorsReady(record: Record, field: string): boolean
	if record.type == "AstStatForIn" and field == "body" then
		return type(record.vars) == "table"
			and #(record.vars :: { any }) > 0
			and type(record.values) == "table"
	end
	return true
end

function AstStatementSlots.validateRequired(role: Role?, record: Record): Problem?
	if type(record.type) == "string" then
		local fields = requiredSlotOrder[record.type]
		if fields ~= nil then
			for _, field in fields do
				if record[field] == nil and slotPredecessorsReady(record, field) then
					local fieldRole = AstStatementSlots.childRole(role, record, field, nil)
					return AstStatementSlots.scalarProblem(fieldRole :: Role, record)
				end
			end
		end
	end
	return nil
end

return table.freeze(AstStatementSlots)
