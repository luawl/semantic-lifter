--!strict

-- Lexical scope and binding-position contexts for the admission graph walk.
-- Positions encode language order, not source-location string order.

local AstLexicalScope = {}

type Record = { [string]: any }

export type Scope = {
	parent: number,
	entry_position: number,
}

export type Context = {
	scope: number,
	position: number,
	statement_scope: number?,
}

export type State = {
	scopes: { [number]: Scope },
	next_scope: number,
}

local function reserveScope(state: State, parent: number, entryPosition: number): number
	state.next_scope += 1
	state.scopes[state.next_scope] = { parent = parent, entry_position = entryPosition }
	return state.next_scope
end

function AstLexicalScope.initialize(root: Record): (State, Context)
	local state: State = { scopes = {}, next_scope = 0 }
	local rootScope = if root.type == "AstStatBlock" then reserveScope(state, 0, 0) else 0
	return state, { scope = rootScope, position = 0, statement_scope = nil }
end

function AstLexicalScope.reserveBody(state: State, record: Record, context: Context): number?
	if (record.type == "AstExprFunction"
		or record.type == "AstStatFor"
		or record.type == "AstStatForIn"
		or record.type == "AstStatRepeat")
		and type(record.body) == "table"
		and (record.body :: Record).type == "AstStatBlock"
	then
		return reserveScope(state, context.scope, context.position)
	end
	return nil
end

function AstLexicalScope.declarationContext(record: Record, context: Context, bodyScope: number?): Context
	if record.type == "AstStatLocal" then
		return { scope = context.scope, position = context.position + 1, statement_scope = nil }
	elseif record.type == "AstExprFunction" or record.type == "AstStatFor" or record.type == "AstStatForIn" then
		return { scope = bodyScope or context.scope, position = 0, statement_scope = nil }
	end
	return { scope = context.scope, position = context.position, statement_scope = nil }
end

function AstLexicalScope.childContext(
	state: State,
	record: Record,
	key: any,
	child: Record,
	context: Context,
	bodyScope: number?
): Context
	local scope = context.scope
	local position = context.position
	local statementScope: number? = nil
	if context.statement_scope ~= nil and type(key) == "number" then
		scope = context.statement_scope :: number
		position = key * 2
	end

	if record.type == "AstStatBlock" and key == "body" then
		statementScope = context.scope
	elseif bodyScope ~= nil and key == "body" and child == record.body then
		scope = bodyScope :: number
		position = 0
	elseif record.type == "AstStatRepeat" and bodyScope ~= nil and key == "condition" then
		scope = bodyScope :: number
		local body = record.body :: Record
		position = if type(body.body) == "table" then (#(body.body :: { any }) + 1) * 2 else 1
	elseif bodyScope ~= nil
		and ((record.type == "AstExprFunction" and (key == "args" or key == "self"))
			or ((record.type == "AstStatFor" or record.type == "AstStatForIn") and (key == "var" or key == "vars")))
	then
		scope = bodyScope :: number
		position = 0
	elseif child.type == "AstStatBlock" then
		scope = reserveScope(state, scope, position)
		position = 0
	end
	return { scope = scope, position = position, statement_scope = statementScope }
end

return table.freeze(AstLexicalScope)
