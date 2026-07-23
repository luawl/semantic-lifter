--!strict

local TemporalTargetIdentity = require("./temporal_target_identity")

local TemporalTestSupport = {}

export type Record = { [string]: any }

function TemporalTestSupport.declaration(name: string, location: string): Record
	return { type = "AstLocal", name = name, location = location }
end

function TemporalTestSupport.localExpression(localNode: Record, location: string): Record
	return { type = "AstExprLocal", location = location, ["local"] = localNode }
end

function TemporalTestSupport.globalExpression(name: string, location: string): Record
	return { type = "AstExprGlobal", location = location, global = name }
end

function TemporalTestSupport.block(body: { Record }, location: string): Record
	return { type = "AstStatBlock", location = location, body = body }
end

function TemporalTestSupport.invocationFromBody(
	body: { Record },
	prefix: string,
	wrappers: { string }?,
	args: { Record }?
): (Record, Record)
	local functionValue: Record = {
		type = "AstExprFunction",
		location = prefix .. "-function",
		args = {},
		body = TemporalTestSupport.block(body, prefix .. "-function-body"),
	}
	local callee = functionValue
	if wrappers ~= nil then
		for index, kind in wrappers do
			callee = { type = kind, location = `{prefix}-wrapper-{index}`, expr = callee }
		end
	end
	return functionValue, {
		type = "AstExprCall",
		location = prefix .. "-invocation",
		func = callee,
		args = args or {},
		self = false,
	}
end

function TemporalTestSupport.localStatement(localNode: Record, location: string, value: Record?): Record
	return {
		type = "AstStatLocal",
		location = location,
		vars = { localNode },
		values = { value or { type = "AstExprConstantNil", location = location .. ":nil" } },
	}
end

function TemporalTestSupport.assignmentValue(localNode: Record, location: string, value: Record): Record
	return {
		type = "AstStatAssign",
		location = location,
		vars = { TemporalTestSupport.localExpression(localNode, location .. ":target") },
		values = { value },
	}
end

function TemporalTestSupport.assignmentBackedSnapshots(body: { Record }, prefix: string): { Record }
	local converted: { Record } = {}
	for index, statement in body do
		if statement.type == "AstStatReturn" then
			table.insert(converted, statement)
		else
			assert(statement.type == "AstStatLocal"
				and type(statement.vars) == "table"
				and #statement.vars >= 1
				and type(statement.values) == "table"
				and #statement.values >= 1)
			local assignmentTargets: { Record } = {}
			for targetIndex, target in statement.vars do
				table.insert(assignmentTargets, TemporalTestSupport.localExpression(
					target :: Record,
					`{prefix}-assignment-{index}-target-{targetIndex}`
				))
			end
			table.insert(converted, {
				type = "AstStatLocal",
				location = `{prefix}-declaration-{index}`,
				vars = statement.vars,
				values = {},
			})
			table.insert(converted, {
				type = "AstStatAssign",
				location = `{prefix}-assignment-{index}`,
				vars = assignmentTargets,
				values = statement.values,
			})
		end
	end
	return converted
end

function TemporalTestSupport.setSingleValueTargetOrdinal(
	statement: Record,
	ordinal: number,
	width: number,
	prefix: string
): { Record }
	assert(ordinal >= 1
		and ordinal <= width
		and type(statement.vars) == "table"
		and type(statement.vars[1]) == "table"
		and type(statement.values) == "table"
		and #statement.values == 1)
	local selected = statement.vars[1] :: Record
	local targets: { Record } = {}
	for index = 1, width do
		table.insert(targets, if index == ordinal
			then selected
			else TemporalTestSupport.declaration(`{prefix}Target{index}`, `{prefix}-target-{index}`))
	end
	statement.vars = targets
	return targets
end

function TemporalTestSupport.assignment(localNode: Record, location: string): Record
	return TemporalTestSupport.assignmentValue(
		localNode,
		location,
		{ type = "AstExprGlobal", location = location .. ":value", global = "authenticated_target" }
	)
end

function TemporalTestSupport.callExpression(localNode: Record, location: string): Record
	return {
		type = "AstExprCall",
		location = location,
		func = TemporalTestSupport.localExpression(localNode, location .. ":callee"),
		args = {},
		self = false,
	}
end

function TemporalTestSupport.callStatement(call: Record, location: string): Record
	return { type = "AstStatExpr", location = location, expr = call }
end

function TemporalTestSupport.document(body: { Record }): Record
	return { root = TemporalTestSupport.block(body, "root") }
end

function TemporalTestSupport.branchStatement(prefix: string, thenBody: { Record }, elseBody: Record?): Record
	return {
		type = "AstStatIf",
		location = prefix .. "-if",
		condition = { type = "AstExprGlobal", location = prefix .. "-condition", global = "condition" },
		thenbody = TemporalTestSupport.block(thenBody, prefix .. "-then"),
		elsebody = elseBody,
	}
end

function TemporalTestSupport.whileStatement(prefix: string, body: { Record }): Record
	return {
		type = "AstStatWhile",
		location = prefix .. "-while",
		condition = { type = "AstExprGlobal", location = prefix .. "-condition", global = "condition" },
		body = TemporalTestSupport.block(body, prefix .. "-body"),
	}
end

function TemporalTestSupport.environmentAliasChain(depth: number, prefix: string): (Record, Record, Record)
	local body: { Record } = {}
	local previous = TemporalTestSupport.declaration(prefix .. "Root", prefix .. "-root")
	table.insert(body, TemporalTestSupport.localStatement(previous, prefix .. "-root-declaration", {
		type = "AstExprGlobal",
		location = prefix .. "-root-value",
		global = "authenticated_target",
	}))
	for index = 1, depth do
		local current = TemporalTestSupport.declaration(prefix .. tostring(index), `{prefix}-alias-{index}`)
		table.insert(
			body,
			TemporalTestSupport.localStatement(
				current,
				`{prefix}-alias-{index}-declaration`,
				TemporalTestSupport.localExpression(previous, `{prefix}-alias-{index}-value`)
			)
		)
		previous = current
	end
	local call = TemporalTestSupport.callExpression(previous, prefix .. "-call")
	table.insert(body, TemporalTestSupport.callStatement(call, prefix .. "-call-statement"))
	return TemporalTestSupport.document(body), call, previous
end

function TemporalTestSupport.aliasJoinDocument(levels: number, candidateCount: number, prefix: string): (Record, Record, Record)
	assert(levels >= 1 and candidateCount >= 2)
	local body: { Record } = {}
	local previous = TemporalTestSupport.declaration(prefix .. "Stable", prefix .. "-stable")
	table.insert(body, TemporalTestSupport.localStatement(previous, prefix .. "-stable-declaration", {
		type = "AstExprGlobal",
		location = prefix .. "-stable-value",
		global = "authenticated_target",
	}))
	for level = 1, levels do
		local joined = TemporalTestSupport.declaration(`{prefix}Join{level}`, `{prefix}-join-{level}`)
		table.insert(body, TemporalTestSupport.localStatement(joined, `{prefix}-join-{level}-declaration`))
		local elseNode: Record = TemporalTestSupport.block({
			TemporalTestSupport.assignmentValue(
				joined,
				`{prefix}-join-{level}-write-{candidateCount}`,
				TemporalTestSupport.localExpression(previous, `{prefix}-join-{level}-value-{candidateCount}`)
			),
		}, `{prefix}-join-{level}-else-{candidateCount}`)
		for candidate = candidateCount - 1, 1, -1 do
			elseNode = TemporalTestSupport.branchStatement(
				`{prefix}-join-{level}-branch-{candidate}`,
				{
					TemporalTestSupport.assignmentValue(
						joined,
						`{prefix}-join-{level}-write-{candidate}`,
						TemporalTestSupport.localExpression(previous, `{prefix}-join-{level}-value-{candidate}`)
					),
				},
				elseNode
			)
		end
		table.insert(body, elseNode)
		previous = joined
	end
	local target = TemporalTestSupport.declaration(prefix .. "Target", prefix .. "-target")
	table.insert(
		body,
		TemporalTestSupport.localStatement(
			target,
			prefix .. "-target-declaration",
			TemporalTestSupport.localExpression(previous, prefix .. "-target-value")
		)
	)
	local call = TemporalTestSupport.callExpression(target, prefix .. "-call")
	table.insert(body, TemporalTestSupport.callStatement(call, prefix .. "-call-statement"))
	return TemporalTestSupport.document(body), call, target
end

function TemporalTestSupport.verifyOrigin(documentValue: Record, call: Record, localNode: Record, origin: Record)
	return TemporalTargetIdentity.verify(TemporalTargetIdentity.analyze(documentValue), call, localNode, origin)
end

function TemporalTestSupport.verify(
	documentValue: Record,
	call: Record,
	localNode: Record,
	originKind: "local_value" | "local_place"
)
	return TemporalTestSupport.verifyOrigin(
		documentValue,
		call,
		localNode,
		if originKind == "local_value"
			then { kind = "local_value", declaration = localNode }
			else { kind = "local_place", declaration = localNode }
	)
end

function TemporalTestSupport.expectFailure(callback: () -> (), expected: string)
	local ok, message = pcall(function(): string
		callback()
		return ""
	end)
	assert(not ok, `temporal target unexpectedly passed: {expected}`)
	assert(string.find(tostring(message), expected, 1, true) ~= nil, `temporal target failure lost diagnostic: {tostring(message)}`)
end

return table.freeze(TemporalTestSupport)
