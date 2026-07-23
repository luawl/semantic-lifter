--!strict

local Support = require("./temporal_test_support")

local TemporalInvocationTestSupport = {}

export type Record = Support.Record
export type BindingKind = "local" | "local_function" | "assignment"
export type AliasBindingKind = "local" | "assignment"

function TemporalInvocationTestSupport.differentTarget(location: string): Record
	return Support.globalExpression("different_target", location)
end

function TemporalInvocationTestSupport.readInvocation(call: Record, prefix: string): (Record, Record)
	return Support.invocationFromBody({ Support.callStatement(call, prefix .. "-read-statement") }, prefix, nil, nil)
end

function TemporalInvocationTestSupport.futureWriteChain(
	target: Record,
	call: Record,
	prefix: string,
	depth: number
): Record
	assert(depth >= 1)
	local _, invocation = TemporalInvocationTestSupport.readInvocation(call, prefix .. "-1")
	for index = 2, depth do
		local _, outer = Support.invocationFromBody({
			Support.callStatement(invocation, `{prefix}-{index - 1}-statement`),
			Support.assignmentValue(
				target,
				`{prefix}-{index}-future-write`,
				TemporalInvocationTestSupport.differentTarget(`{prefix}-{index}-future-value`)
			),
		}, `{prefix}-{index}`, nil, nil)
		invocation = outer
	end
	return invocation
end

function TemporalInvocationTestSupport.wrappedExpression(value: Record, prefix: string): Record
	local result = value
	local wrappers: { string } = { "AstExprGroup", "AstExprTypeAssertion", "AstExprInstantiate" }
	for index, kind in wrappers do
		result = { type = kind, location = `{prefix}-wrapper-{index}`, expr = result }
	end
	return result
end

function TemporalInvocationTestSupport.localInvocation(localNode: Record, prefix: string, wrapped: boolean): Record
	local callee = Support.localExpression(localNode, prefix .. "-callee")
	return {
		type = "AstExprCall",
		location = prefix .. "-invocation",
		func = if wrapped then TemporalInvocationTestSupport.wrappedExpression(callee, prefix .. "-callee") else callee,
		args = {},
		self = false,
	}
end

function TemporalInvocationTestSupport.localFunctionStatement(
	localNode: Record,
	functionValue: Record,
	location: string
): Record
	return {
		type = "AstStatLocalFunction",
		location = location,
		name = localNode,
		func = functionValue,
	}
end

function TemporalInvocationTestSupport.appendFunctionBinding(
	body: { Record },
	holder: Record,
	functionValue: Record,
	prefix: string,
	wrapped: boolean,
	bindingKind: BindingKind
)
	local initializer = if wrapped
		then TemporalInvocationTestSupport.wrappedExpression(functionValue, prefix .. "-initializer")
		else functionValue
	if bindingKind == "local" then
		table.insert(body, Support.localStatement(holder, prefix .. "-declaration", initializer))
	elseif bindingKind == "local_function" then
		assert(not wrapped)
		table.insert(body, TemporalInvocationTestSupport.localFunctionStatement(holder, functionValue, prefix .. "-declaration"))
	else
		table.insert(body, Support.localStatement(holder, prefix .. "-declaration"))
		table.insert(body, Support.assignmentValue(holder, prefix .. "-assignment", initializer))
	end
end

function TemporalInvocationTestSupport.appendAliasBinding(
	body: { Record },
	previous: Record,
	prefix: string,
	wrapped: boolean,
	bindingKind: AliasBindingKind
): Record
	local alias = Support.declaration(prefix .. "Alias", prefix .. "-alias")
	local source = Support.localExpression(previous, prefix .. "-source")
	local value = if wrapped then TemporalInvocationTestSupport.wrappedExpression(source, prefix .. "-value") else source
	if bindingKind == "local" then
		table.insert(body, Support.localStatement(alias, prefix .. "-declaration", value))
	else
		table.insert(body, Support.localStatement(alias, prefix .. "-declaration"))
		table.insert(body, Support.assignmentValue(alias, prefix .. "-assignment", value))
	end
	return alias
end

function TemporalInvocationTestSupport.singleUseFutureWriteChain(
	target: Record,
	call: Record,
	prefix: string,
	depth: number,
	wrapped: boolean,
	bindingKind: BindingKind
): Record
	assert(depth >= 2)
	local functionValue, _ = TemporalInvocationTestSupport.readInvocation(call, prefix .. "-local-function")
	local holder = Support.declaration(prefix .. "Holder", prefix .. "-holder")
	local invocation = TemporalInvocationTestSupport.localInvocation(holder, prefix .. "-local-call", wrapped)
	local body: { Record } = {}
	TemporalInvocationTestSupport.appendFunctionBinding(
		body,
		holder,
		functionValue,
		prefix .. "-holder",
		wrapped,
		bindingKind
	)
	table.insert(body, Support.callStatement(invocation, prefix .. "-local-call-statement"))
	table.insert(
		body,
		Support.assignmentValue(
			target,
			prefix .. "-2-future-write",
			TemporalInvocationTestSupport.differentTarget(prefix .. "-2-future-value")
		)
	)
	local _, outer = Support.invocationFromBody(body, prefix .. "-2", nil, nil)
	invocation = outer
	for index = 3, depth do
		_, outer = Support.invocationFromBody({
			Support.callStatement(invocation, `{prefix}-{index - 1}-statement`),
			Support.assignmentValue(
				target,
				`{prefix}-{index}-future-write`,
				TemporalInvocationTestSupport.differentTarget(`{prefix}-{index}-future-value`)
			),
		}, `{prefix}-{index}`, nil, nil)
		invocation = outer
	end
	return invocation
end

function TemporalInvocationTestSupport.aliasedFutureWriteChain(
	target: Record,
	call: Record,
	prefix: string,
	aliasDepth: number,
	sourceBinding: BindingKind,
	aliasBinding: AliasBindingKind,
	wrapped: boolean
): Record
	assert(aliasDepth >= 1)
	local functionValue, _ = TemporalInvocationTestSupport.readInvocation(call, prefix .. "-function")
	local holder = Support.declaration(prefix .. "Holder", prefix .. "-holder")
	local body: { Record } = {}
	TemporalInvocationTestSupport.appendFunctionBinding(
		body,
		holder,
		functionValue,
		prefix .. "-holder",
		sourceBinding ~= "local_function" and wrapped,
		sourceBinding
	)
	local callee = holder
	for index = 1, aliasDepth do
		callee = TemporalInvocationTestSupport.appendAliasBinding(
			body,
			callee,
			`{prefix}-alias-{index}`,
			wrapped,
			aliasBinding
		)
	end
	table.insert(
		body,
		Support.callStatement(
			TemporalInvocationTestSupport.localInvocation(callee, prefix .. "-call", wrapped),
			prefix .. "-call-statement"
		)
	)
	table.insert(
		body,
		Support.assignmentValue(
			target,
			prefix .. "-write",
			TemporalInvocationTestSupport.differentTarget(prefix .. "-value")
		)
	)
	local _, outer = Support.invocationFromBody(body, prefix .. "-outer", nil, nil)
	return outer
end

return table.freeze(TemporalInvocationTestSupport)
