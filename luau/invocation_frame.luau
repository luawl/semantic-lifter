--!strict

-- Owns bounded Lua invocation adjustment and lexical parameter/vararg frames.
-- Snapshot frames may cross a function-local alias, but never a non-variadic
-- invocation boundary.

local AstExpressionScalar = require("./ast_expression_scalar")
local AstExpressionSlots = require("./ast_expression_slots")

local InvocationFrame = {}
InvocationFrame.maxResultWidth = 64

export type Record = { [string]: any }
export type ArgumentState = "value" | "implicit_nil" | "unknown"

export type Binding = {
	kind: "parameter" | "local_snapshot",
	name: string,
	location: string,
	argumentState: ArgumentState?,
	argument: Record?,
	resultOrdinal: number,
	useNode: Record,
}

export type Context = {
	kind: "invocation" | "snapshot",
	parent: Context?,
	bindings: { Binding },
	vararg: {
		call: Record,
		parameterCount: number,
		argumentCount: number,
	}?,
}

export type SelectedValue = {
	expression: Record,
	resultOrdinal: number,
}

export type ArgumentAdjustment = {
	state: ArgumentState,
	selected: SelectedValue?,
}

local function expectRecord(value: any, label: string): Record
	assert(type(value) == "table", `{label} must be an AST object`)
	return value :: Record
end

function InvocationFrame.recordArrayLength(value: any): number?
	if type(value) ~= "table" then
		return nil
	end
	local count = 0
	local maximum = 0
	for key, element in value do
		if type(key) ~= "number"
			or key < 1
			or key % 1 ~= 0
			or type(element) ~= "table"
			or type((element :: Record).type) ~= "string"
		then
			return nil
		end
		count += 1
		maximum = math.max(maximum, key)
	end
	return if maximum == count then count else nil
end

function InvocationFrame.unwrapExpression(value: any, label: string): Record
	local expression = expectRecord(value, label)
	local seen: { [any]: boolean } = {}
	while expression.type == "AstExprGroup"
		or expression.type == "AstExprTypeAssertion"
		or expression.type == "AstExprInstantiate"
	do
		assert(seen[expression] ~= true, `{label} contains a transparent-wrapper cycle`)
		seen[expression] = true
		expression = expectRecord(expression.expr, label .. " wrapper")
	end
	return expression
end

function InvocationFrame.localIdentity(value: any): (string?, string?)
	if type(value) ~= "table" then
		return nil, nil
	end
	local localNode = value :: Record
	if localNode.type ~= "AstLocal"
		or type(localNode.name) ~= "string"
		or localNode.name == ""
		or type(localNode.location) ~= "string"
		or localNode.location == ""
	then
		return nil, nil
	end
	return localNode.name, localNode.location
end

function InvocationFrame.directLocalIdentity(value: any, label: string): (string?, string?)
	local expression = InvocationFrame.unwrapExpression(value, label)
	if expression.type ~= "AstExprLocal" then
		return nil, nil
	end
	return InvocationFrame.localIdentity(expression["local"])
end

function InvocationFrame.adjustedCallArgument(
	call: Record,
	argumentCount: number,
	argumentOrdinal: number
): ArgumentAdjustment
	if argumentCount > InvocationFrame.maxResultWidth
		or argumentOrdinal < 1
		or argumentOrdinal > InvocationFrame.maxResultWidth
	then
		return { state = "unknown", selected = nil }
	elseif argumentOrdinal <= argumentCount then
		return {
			state = "value",
			selected = { expression = call.args[argumentOrdinal] :: Record, resultOrdinal = 1 },
		}
	elseif argumentCount == 0 then
		return { state = "implicit_nil", selected = nil }
	end
	local finalArgument = call.args[argumentCount] :: Record
	local nestedResultOrdinal = argumentOrdinal - argumentCount + 1
	if finalArgument.type == "AstExprCall" then
		if finalArgument.self ~= false or InvocationFrame.recordArrayLength(finalArgument.args) == nil then
			return { state = "unknown", selected = nil }
		end
	elseif finalArgument.type == "AstExprVarargs" then
		-- Open varargs may supply the selected ordinal.
	elseif AstExpressionSlots.isSupportedRuntimeExpression(finalArgument)
		and AstExpressionScalar.validatePreorder(finalArgument) == nil
		and AstExpressionScalar.validatePostorder(finalArgument) == nil
	then
		return { state = "implicit_nil", selected = nil }
	else
		return { state = "unknown", selected = nil }
	end
	return {
		state = "value",
		selected = { expression = finalArgument, resultOrdinal = nestedResultOrdinal },
	}
end

function InvocationFrame.selectedCallArgument(
	call: Record,
	argumentCount: number,
	argumentOrdinal: number
): SelectedValue?
	return InvocationFrame.adjustedCallArgument(call, argumentCount, argumentOrdinal).selected
end

function InvocationFrame.adjustedContextVararg(
	value: any,
	resultOrdinal: number,
	context: Context?
): (ArgumentAdjustment?, Context?)
	if type(value) ~= "table"
		or resultOrdinal < 1
		or resultOrdinal > InvocationFrame.maxResultWidth
	then
		return nil, nil
	end
	local expression = value :: Record
	if resultOrdinal == 1 then
		expression = InvocationFrame.unwrapExpression(expression, "target forwarded vararg")
	elseif expression.type ~= "AstExprVarargs" then
		return nil, nil
	end
	if expression.type ~= "AstExprVarargs" then
		return nil, nil
	end
	local current = context
	while current ~= nil do
		local frame = current :: Context
		if frame.vararg ~= nil then
			local owner = frame.vararg
			local argumentOrdinal = owner.parameterCount + resultOrdinal
			if argumentOrdinal > InvocationFrame.maxResultWidth then
				return nil, nil
			end
			return InvocationFrame.adjustedCallArgument(
				owner.call,
				owner.argumentCount,
				argumentOrdinal
			), frame.parent
		elseif frame.kind == "invocation" then
			return nil, nil
		end
		current = frame.parent
	end
	return nil, nil
end

function InvocationFrame.selectedContextVararg(
	value: any,
	resultOrdinal: number,
	context: Context?
): (SelectedValue?, Context?)
	local adjustment, parent = InvocationFrame.adjustedContextVararg(value, resultOrdinal, context)
	if adjustment == nil or (adjustment :: ArgumentAdjustment).state ~= "value" then
		return nil, nil
	end
	return (adjustment :: ArgumentAdjustment).selected, parent
end

function InvocationFrame.fixedParameterContext(call: Record, callee: Record, parent: Context?): Context?
	local parameterCount = InvocationFrame.recordArrayLength(callee.args)
	local argumentCount = InvocationFrame.recordArrayLength(call.args)
	if parameterCount == nil
		or argumentCount == nil
		or parameterCount > InvocationFrame.maxResultWidth
		or argumentCount > InvocationFrame.maxResultWidth
	then
		return nil
	end
	local bindings: { Binding } = {}
	local seenObjects: { [any]: boolean } = {}
	local seenLocations: { [string]: boolean } = {}
	for index = 1, parameterCount do
		local parameter = callee.args[index] :: Record
		local name, location = InvocationFrame.localIdentity(parameter)
		if name == nil
			or location == nil
			or seenObjects[parameter] == true
			or seenLocations[location :: string] == true
		then
			return nil
		end
		seenObjects[parameter] = true
		seenLocations[location :: string] = true
		local adjustment = InvocationFrame.adjustedCallArgument(call, argumentCount, index)
		local selectedArgument = adjustment.selected
		table.insert(bindings, {
			kind = "parameter",
			name = name :: string,
			location = location :: string,
			argumentState = adjustment.state,
			argument = if selectedArgument == nil then nil else selectedArgument.expression,
			resultOrdinal = if selectedArgument == nil then 1 else selectedArgument.resultOrdinal,
			useNode = call,
		})
	end
	return {
		kind = "invocation",
		parent = parent,
		bindings = bindings,
		vararg = if callee.vararg == true
			then { call = call, parameterCount = parameterCount, argumentCount = argumentCount }
			else nil,
	}
end

function InvocationFrame.selectedVarargArgument(
	call: Record,
	callee: Record,
	returned: Record,
	resultOrdinal: number
): SelectedValue?
	local parameterCount = InvocationFrame.recordArrayLength(callee.args)
	local argumentCount = InvocationFrame.recordArrayLength(call.args)
	if returned.type ~= "AstExprVarargs"
		or callee.vararg ~= true
		or parameterCount == nil
		or argumentCount == nil
		or parameterCount > InvocationFrame.maxResultWidth
		or argumentCount > InvocationFrame.maxResultWidth
		or resultOrdinal < 1
		or resultOrdinal > InvocationFrame.maxResultWidth
	then
		return nil
	end
	local argumentOrdinal = parameterCount + resultOrdinal
	if argumentOrdinal > InvocationFrame.maxResultWidth then
		return nil
	end
	return InvocationFrame.selectedCallArgument(call, argumentCount, argumentOrdinal)
end

function InvocationFrame.calleeBinding(context: Context?, expression: Record): (Binding?, Context?)
	if expression.type ~= "AstExprLocal" then
		return nil, nil
	end
	local name, location = InvocationFrame.localIdentity(expression["local"])
	if name == nil or location == nil then
		return nil, nil
	end
	local current = context
	while current ~= nil do
		for _, binding in (current :: Context).bindings do
			if binding.name == name and binding.location == location then
				return binding, (current :: Context).parent
			end
		end
		current = (current :: Context).parent
	end
	return nil, nil
end

return table.freeze(InvocationFrame)
