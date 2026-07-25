--!strict

-- Matches one authenticated semantic origin against an existing source
-- expression. Temporal ownership and local availability stay with the caller.

local InvocationFrame = require("./invocation_frame")
local TargetOriginExpressionMatcher = require("./target_origin_expression_matcher")
local TargetOriginReturnSelector = require("./target_origin_return_selector")

local TargetOriginMatcher = {}
TargetOriginMatcher.maxDirectReturnDepth = 64
TargetOriginMatcher.maxLocalSnapshotDepth = 64
TargetOriginMatcher.maxResultSnapshotDepth = 64
TargetOriginMatcher.maxParameterCalleeDepth = 64
TargetOriginMatcher.maxLocalDeclarationTargets = 64
TargetOriginMatcher.maxLocalDeclarationValues = 64
TargetOriginMatcher.maxDirectReturnValues = InvocationFrame.maxResultWidth

type Record = InvocationFrame.Record
type LocalMatcher = (Record, Record) -> boolean
type CalleeResolver = (Record, Record) -> Record?
export type ResultMatcher = (Record, number, Record) -> boolean
type CalleeBinding = InvocationFrame.Binding
type CalleeContext = InvocationFrame.Context

type LocalSnapshot = {
	name: string,
	location: string,
	value: Record,
	resultOrdinal: number,
}

type SelectedValue = InvocationFrame.SelectedValue

type LocalTransfer = {
	targets: { Record },
	values: { Record },
	targetCount: number,
	valueCount: number,
}

type ClosureTransfers = {
	items: { LocalTransfer },
	seenLocations: { [string]: boolean },
}

type DirectClosureValue = {
	returned: Record,
	firstValue: Record?,
	snapshots: { LocalSnapshot },
	calleeSnapshot: boolean,
	resultOrdinal: number,
}

local recordArrayLength = InvocationFrame.recordArrayLength
local unwrapExpression = InvocationFrame.unwrapExpression
local localIdentity = InvocationFrame.localIdentity
local directLocalIdentity = InvocationFrame.directLocalIdentity
local selectedCallArgument = InvocationFrame.selectedCallArgument
local selectedContextVararg = InvocationFrame.selectedContextVararg
local fixedParameterContext = InvocationFrame.fixedParameterContext
local selectedVarargArgument = InvocationFrame.selectedVarargArgument
local calleeBinding = InvocationFrame.calleeBinding
local matchesDirect = TargetOriginExpressionMatcher.matchesDirect

local function directAssignmentTarget(value: any): Record?
	if type(value) ~= "table" or (value :: Record).type ~= "AstExprLocal" then
		return nil
	end
	local target = (value :: Record)["local"]
	local name, location = localIdentity(target)
	return if name ~= nil and location ~= nil then target :: Record else nil
end

local function matchesLocalIdentity(value: any, target: Record, label: string): boolean
	local sourceName, sourceLocation = directLocalIdentity(value, label)
	local targetName, targetLocation = localIdentity(target)
	return sourceName ~= nil
		and sourceLocation ~= nil
		and sourceName == targetName
		and sourceLocation == targetLocation
end

local function matchesLocalChain(
	values: { SelectedValue },
	targets: { Record },
	firstIndex: number,
	lastIndex: number
): boolean
	for index = firstIndex, lastIndex do
		if values[index].resultOrdinal ~= 1
			or not matchesLocalIdentity(
				values[index].expression,
				targets[index - 1],
				"target direct-closure local alias"
			)
		then
			return false
		end
	end
	return true
end

local function directLocalCall(value: any, target: Record, label: string): Record?
	local call = unwrapExpression(value, label)
	if call.type ~= "AstExprCall"
		or call.self ~= false
		or recordArrayLength(call.args) == nil
		or not matchesLocalIdentity(call.func, target, label .. " callee")
	then
		return nil
	end
	return call
end

local function localSnapshotConsumer(value: any, label: string): Record
	local expression = unwrapExpression(value, label)
	if expression.type == "AstExprCall"
		and expression.self == false
		and recordArrayLength(expression.args) ~= nil
		and type(expression.func) == "table"
	then
		return expression.func :: Record
	end
	return expression
end

local function directClosureTransfers(statements: { Record }, statementCount: number): ClosureTransfers?
	local transfers: { LocalTransfer } = {}
	local seenObjects: { [any]: boolean } = {}
	local seenLocations: { [string]: boolean } = {}
	local awaitingAssignment: { [string]: Record } = {}
	local awaitingCount = 0
	for index = 1, statementCount - 1 do
		local statement = statements[index] :: Record
		if statement.type == "AstStatLocalFunction" then
			local target = statement.name
			local value = statement.func
			local name, location = localIdentity(target)
			if name == nil
				or location == nil
				or type(value) ~= "table"
				or (value :: Record).type ~= "AstExprFunction"
				or seenObjects[target] == true
				or seenLocations[location :: string] == true
			then
				return nil
			end
			seenObjects[target] = true
			seenLocations[location :: string] = true
			table.insert(transfers, {
				targets = { target :: Record },
				values = { value :: Record },
				targetCount = 1,
				valueCount = 1,
			})
		elseif statement.type == "AstStatLocal" then
			local targetCount = recordArrayLength(statement.vars)
			local valueCount = recordArrayLength(statement.values)
			if targetCount == nil
				or targetCount == 0
				or targetCount > TargetOriginMatcher.maxLocalDeclarationTargets
				or valueCount == nil
				or valueCount > TargetOriginMatcher.maxLocalDeclarationValues
			then
				return nil
			end
			local targets: { Record } = {}
			for targetIndex = 1, targetCount do
				local target = statement.vars[targetIndex] :: Record
				local name, location = localIdentity(target)
				if name == nil
					or location == nil
					or seenObjects[target] == true
					or seenLocations[location :: string] == true
				then
					return nil
				end
				seenObjects[target] = true
				seenLocations[location :: string] = true
				table.insert(targets, target)
			end
			if valueCount == 0 then
				for _, target in targets do
					local _, location = localIdentity(target)
					awaitingAssignment[location :: string] = target
					awaitingCount += 1
				end
			else
				local values: { Record } = {}
				for valueIndex = 1, valueCount do
					table.insert(values, statement.values[valueIndex] :: Record)
				end
				table.insert(transfers, {
					targets = targets,
					values = values,
					targetCount = targetCount,
					valueCount = valueCount,
				})
			end
		elseif statement.type == "AstStatAssign" then
			local targetCount = recordArrayLength(statement.vars)
			local valueCount = recordArrayLength(statement.values)
			if targetCount == nil
				or targetCount == 0
				or targetCount > TargetOriginMatcher.maxLocalDeclarationTargets
				or valueCount == nil
				or valueCount == 0
				or valueCount > TargetOriginMatcher.maxLocalDeclarationValues
			then
				return nil
			end
			local targets: { Record } = {}
			local assignmentLocations: { [string]: boolean } = {}
			for targetIndex = 1, targetCount do
				local target = directAssignmentTarget(statement.vars[targetIndex])
				local _, location = localIdentity(target)
				if target == nil
					or location == nil
					or assignmentLocations[location :: string] == true
					or awaitingAssignment[location :: string] ~= target
				then
					return nil
				end
				assignmentLocations[location :: string] = true
				table.insert(targets, target :: Record)
			end
			for _, target in targets do
				local _, location = localIdentity(target)
				awaitingAssignment[location :: string] = nil
				awaitingCount -= 1
			end
			local values: { Record } = {}
			for valueIndex = 1, valueCount do
				table.insert(values, statement.values[valueIndex] :: Record)
			end
			table.insert(transfers, {
				targets = targets,
				values = values,
				targetCount = targetCount,
				valueCount = valueCount,
			})
		else
			return nil
		end
	end
	if awaitingCount ~= 0 or #transfers == 0 then
		return nil
	end
	return { items = transfers, seenLocations = seenLocations }
end

local function selectedTransferValue(transfer: LocalTransfer, targetOrdinal: number): SelectedValue?
	if targetOrdinal <= transfer.valueCount then
		return { expression = transfer.values[targetOrdinal], resultOrdinal = 1 }
	end
	local resultOrdinal = targetOrdinal - transfer.valueCount + 1
	if resultOrdinal > TargetOriginMatcher.maxDirectReturnValues then
		return nil
	end
	local expression = transfer.values[transfer.valueCount]
	if expression.type == "AstExprCall" then
		if expression.self ~= false or recordArrayLength(expression.args) == nil then
			return nil
		end
	elseif expression.type ~= "AstExprVarargs" then
		return nil
	end
	return { expression = expression, resultOrdinal = resultOrdinal }
end

local function directClosureReturnedValue(
	statements: any,
	requestedResultOrdinal: number,
	context: CalleeContext?
): DirectClosureValue?
	local selection = TargetOriginReturnSelector.select(statements, requestedResultOrdinal, context)
	if selection == nil then
		return nil
	end
	local statementCount = selection.statementCount
	local returned = selection.returned
	local returnedResultOrdinal = selection.resultOrdinal
	if statementCount == 1 then
		return {
			returned = returned,
			firstValue = nil,
			snapshots = {},
			calleeSnapshot = false,
			resultOrdinal = returnedResultOrdinal,
		}
	end
	local parsed = directClosureTransfers(statements :: { Record }, statementCount)
	if parsed == nil then
		return nil
	end
	local declarations = (parsed :: ClosureTransfers).items
	local localCount = #declarations
	local targets: { Record } = {}
	local values: { SelectedValue } = {}
	local snapshots: { LocalSnapshot } = {}
	local seenLocations = (parsed :: ClosureTransfers).seenLocations
	local consumer = localSnapshotConsumer(returned, "target direct-closure return consumer")
	for index = localCount, 1, -1 do
		local declaration = declarations[index]
		local selected: number? = nil
		for targetIndex = 1, declaration.targetCount do
			if matchesLocalIdentity(
				consumer,
				declaration.targets[targetIndex] :: Record,
				"target direct-closure selected local"
			) then
				if selected ~= nil then
					return nil
				end
				selected = targetIndex
			end
		end
		if selected == nil then
			return nil
		end
		local target = declaration.targets[selected :: number] :: Record
		local name, location = localIdentity(target)
		if name == nil or location == nil then
			return nil
		end
		local selectedValue = selectedTransferValue(declaration, selected :: number)
		if selectedValue == nil then
			return nil
		end
		local source = (selectedValue :: SelectedValue).expression
		table.insert(targets, 1, target)
		table.insert(values, 1, selectedValue :: SelectedValue)
		table.insert(snapshots, 1, {
			name = name :: string,
			location = location :: string,
			value = source,
			resultOrdinal = (selectedValue :: SelectedValue).resultOrdinal,
		})
		if index > 1 then
			consumer = localSnapshotConsumer(source, "target direct-closure snapshot consumer")
		end
	end
	local firstSourceName, firstSourceLocation = directLocalIdentity(
		values[1].expression,
		"target direct-closure first local alias"
	)
	if firstSourceName ~= nil
		and firstSourceLocation ~= nil
		and seenLocations[firstSourceLocation :: string] == true
	then
		return nil
	end
	if matchesLocalIdentity(returned, targets[localCount], "target direct-closure local return") then
		if localCount <= TargetOriginMatcher.maxLocalSnapshotDepth
			and matchesLocalChain(values, targets, 2, localCount)
		then
			return {
				returned = returned,
				firstValue = values[1].expression,
				snapshots = snapshots,
				calleeSnapshot = false,
				resultOrdinal = values[1].resultOrdinal,
			}
		end
		local resultCallIndex: number? = nil
		for index = 2, localCount do
			if directLocalCall(
				values[index].expression,
				targets[index - 1],
				"target direct-closure result snapshot"
			) ~= nil then
				if resultCallIndex ~= nil then
					return nil
				end
				resultCallIndex = index
			elseif values[index].resultOrdinal ~= 1
				or not matchesLocalIdentity(
					values[index].expression,
					targets[index - 1],
					"target direct-closure result alias"
				)
			then
				return nil
			end
		end
		if resultCallIndex == nil then
			return nil
		end
		local calleeCount = (resultCallIndex :: number) - 1
		local resultAliasCount = localCount - (resultCallIndex :: number)
		if calleeCount > TargetOriginMatcher.maxLocalSnapshotDepth
			or resultAliasCount > TargetOriginMatcher.maxResultSnapshotDepth
		then
			return nil
		end
		local calleeSnapshots: { LocalSnapshot } = {}
		for index = 1, calleeCount do
			table.insert(calleeSnapshots, snapshots[index])
		end
		return {
			returned = values[resultCallIndex :: number].expression,
			firstValue = values[1].expression,
			snapshots = calleeSnapshots,
			calleeSnapshot = true,
			resultOrdinal = values[resultCallIndex :: number].resultOrdinal,
		}
	end
	if localCount > TargetOriginMatcher.maxLocalSnapshotDepth
		or directLocalCall(returned, targets[localCount], "target direct-closure local callee return") == nil
	then
		return nil
	end
	local resultCallIndex: number? = nil
	for index = 2, localCount do
		if directLocalCall(
			values[index].expression,
			targets[index - 1],
			"target direct-closure projected callee snapshot"
		) ~= nil then
			if resultCallIndex ~= nil then
				return nil
			end
			resultCallIndex = index
		elseif values[index].resultOrdinal ~= 1
			or not matchesLocalIdentity(
				values[index].expression,
				targets[index - 1],
				"target direct-closure projected callee alias"
			)
		then
			return nil
		end
	end
	return {
		returned = returned,
		firstValue = values[1].expression,
		snapshots = snapshots,
		calleeSnapshot = true,
		resultOrdinal = returnedResultOrdinal,
	}
end

local function frameBinding(context: CalleeContext, value: any): CalleeBinding?
	local expression = unwrapExpression(value, "target direct-closure first local alias")
	if expression.type ~= "AstExprLocal" then
		return nil
	end
	local name, location = localIdentity(expression["local"])
	if name == nil or location == nil then
		return nil
	end
	for _, binding in context.bindings do
		if binding.name == name and binding.location == location then
			return binding
		end
	end
	return nil
end

local function localSnapshotContext(value: DirectClosureValue, parent: CalleeContext?): CalleeContext?
	if parent == nil or value.firstValue == nil or #value.snapshots == 0 then
		return nil
	end
	local parameter = frameBinding(parent :: CalleeContext, value.firstValue)
	local rootUseNode: Record
	if parameter ~= nil then
		if parameter.kind ~= "parameter" then
			return nil
		end
		rootUseNode = parameter.useNode
	elseif value.snapshots[1].resultOrdinal == 1
		and unwrapExpression(value.firstValue, "target direct-closure call snapshot root").type == "AstExprCall"
	then
		rootUseNode = value.firstValue :: Record
	elseif value.snapshots[1].resultOrdinal > 1
		and (value.firstValue :: Record).type == "AstExprCall"
	then
		rootUseNode = value.firstValue :: Record
	else
		local rootName, rootLocation = directLocalIdentity(
			value.firstValue,
			"target direct-closure captured snapshot root"
		)
		if rootName == nil or rootLocation == nil then
			return nil
		end
		rootUseNode = value.firstValue :: Record
	end
	local context = parent :: CalleeContext
	for _, snapshot in value.snapshots do
		context = {
			kind = "snapshot",
			parent = context,
			bindings = { {
				kind = "local_snapshot",
				name = snapshot.name,
				location = snapshot.location,
				argument = snapshot.value,
				resultOrdinal = snapshot.resultOrdinal,
				useNode = rootUseNode,
			} },
			vararg = nil,
		}
	end
	return context
end

type CalleeResolutionState = {
	resolveCallee: CalleeResolver?,
	parameterDepth: number,
	localDepth: number,
	projectedDepth: number,
	varargDepth: number,
	active: { [any]: boolean },
}

type ResultCalleeResolver = (Record, Record, number, CalleeContext?, CalleeResolutionState) -> Record?

local resolveResultCalleeAt: ResultCalleeResolver
local resolveProjectedCalleeAt: ResultCalleeResolver

local function descendBinding(state: CalleeResolutionState, kind: "parameter" | "local_snapshot"): CalleeResolutionState?
	local nextState: CalleeResolutionState = table.clone(state)
	if kind == "parameter" then
		if state.parameterDepth >= TargetOriginMatcher.maxParameterCalleeDepth then
			return nil
		end
		nextState.parameterDepth += 1
	else
		if state.localDepth >= TargetOriginMatcher.maxLocalSnapshotDepth then
			return nil
		end
		nextState.localDepth += 1
	end
	return nextState
end

local function resolveCalleeAt(
	useNode: Record,
	value: any,
	context: CalleeContext?,
	state: CalleeResolutionState
): Record?
	local callee = unwrapExpression(value, "target direct-closure callee")
	if callee.type == "AstExprFunction" then
		return callee
	end
	local binding, parent = calleeBinding(context, callee)
	if binding ~= nil then
		local nextState = descendBinding(state, binding.kind)
		if nextState == nil
			or binding.argument == nil
			or binding.resultOrdinal < 1
			or binding.resultOrdinal > TargetOriginMatcher.maxDirectReturnValues
			or state.active[binding] == true
		then
			return nil
		end
		state.active[binding] = true
		local resolved = resolveResultCalleeAt(
			binding.useNode,
			binding.argument :: Record,
			binding.resultOrdinal,
			parent,
			nextState :: CalleeResolutionState
		)
		state.active[binding] = nil
		return resolved
	elseif state.resolveCallee == nil then
		return nil
	end
	local resolved = (state.resolveCallee :: CalleeResolver)(useNode, callee)
	if resolved == nil then
		return nil
	end
	local expression = unwrapExpression(resolved, "target resolved direct-closure callee")
	return if expression.type == "AstExprFunction" then expression else nil
end

resolveResultCalleeAt = function(
	useNode: Record,
	value: Record,
	resultOrdinal: number,
	context: CalleeContext?,
	state: CalleeResolutionState
): Record?
	local selectedVararg, parent = selectedContextVararg(value, resultOrdinal, context)
	if selectedVararg ~= nil then
		if state.varargDepth >= TargetOriginMatcher.maxDirectReturnDepth then
			return nil
		end
		local nextState: CalleeResolutionState = table.clone(state)
		nextState.varargDepth += 1
		return resolveResultCalleeAt(
			useNode,
			selectedVararg.expression,
			selectedVararg.resultOrdinal,
			parent,
			nextState
		)
	end
	if resultOrdinal == 1 then
		local resolved = resolveCalleeAt(useNode, value, context, state)
		if resolved ~= nil then
			return resolved
		end
	end
	return resolveProjectedCalleeAt(useNode, value, resultOrdinal, context, state)
end

resolveProjectedCalleeAt = function(
	useNode: Record,
	value: Record,
	resultOrdinal: number,
	context: CalleeContext?,
	state: CalleeResolutionState
): Record?
	if resultOrdinal < 1
		or resultOrdinal > TargetOriginMatcher.maxDirectReturnValues
		or state.projectedDepth >= TargetOriginMatcher.maxDirectReturnDepth
	then
		return nil
	end
	local call = if resultOrdinal == 1
		then unwrapExpression(value, "target projected callable result")
		else value
	if call.type ~= "AstExprCall"
		or call.self ~= false
		or recordArrayLength(call.args) == nil
		or state.active[call] == true
	then
		return nil
	end
	state.active[call] = true
	local resolved: Record? = nil
	local callee = resolveCalleeAt(call, call.func, context, state)
	if callee ~= nil and recordArrayLength((callee :: Record).args) ~= nil then
		local body = (callee :: Record).body
		if type(body) == "table" and (body :: Record).type == "AstStatBlock" then
			local childContext = fixedParameterContext(call, callee :: Record, context)
			local returnedValue = directClosureReturnedValue((body :: Record).body, resultOrdinal, childContext)
			if returnedValue ~= nil then
				local returned = returnedValue.returned
				local returnedResultOrdinal = returnedValue.resultOrdinal
				local returnContext = childContext or context
				local contextValid = true
				if returnedValue.calleeSnapshot then
					local snapshotContext = localSnapshotContext(returnedValue, childContext)
					if snapshotContext == nil then
						contextValid = false
					else
						returnContext = snapshotContext
					end
				elseif returnedValue.firstValue ~= nil then
					returned = returnedValue.firstValue :: Record
				end
				local selectedVararg = selectedVarargArgument(
					call,
					callee :: Record,
					returned,
					returnedResultOrdinal
				)
				if selectedVararg ~= nil then
					returned = (selectedVararg :: SelectedValue).expression
					returnedResultOrdinal = (selectedVararg :: SelectedValue).resultOrdinal
					returnContext = context
				end
				if contextValid then
					local nextState: CalleeResolutionState = table.clone(state)
					nextState.projectedDepth += 1
					resolved = resolveResultCalleeAt(
						useNode,
						returned,
						returnedResultOrdinal,
						returnContext,
						nextState
					)
				end
			end
		end
	end
	state.active[call] = nil
	return resolved
end

local function directClosureReturn(
	value: any,
	resultOrdinal: number,
	resolveCallee: CalleeResolver?,
	context: CalleeContext?
): (Record?, Record?, DirectClosureValue?)
	local call = unwrapExpression(value, "target direct-closure call")
	if call.type ~= "AstExprCall" or call.self ~= false or recordArrayLength(call.args) == nil then
		return nil, nil, nil
	end
	local callee = resolveCalleeAt(call, call.func, context, {
		resolveCallee = resolveCallee,
		parameterDepth = 0,
		localDepth = 0,
		projectedDepth = 0,
		varargDepth = 0,
		active = {},
	})
	if callee == nil or recordArrayLength((callee :: Record).args) == nil then
		return nil, nil, nil
	end
	local body = (callee :: Record).body
	if type(body) ~= "table" or (body :: Record).type ~= "AstStatBlock" then
		return nil, nil, nil
	end
	local returnedValue = directClosureReturnedValue(
		(body :: Record).body,
		resultOrdinal,
		fixedParameterContext(call, callee :: Record, context)
	)
	if returnedValue == nil then
		return nil, nil, nil
	end
	return call, callee :: Record, returnedValue
end

local function returnedParameterArgument(call: Record, callee: Record, returned: Record): SelectedValue?
	local expression = unwrapExpression(returned, "target direct-closure returned parameter")
	if expression.type ~= "AstExprLocal" then
		return nil
	end
	local returnedName, returnedLocation = localIdentity(expression["local"])
	if returnedName == nil or returnedLocation == nil then
		return nil
	end
	local parameterCount = recordArrayLength(callee.args)
	local argumentCount = recordArrayLength(call.args)
	if parameterCount == nil
		or argumentCount == nil
		or parameterCount > TargetOriginMatcher.maxDirectReturnValues
		or argumentCount > TargetOriginMatcher.maxDirectReturnValues
	then
		return nil
	end
	local selected: number? = nil
	local seenObjects: { [any]: boolean } = {}
	local seenLocations: { [string]: boolean } = {}
	for index = 1, parameterCount do
		local parameter = callee.args[index] :: Record
		local name, location = localIdentity(parameter)
		if name == nil
			or location == nil
			or seenObjects[parameter] == true
			or seenLocations[location :: string] == true
		then
			return nil
		end
		seenObjects[parameter] = true
		seenLocations[location :: string] = true
		if name == returnedName and location == returnedLocation then
			if selected ~= nil then
				return nil
			end
			selected = index
		end
	end
	if selected == nil then
		return nil
	end
	return selectedCallArgument(call, argumentCount, selected :: number)
end

local function matchesAt(
	value: any,
	resultOrdinal: number,
	origin: Record,
	matchesLocal: LocalMatcher,
	resolveCallee: CalleeResolver?,
	matchesResult: ResultMatcher?,
	depth: number,
	activeCalls: { [any]: boolean },
	context: CalleeContext?
): boolean
	if resultOrdinal == 1 and matchesDirect(value, origin, matchesLocal) then
		return true
	elseif matchesResult ~= nil and (matchesResult :: ResultMatcher)(value, resultOrdinal, origin) then
		return true
	elseif depth >= TargetOriginMatcher.maxDirectReturnDepth then
		return false
	end
	local function descend(nextValue: any, nextResultOrdinal: number, nextContext: CalleeContext?): boolean
		return matchesAt(
			nextValue,
			nextResultOrdinal,
			origin,
			matchesLocal,
			resolveCallee,
			matchesResult,
			depth + 1,
			activeCalls,
			nextContext
		)
	end
	if resultOrdinal == 1 then
		local expression = unwrapExpression(value, "target conditional origin")
		if expression.type == "AstExprIfElse" then
			local selected = TargetOriginReturnSelector.selectedConditionalExpression(expression, context)
			if selected == nil then
				return false
			end
			if selected ~= expression then
				return descend(selected :: Record, 1, context)
			end
			return descend(expression.trueExpr, 1, context) and descend(expression.falseExpr, 1, context)
		end
	end
	local selectedContextValue, parentContext = selectedContextVararg(value, resultOrdinal, context)
	if selectedContextValue ~= nil then
		return descend(
			selectedContextValue.expression,
			selectedContextValue.resultOrdinal,
			parentContext
		)
	end
	local call, callee, returnedValue = directClosureReturn(value, resultOrdinal, resolveCallee, context)
	if call == nil or callee == nil or returnedValue == nil or activeCalls[call] == true then
		return false
	end
	activeCalls[call] = true
	local childContext = fixedParameterContext(call, callee, context)
	local returned = returnedValue.returned
	local returnedResultOrdinal = returnedValue.resultOrdinal
	local returnContext = childContext or context
	local selectedFromVararg = false
	if returnedValue.calleeSnapshot then
		local snapshotContext = localSnapshotContext(returnedValue, childContext)
		if snapshotContext == nil then
			activeCalls[call] = nil
			return false
		end
		returnContext = snapshotContext
	elseif returnedValue.firstValue ~= nil then
		returned = returnedValue.firstValue :: Record
	end
	local selectedVararg = selectedVarargArgument(call, callee, returned, returnedResultOrdinal)
	if selectedVararg ~= nil then
		returned = (selectedVararg :: SelectedValue).expression
		returnedResultOrdinal = (selectedVararg :: SelectedValue).resultOrdinal
		returnContext = context
		selectedFromVararg = true
	end
	local matched: boolean
	local binding: CalleeBinding? = nil
	local parent: CalleeContext? = nil
	if selectedFromVararg then
		binding, parent = calleeBinding(
			returnContext,
			unwrapExpression(returned, "target selected vararg binding")
		)
	end
	if binding ~= nil then
		matched = binding.argument ~= nil
			and binding.resultOrdinal >= 1
			and binding.resultOrdinal <= TargetOriginMatcher.maxDirectReturnValues
			and descend(
				binding.argument :: Record,
				binding.resultOrdinal,
				parent
			)
	else
		matched = descend(returned, returnedResultOrdinal, returnContext)
	end
	if not matched then
		local argument = returnedParameterArgument(call, callee, returned)
		if argument ~= nil then
			matched = descend(
				argument.expression,
				argument.resultOrdinal,
				context
			)
		end
	end
	activeCalls[call] = nil
	return matched
end

function TargetOriginMatcher.matchesResult(
	value: any,
	resultOrdinal: number,
	origin: Record,
	matchesLocal: LocalMatcher,
	resolveCallee: CalleeResolver?,
	matchesResult: ResultMatcher?
): boolean
	if resultOrdinal < 1 or resultOrdinal > TargetOriginMatcher.maxDirectReturnValues or resultOrdinal % 1 ~= 0 then
		return false
	end
	return matchesAt(value, resultOrdinal, origin, matchesLocal, resolveCallee, matchesResult, 0, {}, nil)
end

function TargetOriginMatcher.matches(
	value: any,
	origin: Record,
	matchesLocal: LocalMatcher,
	resolveCallee: CalleeResolver?,
	matchesResult: ResultMatcher?
): boolean
	return TargetOriginMatcher.matchesResult(value, 1, origin, matchesLocal, resolveCallee, matchesResult)
end

return table.freeze(TargetOriginMatcher)
