--!strict

-- Locates exact direct invocations and traces their lexical owner chain.
-- Reaching-definition and commit policy remain with the caller.

local TemporalInvocationFlow = {}

type Record = { [string]: any }

local MAX_LOCAL_VERSION_BOUNDARIES = 64

export type Position = {
	node: Record,
	owner: Record,
	statement: Record?,
	block: Record?,
	statementIndex: number?,
}

export type Model = {
	positions: { [any]: Position },
	repeatDepths: { [any]: number },
	parents: { [any]: Record },
	localUses: { [string]: { Record } },
}

export type Chain = {
	invocations: { Position },
	repeated: boolean,
}

export type InvocationSet = {
	chains: { Chain },
}

type LocalCallee = {
	value: Record,
	assignment: Position?,
	intervalDefinition: Position?,
	intervalKill: Position?,
}

type LocalBinding = {
	values: { Record },
	assignment: Position?,
	intervalDefinition: Position?,
	intervalKill: Position?,
}

type LocalValueInterval = {
	values: { Record },
	definition: Position?,
	kill: Position?,
}

type CalleeSite = {
	invocation: Position,
	localCallees: { LocalCallee },
}

type CalleeInvocationSet = {
	sites: { CalleeSite },
}

type Search = {
	activeFunctions: { [any]: boolean },
	seenAliasEdges: { [any]: boolean },
	aliasEdgeCount: number,
	maxAliasDepth: number,
	maxAliasEdges: number,
	maxSites: number,
}

local function transparentParent(index: Model, value: Record): (Record, Record?)
	local child = value
	local parent = index.parents[child]
	while parent ~= nil
		and (parent.type == "AstExprGroup" or parent.type == "AstExprTypeAssertion" or parent.type == "AstExprInstantiate")
		and parent.expr == child
	do
		child = parent
		parent = index.parents[child]
	end
	return child, parent
end

local function invocationForCallee(index: Model, value: Record): Position?
	local child, parent = transparentParent(index, value)
	if parent == nil or parent.type ~= "AstExprCall" or parent.func ~= child then
		return nil
	end
	local invocation = index.positions[parent]
	return invocation
end

local function positionPrecedes(left: Position, right: Position): boolean
	return left.owner == right.owner
		and left.block ~= nil
		and left.block == right.block
		and left.statementIndex ~= nil
		and right.statementIndex ~= nil
		and left.statementIndex < right.statementIndex
end

local function retainUniqueLocalDeclaration(
	value: any,
	seenDeclarations: { [any]: boolean },
	seenLocations: { [string]: boolean }
): boolean
	if type(value) ~= "table" or (value :: Record).type ~= "AstLocal" then
		return false
	end
	local declaration = value :: Record
	local location = declaration.location
	if type(location) ~= "string"
		or location == ""
		or seenDeclarations[declaration] == true
		or seenLocations[location] == true
	then
		return false
	end
	seenDeclarations[declaration] = true
	seenLocations[location] = true
	return true
end

local function directLocalAssignmentTargets(statement: Record): { Record }?
	local variables = statement.vars
	local values = statement.values
	if type(variables) ~= "table" or type(values) ~= "table" or #variables == 0 or #values == 0 then
		return nil
	end
	local seenDeclarations: { [any]: boolean } = {}
	local seenLocations: { [string]: boolean } = {}
	for _, targetValue in variables do
		if type(targetValue) ~= "table" then
			return nil
		end
		local target = targetValue :: Record
		if target.type ~= "AstExprLocal"
			or not retainUniqueLocalDeclaration(target["local"], seenDeclarations, seenLocations)
		then
			return nil
		end
	end
	for _, assignedValue in values do
		if type(assignedValue) ~= "table" or type((assignedValue :: Record).type) ~= "string" then
			return nil
		end
	end
	return variables :: { Record }
end

local function directLocalFunctionStatementTarget(statement: Record): Record?
	local target = statement.name
	local functionValue = statement.func
	if type(target) ~= "table"
		or (target :: Record).type ~= "AstExprLocal"
		or type((target :: Record)["local"]) ~= "table"
		or type(functionValue) ~= "table"
		or (functionValue :: Record).type ~= "AstExprFunction"
	then
		return nil
	end
	return target :: Record
end

local function localVersionBoundary(index: Model, value: Record): Position?
	local parent = index.parents[value]
	if parent == nil then
		return nil
	elseif parent.type == "AstStatFunction" then
		return if directLocalFunctionStatementTarget(parent) == value then index.positions[parent] else nil
	elseif parent.type ~= "AstStatAssign" then
		return nil
	end
	local variables = directLocalAssignmentTargets(parent)
	if variables == nil then
		return nil
	end
	local targetCount = 0
	for _, target in variables do
		if target == value then
			targetCount += 1
		end
	end
	if targetCount ~= 1 then
		return nil
	end
	return index.positions[parent]
end

local function isUnsupportedLocalWriteTarget(index: Model, value: Record): boolean
	local parent = index.parents[value]
	if parent == nil then
		return false
	elseif parent.type == "AstStatCompoundAssign" then
		return parent.var == value
	elseif parent.type == "AstStatFunction" then
		return parent.name == value and directLocalFunctionStatementTarget(parent) == nil
	elseif parent.type ~= "AstStatAssign" then
		return false
	end
	local variables = parent.vars
	if type(variables) ~= "table" then
		return false
	end
	local targetCount = 0
	for _, target in variables do
		if target == value then
			targetCount += 1
		end
	end
	if targetCount == 0 then
		return false
	end
	return targetCount ~= 1 or directLocalAssignmentTargets(parent) == nil
end

local function localValueIntervalUses(
	index: Model,
	uses: { Record },
	assignmentTarget: Record?,
	definitionPosition: Position
): LocalValueInterval?
	local boundaries: { Position } = {}
	local boundaryIndices: { [number]: boolean } = {}
	local nearestKill: Position? = nil
	for _, use in uses do
		if use ~= assignmentTarget then
			if isUnsupportedLocalWriteTarget(index, use) then
				return nil
			end
			local boundary = localVersionBoundary(index, use)
			if boundary ~= nil then
				if not positionPrecedes(boundary, definitionPosition)
					and not positionPrecedes(definitionPosition, boundary)
				then
					return nil
				elseif #boundaries == MAX_LOCAL_VERSION_BOUNDARIES then
					return nil
				end
				local statementIndex = boundary.statementIndex
				assert(statementIndex ~= nil, "ordered local version boundary has no statement index")
				if boundaryIndices[statementIndex] == true then
					return nil
				end
				boundaryIndices[statementIndex] = true
				table.insert(boundaries, boundary)
				if positionPrecedes(definitionPosition, boundary)
					and (nearestKill == nil or positionPrecedes(boundary, nearestKill :: Position))
				then
					nearestKill = boundary
				end
			end
		end
	end

	local values: { Record } = {}
	if #boundaries == 0 then
		for _, use in uses do
			if use ~= assignmentTarget then
				table.insert(values, use)
			end
		end
		return if #values == 0
			then nil
			else { values = values, definition = nil, kill = nil }
	end
	for _, use in uses do
		if use ~= assignmentTarget and localVersionBoundary(index, use) == nil then
			local usePosition = index.positions[use]
			if usePosition == nil then
				return nil
			elseif usePosition.owner ~= definitionPosition.owner then
				if usePosition.owner.type ~= "AstExprFunction" then
					return nil
				end
				table.insert(values, use)
			elseif positionPrecedes(usePosition, definitionPosition) then
				-- This use belongs to an older value of the same local.
			elseif not positionPrecedes(definitionPosition, usePosition) then
				return nil
			elseif nearestKill == nil or positionPrecedes(usePosition, nearestKill :: Position) then
				table.insert(values, use)
			elseif not positionPrecedes(nearestKill :: Position, usePosition) then
				return nil
			end
		end
	end
	return if #values == 0
		then nil
		else { values = values, definition = definitionPosition, kill = nearestKill }
end

local function fixedResultOrdinal(statement: Record, child: Record): number?
	local values = statement.values
	if type(values) ~= "table" or #values == 0 then
		return nil
	end
	local ordinal: number? = nil
	for index = 1, #values do
		local value = values[index]
		if type(value) ~= "table" or type((value :: Record).type) ~= "string" then
			return nil
		elseif value == child then
			if ordinal ~= nil then
				return nil
			end
			ordinal = index
		end
	end
	return ordinal
end

local function localBinding(index: Model, functionValue: Record): LocalBinding?
	if functionValue.type ~= "AstExprFunction" and functionValue.type ~= "AstExprLocal" then
		return nil
	end
	local child, parent = transparentParent(index, functionValue)
	local declaration: any = nil
	local assignmentTarget: Record? = nil
	local assignmentPosition: Position? = nil
	local definitionPosition: Position? = nil
	if parent ~= nil and parent.type == "AstStatLocal" then
		local variables = parent.vars
		local ordinal = fixedResultOrdinal(parent, child)
		if type(variables) ~= "table" or #variables == 0 or ordinal == nil or ordinal > #variables then
			return nil
		end
		local seenDeclarations: { [any]: boolean } = {}
		local seenLocations: { [string]: boolean } = {}
		for index = 1, #variables do
			if not retainUniqueLocalDeclaration(variables[index], seenDeclarations, seenLocations) then
				return nil
			end
		end
		declaration = variables[ordinal]
		definitionPosition = index.positions[parent]
	elseif parent ~= nil and parent.type == "AstStatLocalFunction" and parent.func == child then
		declaration = parent.name
		definitionPosition = index.positions[parent]
	elseif parent ~= nil and parent.type == "AstStatFunction" and parent.func == child then
		local target = directLocalFunctionStatementTarget(parent)
		if target == nil then
			return nil
		end
		declaration = target["local"]
		assignmentTarget = target
		assignmentPosition = index.positions[parent]
		definitionPosition = assignmentPosition
	elseif parent ~= nil and parent.type == "AstStatAssign" then
		local variables = directLocalAssignmentTargets(parent)
		local ordinal = fixedResultOrdinal(parent, child)
		if variables == nil or ordinal == nil or ordinal > #variables then
			return nil
		end
		local target = variables[ordinal]
		declaration = target["local"]
		assignmentTarget = target
		assignmentPosition = index.positions[parent]
		definitionPosition = assignmentPosition
	else
		return nil
	end
	if type(declaration) ~= "table" or declaration.type ~= "AstLocal" then
		return nil
	end
	local location = declaration.location
	if type(location) ~= "string" or location == "" then
		return nil
	end
	local uses = index.localUses[location]
	if uses == nil then
		return nil
	end
	if definitionPosition == nil or (assignmentTarget ~= nil and assignmentPosition == nil) then
		return nil
	end
	local interval = localValueIntervalUses(index, uses, assignmentTarget, definitionPosition :: Position)
	if interval == nil then
		return nil
	end
	return {
		values = interval.values,
		assignment = assignmentPosition,
		intervalDefinition = interval.definition,
		intervalKill = interval.kill,
	}
end
local function assignmentPrecedesUse(index: Model, localCallee: LocalCallee, invocations: { Position }): boolean
	local assignment = localCallee.assignment
	if assignment == nil then
		return true
	end
	local use = index.positions[localCallee.value]
	if use == nil then
		return false
	elseif assignment.owner == use.owner then
		return positionPrecedes(assignment, use)
	end
	local reachedUseOwner = false
	for _, invocation in invocations do
		reachedUseOwner = reachedUseOwner or invocation.owner == use.owner
		if reachedUseOwner and invocation.owner == assignment.owner then
			return positionPrecedes(assignment, invocation)
		end
	end
	return false
end

local function useOccursInVersion(index: Model, localCallee: LocalCallee, invocations: { Position }): boolean
	if not assignmentPrecedesUse(index, localCallee, invocations) then
		return false
	end
	local definition = localCallee.intervalDefinition
	if definition == nil then
		return true
	end
	local use = index.positions[localCallee.value]
	if use == nil then
		return false
	end
	local point: Position? = if use.owner == definition.owner then use else nil
	if point == nil then
		local reachedUseOwner = false
		for _, invocation in invocations do
			reachedUseOwner = reachedUseOwner or invocation.owner == use.owner
			if reachedUseOwner and invocation.owner == definition.owner then
				point = invocation
				break
			end
		end
	end
	if point == nil or not positionPrecedes(definition, point :: Position) then
		return false
	end
	local kill = localCallee.intervalKill
	return kill == nil or positionPrecedes(point :: Position, kill)
end

local function copyLocalCallees(values: { LocalCallee }): { LocalCallee }
	local result: { LocalCallee } = {}
	for _, value in values do
		table.insert(result, value)
	end
	return result
end

local function calleeInvocationSet(
	index: Model,
	functionValue: Record,
	search: Search
): CalleeInvocationSet?
	local invocation = invocationForCallee(index, functionValue)
	if invocation ~= nil then
		return { sites = { { invocation = invocation, localCallees = {} } } }
	end
	local sites: { CalleeSite } = {}
	local seenValues: { [any]: boolean } = {}
	local function visit(value: Record, localCallees: { LocalCallee }, aliasDepth: number): boolean
		local binding = localBinding(index, value)
		if binding == nil or #binding.values > search.maxSites + search.maxAliasEdges then
			return false
		end
		local initialSiteCount = #sites
		for _, value in binding.values do
			if seenValues[value] == true then
				return false
			end
			seenValues[value] = true
			local localCallee: LocalCallee = {
				value = value,
				assignment = binding.assignment,
				intervalDefinition = binding.intervalDefinition,
				intervalKill = binding.intervalKill,
			}
			invocation = invocationForCallee(index, value)
			if invocation == nil then
				if aliasDepth == search.maxAliasDepth then
					return false
				end
				if search.seenAliasEdges[value] ~= true then
					if search.aliasEdgeCount == search.maxAliasEdges then
						return false
					end
					search.seenAliasEdges[value] = true
					search.aliasEdgeCount += 1
				end
				local transferPath = copyLocalCallees(localCallees)
				table.insert(transferPath, localCallee)
				if not visit(value, transferPath, aliasDepth + 1) then
					return false
				end
			elseif (index.repeatDepths[invocation.node] or 0) > 0 then
				return false
			else
				if #sites == search.maxSites then
					return false
				end
				local siteCallees = copyLocalCallees(localCallees)
				table.insert(siteCallees, localCallee)
				table.insert(sites, { invocation = invocation, localCallees = siteCallees })
			end
		end
		return #sites > initialSiteCount
	end
	return if visit(functionValue, {}, 0) then { sites = sites } else nil
end

local directInvocationSet: (Model, Record, number, Search) -> InvocationSet?
local traceToOwnerSetInternal: (Model, Record, Record, number, Search) -> InvocationSet?

traceToOwnerSetInternal = function(
	index: Model,
	functionOwner: Record,
	owner: Record,
	maxDepth: number,
	search: Search
): InvocationSet?
	local segments = directInvocationSet(index, functionOwner, maxDepth, search)
	if segments == nil then
		return nil
	end
	local chains: { Chain } = {}
	for _, segment in segments.chains do
		local outerInvocation = segment.invocations[#segment.invocations]
		assert(outerInvocation ~= nil, "direct invocation segment has no outer point")
		if outerInvocation.owner == owner then
			table.insert(chains, segment)
		elseif outerInvocation.owner.type ~= "AstExprFunction" then
			return nil
		else
			local remainingDepth = maxDepth - #segment.invocations
			if remainingDepth < 1 then
				return nil
			end
			local outerSet = traceToOwnerSetInternal(index, outerInvocation.owner, owner, remainingDepth, search)
			if outerSet == nil then
				return nil
			end
			for _, outerChain in outerSet.chains do
				if #chains == search.maxSites then
					return nil
				end
				local invocations = table.clone(segment.invocations)
				for _, invocation in outerChain.invocations do
					table.insert(invocations, invocation)
				end
				table.insert(chains, {
					invocations = invocations,
					repeated = segment.repeated or outerChain.repeated,
				})
			end
		end
	end
	return if #chains == 0 then nil else { chains = chains }
end

directInvocationSet = function(index: Model, functionValue: Record, maxDepth: number, search: Search): InvocationSet?
	if maxDepth < 1 or functionValue.type ~= "AstExprFunction" or search.activeFunctions[functionValue] == true then
		return nil
	end
	local functionPosition = index.positions[functionValue]
	if functionPosition == nil then
		return nil
	end
	search.activeFunctions[functionValue] = true
	local function build(): InvocationSet?
		local callees = calleeInvocationSet(index, functionValue, search)
		if callees == nil then
			return nil
		end
		local chains: { Chain } = {}
		for _, callee in callees.sites do
			local suffixes: { Chain }
			if callee.invocation.owner == functionPosition.owner then
				suffixes = { { invocations = {}, repeated = false } }
			else
				if callee.invocation.owner.type ~= "AstExprFunction" or maxDepth == 1 then
					return nil
				end
				local callerSet = traceToOwnerSetInternal(
					index,
					callee.invocation.owner,
					functionPosition.owner,
					maxDepth - 1,
					search
				)
				if callerSet == nil then
					return nil
				end
				suffixes = callerSet.chains
			end
			for _, suffix in suffixes do
				if #chains == search.maxSites then
					return nil
				end
				local invocations: { Position } = { callee.invocation }
				for _, invocation in suffix.invocations do
					table.insert(invocations, invocation)
				end
				for _, localCallee in callee.localCallees do
					if not useOccursInVersion(index, localCallee, invocations) then
						return nil
					end
				end
				table.insert(chains, {
					invocations = invocations,
					repeated = (index.repeatDepths[callee.invocation.node] or 0) > 0 or suffix.repeated,
				})
			end
		end
		if #chains == 0 then
				return nil
		end
		return { chains = chains }
	end
	local invocationSet = build()
	search.activeFunctions[functionValue] = nil
	return invocationSet
end

function TemporalInvocationFlow.directInvocationPoint(
	index: Model,
	functionValue: Record,
	maxAliasDepth: number
): Position?
	local invocationSet = directInvocationSet(index, functionValue, maxAliasDepth, {
		activeFunctions = {},
		seenAliasEdges = {},
		aliasEdgeCount = 0,
		maxAliasDepth = maxAliasDepth,
		maxAliasEdges = maxAliasDepth,
		maxSites = 1,
	})
	local chain = if invocationSet == nil then nil else invocationSet.chains[1]
	return if chain == nil then nil else chain.invocations[1]
end

function TemporalInvocationFlow.traceToOwner(
	index: Model,
	functionOwner: Record,
	owner: Record,
	maxDepth: number
): Chain?
	local invocationSet = traceToOwnerSetInternal(index, functionOwner, owner, maxDepth, {
		activeFunctions = {},
		seenAliasEdges = {},
		aliasEdgeCount = 0,
		maxAliasDepth = maxDepth,
		maxAliasEdges = maxDepth,
		maxSites = 1,
	})
	return if invocationSet == nil then nil else invocationSet.chains[1]
end

function TemporalInvocationFlow.traceSetToOwner(
	index: Model,
	functionOwner: Record,
	owner: Record,
	maxDepth: number,
	maxSites: number
): InvocationSet?
	if maxSites < 1 then
		return nil
	end
	return traceToOwnerSetInternal(index, functionOwner, owner, maxDepth, {
		activeFunctions = {},
		seenAliasEdges = {},
		aliasEdgeCount = 0,
		maxAliasDepth = maxDepth,
		maxAliasEdges = maxDepth,
		maxSites = maxSites,
	})
end

return table.freeze(TemporalInvocationFlow)
