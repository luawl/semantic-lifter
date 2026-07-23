--!strict

-- Computes feasible last-definition indices at one structured source point.
-- Identity, origin, and mutation policy remain with the temporal proof owner.

local StructuredDefinitionSets = {}

type Record = { [string]: any }

export type Position = {
	node: Record,
	owner: Record,
	statement: Record?,
	block: Record?,
	statementIndex: number?,
}

export type Model = {
	positions: { [any]: Position },
	blockParents: { [any]: Record },
}

export type Candidate = {
	owner: Record,
	statement: Record?,
	repeated: boolean,
}

type Flow = {
	candidates: { number },
	fallthrough: boolean,
	breakCandidates: { number },
	continueCandidates: { number },
	breaks: boolean,
	continues: boolean,
	supported: boolean,
}

type LoopSummary = {
	entryCandidates: { number },
	conditionCandidates: { number },
	conditionExists: boolean,
	exits: Flow,
}

local function copyCandidates(values: { number }): { number }
	local result: { number } = {}
	for _, value in values do
		table.insert(result, value)
	end
	return result
end

local function copyFlow(flow: Flow): Flow
	return {
		candidates = copyCandidates(flow.candidates),
		fallthrough = flow.fallthrough,
		breakCandidates = copyCandidates(flow.breakCandidates),
		continueCandidates = copyCandidates(flow.continueCandidates),
		breaks = flow.breaks,
		continues = flow.continues,
		supported = flow.supported,
	}
end

local function unsupported(): Flow
	return {
		candidates = {},
		fallthrough = false,
		breakCandidates = {},
		continueCandidates = {},
		breaks = false,
		continues = false,
		supported = false,
	}
end

local function candidateFlow(index: number): Flow
	return {
		candidates = { index },
		fallthrough = true,
		breakCandidates = {},
		continueCandidates = {},
		breaks = false,
		continues = false,
		supported = true,
	}
end

local function normalFlow(candidates: { number }, fallthrough: boolean): Flow
	return {
		candidates = copyCandidates(candidates),
		fallthrough = fallthrough,
		breakCandidates = {},
		continueCandidates = {},
		breaks = false,
		continues = false,
		supported = true,
	}
end

local function mergeCandidateSets(left: { number }, right: { number }): { number }
	local merged = copyCandidates(left)
	local present: { [number]: boolean } = {}
	for _, index in merged do
		present[index] = true
	end
	for _, index in right do
		if present[index] ~= true then
			present[index] = true
			table.insert(merged, index)
		end
	end
	return merged
end

local function mergeFlows(left: Flow, right: Flow): Flow
	if not left.supported or not right.supported then
		return unsupported()
	end
	local candidates: { number } = {}
	if left.fallthrough then
		candidates = copyCandidates(left.candidates)
	end
	if right.fallthrough then
		candidates = mergeCandidateSets(candidates, right.candidates)
	end
	return {
		candidates = candidates,
		fallthrough = left.fallthrough or right.fallthrough,
		breakCandidates = mergeCandidateSets(left.breakCandidates, right.breakCandidates),
		continueCandidates = mergeCandidateSets(left.continueCandidates, right.continueCandidates),
		breaks = left.breaks or right.breaks,
		continues = left.continues or right.continues,
		supported = true,
	}
end

local function sameCandidates(left: { number }, right: { number }): boolean
	if #left ~= #right then
		return false
	end
	local present: { [number]: boolean } = {}
	for _, index in left do
		present[index] = true
	end
	for _, index in right do
		if present[index] ~= true then
			return false
		end
	end
	return true
end

local flowFullBlock: ({ [any]: number }, Record, Flow) -> Flow
local flowFullStatement: ({ [any]: number }, Record, Flow) -> Flow
local flowLoop: ({ [any]: number }, Record, Flow, boolean) -> Flow
local advanceFlow: ({ [any]: number }, Record, Flow) -> Flow
local solveLoop: ({ [any]: number }, Record, Flow, boolean) -> LoopSummary?

flowFullStatement = function(byStatement: { [any]: number }, statement: Record, incoming: Flow): Flow
	if not incoming.supported or not incoming.fallthrough then
		return incoming
	end
	local candidateIndex = byStatement[statement]
	if candidateIndex ~= nil then
		return candidateFlow(candidateIndex)
	end

	local kind = statement.type
	if kind == "AstStatIf" then
		if type(statement.thenbody) ~= "table" or statement.thenbody.type ~= "AstStatBlock" then
			return unsupported()
		end
		local thenFlow = flowFullBlock(byStatement, statement.thenbody :: Record, copyFlow(incoming))
		local elseFlow = copyFlow(incoming)
		if statement.elsebody ~= nil then
			if type(statement.elsebody) ~= "table" then
				return unsupported()
			end
			local elseNode = statement.elsebody :: Record
			if elseNode.type == "AstStatBlock" then
				elseFlow = flowFullBlock(byStatement, elseNode, copyFlow(incoming))
			elseif elseNode.type == "AstStatIf" then
				elseFlow = flowFullStatement(byStatement, elseNode, copyFlow(incoming))
			else
				return unsupported()
			end
		end
		return mergeFlows(thenFlow, elseFlow)
	elseif kind == "AstStatDo" or kind == "AstStatBlock" then
		local body = if kind == "AstStatBlock" then statement else statement.body
		if type(body) ~= "table" or body.type ~= "AstStatBlock" then
			return unsupported()
		end
		return flowFullBlock(byStatement, body :: Record, incoming)
	elseif kind == "AstStatWhile" or kind == "AstStatRepeat" or kind == "AstStatFor" or kind == "AstStatForIn" then
		if type(statement.body) ~= "table" or statement.body.type ~= "AstStatBlock" then
			return unsupported()
		end
		return flowLoop(byStatement, statement.body :: Record, incoming, kind == "AstStatRepeat")
	elseif kind == "AstStatReturn" then
		return {
			candidates = {},
			fallthrough = false,
			breakCandidates = {},
			continueCandidates = {},
			breaks = false,
			continues = false,
			supported = true,
		}
	elseif kind == "AstStatBreak" then
		return {
			candidates = {},
			fallthrough = false,
			breakCandidates = copyCandidates(incoming.candidates),
			continueCandidates = {},
			breaks = true,
			continues = false,
			supported = true,
		}
	elseif kind == "AstStatContinue" then
		return {
			candidates = {},
			fallthrough = false,
			breakCandidates = {},
			continueCandidates = copyCandidates(incoming.candidates),
			breaks = false,
			continues = true,
			supported = true,
		}
	end
	return incoming
end

advanceFlow = function(byStatement: { [any]: number }, statement: Record, incoming: Flow): Flow
	if not incoming.supported or not incoming.fallthrough then
		return incoming
	end
	local result = flowFullStatement(byStatement, statement, {
		candidates = copyCandidates(incoming.candidates),
		fallthrough = true,
		breakCandidates = {},
		continueCandidates = {},
		breaks = false,
		continues = false,
		supported = true,
	})
	if not result.supported then
		return unsupported()
	end
	result.breakCandidates = mergeCandidateSets(incoming.breakCandidates, result.breakCandidates)
	result.continueCandidates = mergeCandidateSets(incoming.continueCandidates, result.continueCandidates)
	result.breaks = incoming.breaks or result.breaks
	result.continues = incoming.continues or result.continues
	return result
end

local function finishLoop(
	incoming: Flow,
	state: { number },
	breakCandidates: { number },
	hasBreak: boolean,
	conditionExitCandidates: { number },
	hasConditionExit: boolean,
	executesAtLeastOnce: boolean
): LoopSummary
	local conditionCandidates = if executesAtLeastOnce then conditionExitCandidates else state
	local conditionExists = if executesAtLeastOnce then hasConditionExit else incoming.fallthrough
	local exits = mergeCandidateSets(conditionCandidates, breakCandidates)
	return {
		entryCandidates = copyCandidates(state),
		conditionCandidates = copyCandidates(conditionCandidates),
		conditionExists = conditionExists,
		exits = normalFlow(exits, conditionExists or hasBreak),
	}
end

solveLoop = function(byStatement: { [any]: number }, body: Record, incoming: Flow, executesAtLeastOnce: boolean): LoopSummary?
	local state = copyCandidates(incoming.candidates)
	local breakCandidates: { number } = {}
	local conditionExitCandidates: { number } = {}
	local hasBreak = false
	local hasConditionExit = false
	local candidateLimit = 1
	for _ in byStatement do
		candidateLimit += 1
	end
	for _ = 1, candidateLimit do
		local bodyFlow = flowFullBlock(byStatement, body, {
			candidates = copyCandidates(state),
			fallthrough = true,
			breakCandidates = {},
			continueCandidates = {},
			breaks = false,
			continues = false,
			supported = true,
		})
		if not bodyFlow.supported then
			return nil
		end
		breakCandidates = mergeCandidateSets(breakCandidates, bodyFlow.breakCandidates)
		hasBreak = hasBreak or bodyFlow.breaks
		local backedgeCandidates = copyCandidates(bodyFlow.continueCandidates)
		if bodyFlow.fallthrough then
			backedgeCandidates = mergeCandidateSets(backedgeCandidates, bodyFlow.candidates)
		end
		local hasBackedge = bodyFlow.fallthrough or bodyFlow.continues
		if executesAtLeastOnce and hasBackedge then
			conditionExitCandidates = mergeCandidateSets(conditionExitCandidates, backedgeCandidates)
			hasConditionExit = true
		end
		if not hasBackedge then
			return finishLoop(
				incoming,
				state,
				breakCandidates,
				hasBreak,
				conditionExitCandidates,
				hasConditionExit,
				executesAtLeastOnce
			)
		end
		local nextState = mergeCandidateSets(state, backedgeCandidates)
		if sameCandidates(nextState, state) then
			return finishLoop(
				incoming,
				nextState,
				breakCandidates,
				hasBreak,
				conditionExitCandidates,
				hasConditionExit,
				executesAtLeastOnce
			)
		end
		state = nextState
	end
	return nil
end

flowLoop = function(byStatement: { [any]: number }, body: Record, incoming: Flow, executesAtLeastOnce: boolean): Flow
	local summary = solveLoop(byStatement, body, incoming, executesAtLeastOnce)
	return if summary == nil then unsupported() else (summary :: LoopSummary).exits
end

flowFullBlock = function(byStatement: { [any]: number }, block: Record, incoming: Flow): Flow
	if type(block.body) ~= "table" then
		return unsupported()
	end
	local flow = copyFlow(incoming)
	for _, value in block.body do
		if type(value) ~= "table" then
			return unsupported()
		end
		flow = advanceFlow(byStatement, value :: Record, flow)
		if not flow.supported or not flow.fallthrough then
			break
		end
	end
	return flow
end

local function pointPath(model: Model, point: Position): { [any]: number }?
	local path: { [any]: number } = {}
	local statement = point.statement
	while statement ~= nil do
		local position = model.positions[statement]
		if position == nil or position.block == nil or position.statementIndex == nil then
			return nil
		end
		path[position.block] = position.statementIndex
		statement = model.blockParents[position.block]
	end
	return path
end

local function containsPathBlock(value: any, path: { [any]: number }): boolean
	if type(value) ~= "table" then
		return false
	end
	local node = value :: Record
	if node.type == "AstStatBlock" then
		return path[node] ~= nil
	elseif node.type == "AstExprFunction" then
		return false
	end
	for key, child in node do
		if key ~= "local" and containsPathBlock(child, path) then
			return true
		end
	end
	return false
end

local flowToPointBlock: ({ [any]: number }, { [any]: number }, Record, Flow) -> Flow
local flowToPointStatement: ({ [any]: number }, { [any]: number }, Record, Flow) -> Flow

flowToPointStatement = function(
	byStatement: { [any]: number },
	path: { [any]: number },
	statement: Record,
	incoming: Flow
): Flow
	local kind = statement.type
	if kind == "AstStatIf" then
		if type(statement.thenbody) == "table" and containsPathBlock(statement.thenbody, path) then
			return flowToPointBlock(byStatement, path, statement.thenbody :: Record, incoming)
		elseif type(statement.elsebody) == "table" and containsPathBlock(statement.elsebody, path) then
			local elseNode = statement.elsebody :: Record
			if elseNode.type == "AstStatBlock" then
				return flowToPointBlock(byStatement, path, elseNode, incoming)
		elseif elseNode.type == "AstStatIf" then
				return flowToPointStatement(byStatement, path, elseNode, incoming)
			end
			return unsupported()
		end
	elseif kind == "AstStatDo" and type(statement.body) == "table" and containsPathBlock(statement.body, path) then
		return flowToPointBlock(byStatement, path, statement.body :: Record, incoming)
	elseif kind == "AstStatWhile" or kind == "AstStatRepeat" or kind == "AstStatFor" or kind == "AstStatForIn" then
		if type(statement.body) ~= "table" or statement.body.type ~= "AstStatBlock" then
			return unsupported()
		end
		local body = statement.body :: Record
		local pointInBody = containsPathBlock(body, path)
		if not pointInBody and (kind == "AstStatFor" or kind == "AstStatForIn") then
			-- Numeric and generic controls execute once before any backedge.
			return incoming
		end
		local summary = solveLoop(byStatement, body, incoming, kind == "AstStatRepeat")
		if summary == nil then
			return unsupported()
		end
		local loop = summary :: LoopSummary
		if pointInBody then
			return flowToPointBlock(byStatement, path, body, normalFlow(loop.entryCandidates, true))
		elseif kind == "AstStatRepeat" then
			return normalFlow(loop.conditionCandidates, loop.conditionExists)
		end
		return normalFlow(loop.entryCandidates, incoming.fallthrough)
	end
	-- The point is in this statement's expression, before its own write commits.
	return incoming
end

flowToPointBlock = function(
	byStatement: { [any]: number },
	path: { [any]: number },
	block: Record,
	incoming: Flow
): Flow
	local stopIndex = path[block]
	if stopIndex == nil or type(block.body) ~= "table" then
		return unsupported()
	end
	local flow = copyFlow(incoming)
	for index = 1, stopIndex - 1 do
		local value = block.body[index]
		if type(value) ~= "table" then
			return unsupported()
		end
		flow = advanceFlow(byStatement, value :: Record, flow)
		if not flow.supported or not flow.fallthrough then
			return flow
		end
	end
	local statement = block.body[stopIndex]
	if type(statement) ~= "table" then
		return unsupported()
	end
	return flowToPointStatement(byStatement, path, statement :: Record, flow)
end

function StructuredDefinitionSets.find(
	model: Model,
	owner: Record,
	point: Position,
	candidates: { Candidate }
): { number }?
	local ownerBlock: Record?
	if owner.type == "AstStatBlock" then
		ownerBlock = owner
	elseif type(owner.body) == "table" and owner.body.type == "AstStatBlock" then
		ownerBlock = owner.body :: Record
	end
	if ownerBlock == nil or point.owner ~= owner then
		return nil
	end

	local byStatement: { [any]: number } = {}
	local initial: { number } = {}
	for index, candidate in candidates do
		if candidate.owner ~= owner then
			return nil
		elseif candidate.statement == nil then
			table.insert(initial, index)
		elseif byStatement[candidate.statement] ~= nil then
			return nil
		else
			byStatement[candidate.statement] = index
		end
	end

	local path = pointPath(model, point)
	if path == nil or path[ownerBlock :: Record] == nil then
		return nil
	end
	local result = flowToPointBlock(
		byStatement,
		path :: { [any]: number },
		ownerBlock :: Record,
		{
			candidates = initial,
			fallthrough = true,
			breakCandidates = {},
			continueCandidates = {},
			breaks = false,
			continues = false,
			supported = true,
		}
	)
	if not result.supported or not result.fallthrough or #result.candidates == 0 then
		return nil
	end
	return result.candidates
end

return table.freeze(StructuredDefinitionSets)
