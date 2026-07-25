--!strict

-- Proves that an authenticated local target denotes one existing source write
-- at a call. The proof is frontend-private; lowering reuses the local binding
-- or place and never evaluates the defining expression again.

local TargetOriginMatcher = require("./target_origin_matcher")
local StructuredDefinitionSets = require("./structured_definition_sets")
local TemporalAliasGraph = require("./temporal_alias_graph")
local TemporalCalleeResolver = require("./temporal_callee_resolver")
local TemporalInvocationFlow = require("./temporal_invocation_flow")
local TemporalSourceIndex = require("./temporal_source_index")

local TemporalTargetIdentity = {}
TemporalTargetIdentity.maxAliasDepth = 64
TemporalTargetIdentity.maxAliasCandidates = 256
TemporalTargetIdentity.maxInvocationDepth = 64
TemporalTargetIdentity.maxInvocationSites = 64
TemporalTargetIdentity.maxLocalCalleeDefinitions = 64

type Record = TemporalSourceIndex.Record
type Position = TemporalSourceIndex.Position
type Declaration = TemporalSourceIndex.Declaration
type Definition = TemporalSourceIndex.Definition
export type ResultMatcher = TargetOriginMatcher.ResultMatcher

type StructuredCandidate = {
	owner: Record,
	statement: Record?,
	repeated: boolean,
}

type Index = TemporalSourceIndex.Index

type AncestryEntry = {
	block: Record,
	statementIndex: number,
}

export type Proof = {
	binding_kind: "value" | "place",
	declaration: Record,
	alias_depth: number,
	definition_count: number,
	definition_kind: string,
	definition_location: string,
	call_location: string,
}

export type Analysis = Index

local function expectRecord(value: any, label: string): Record
	assert(type(value) == "table", `{label} must be an AST object`)
	return value :: Record
end

local function expectLocation(value: any, label: string): string
	assert(type(value) == "string" and value ~= "", `{label} must have a source location`)
	return value
end

local declarationLocation = TemporalSourceIndex.declarationLocation
local isRepeatedStatement = TemporalSourceIndex.isRepeatedStatement

local function ancestry(index: Index, position: Position): { AncestryEntry }
	local entries: { AncestryEntry } = {}
	local statement = position.statement
	while statement ~= nil do
		local statementPosition = index.positions[statement]
		if statementPosition == nil or statementPosition.block == nil or statementPosition.statementIndex == nil then
			break
		end
		table.insert(entries, {
			block = statementPosition.block,
			statementIndex = statementPosition.statementIndex,
		})
		statement = index.blockParents[statementPosition.block]
	end
	return entries
end

local function definitionDominates(index: Index, definition: Definition, point: Position): boolean
	if definition.owner ~= point.owner or definition.repeated then
		return false
	elseif definition.statement == nil then
		return true
	elseif definition.block == nil or definition.statementIndex == nil then
		return false
	end
	for _, entry in ancestry(index, point) do
		if entry.block == definition.block then
			return definition.statementIndex < entry.statementIndex
		end
	end
	return false
end

local function definitionIsBefore(index: Index, left: Definition, right: Definition): boolean
	if left.owner ~= right.owner or left.repeated or right.repeated then
		return false
	elseif left.statement == nil then
		return right.statement ~= nil
	elseif right.statement == nil then
		return false
	end
	local leftPosition = index.positions[left.statement]
	local rightPosition = index.positions[right.statement]
	if leftPosition == nil or rightPosition == nil then
		return false
	end
	for _, leftEntry in ancestry(index, leftPosition) do
		for _, rightEntry in ancestry(index, rightPosition) do
			if leftEntry.block == rightEntry.block then
				return leftEntry.statementIndex < rightEntry.statementIndex
			end
		end
	end
	return false
end

local function pointInOwner(index: Index, node: Record, owner: Record): Position?
	local position = index.positions[node]
	while position ~= nil and position.owner ~= owner do
		local creation = index.positions[position.owner]
		if creation == nil or creation.owner == position.owner then
			return nil
		end
		position = creation
	end
	return position
end

local function pointIsBeforeStatement(index: Index, point: Position, statement: Record): boolean
	local statementPosition = index.positions[statement]
	if statementPosition == nil then
		return false
	end
	for _, pointEntry in ancestry(index, point) do
		for _, statementEntry in ancestry(index, statementPosition) do
			if pointEntry.block == statementEntry.block then
				return pointEntry.statementIndex < statementEntry.statementIndex
			end
		end
	end
	return false
end

local function outermostRepeatedStatement(index: Index, definition: Definition): Record?
	local statement = definition.statement
	local outermost: Record? = nil
	while statement ~= nil do
		if isRepeatedStatement(statement) then
			outermost = statement
		end
		local position = index.positions[statement]
		if position == nil or position.block == nil then
			break
		end
		statement = index.blockParents[position.block]
	end
	return outermost
end

local function conditionalGuardRoot(index: Index, point: Position): Record?
	local child = point.node
	local parent = index.parents[child]
	while parent ~= nil do
		if parent.type == "AstStatIf" and parent.condition == child then
			local root = parent
			local outer = index.parents[root]
			while outer ~= nil and outer.type == "AstStatIf" and outer.elsebody == root do
				root = outer
				outer = index.parents[root]
			end
			return root
		end
		child = parent
		parent = index.parents[child]
	end
	return nil
end

local function nodeIsWithin(index: Index, node: Record, ancestor: Record): boolean
	local current: Record? = node
	while current ~= nil do
		if current == ancestor then
			return true
		end
		current = index.parents[current :: Record]
	end
	return false
end

local function pointPrecedesDefinitionCommit(index: Index, point: Position, definition: Definition): boolean
	if point.owner ~= definition.owner or definition.statement == nil then
		return false
	end
	if point.statement == definition.statement then
		return not definition.repeated and (definition.kind == "assignment" or definition.kind == "compound_assignment")
	end
	local guardRoot = conditionalGuardRoot(index, point)
	if guardRoot ~= nil and nodeIsWithin(index, definition.statement, guardRoot :: Record) then
		local repeatBoundary = if definition.repeated then outermostRepeatedStatement(index, definition) else nil
		if repeatBoundary == nil or not nodeIsWithin(index, point.node, repeatBoundary :: Record) then
			return true
		end
	end
	local boundary = if definition.repeated then outermostRepeatedStatement(index, definition) else definition.statement
	if definition.repeated
		and boundary == point.statement
		and ((boundary :: Record).type == "AstStatFor" or (boundary :: Record).type == "AstStatForIn")
	then
		-- Numeric and generic for controls are evaluated once before the body.
		return true
	end
	return boundary ~= nil and pointIsBeforeStatement(index, point, boundary :: Record)
end

local function pointPrecedesInvocationChain(
	index: Index,
	point: Position,
	chain: TemporalInvocationFlow.Chain
): boolean
	if chain.repeated then
		return false
	end
	local invocation = chain.invocations[#chain.invocations]
	assert(invocation ~= nil, "direct invocation chain has no outer point")
	local liftedDefinition: Definition = {
		owner = point.owner,
		statement = invocation.statement,
		block = invocation.block,
		statementIndex = invocation.statementIndex,
		expression = nil,
		resultOrdinal = 1,
		kind = "local_function",
		repeated = false,
	}
	return pointPrecedesDefinitionCommit(index, point, liftedDefinition)
end

local function pointPrecedesNestedInvocation(index: Index, point: Position, definition: Definition): boolean
	if definition.repeated or definition.owner.type ~= "AstExprFunction" then
		return false
	end
	local chain = TemporalInvocationFlow.traceToOwner(
		index,
		definition.owner,
		point.owner,
		TemporalTargetIdentity.maxInvocationDepth
	)
	if chain ~= nil then
		return pointPrecedesInvocationChain(index, point, chain)
	end
	local invocationSet = TemporalInvocationFlow.traceSetToOwner(
		index,
		definition.owner,
		point.owner,
		TemporalTargetIdentity.maxInvocationDepth,
		TemporalTargetIdentity.maxInvocationSites
	)
	if invocationSet == nil then
		return false
	end
	for _, invocationChain in invocationSet.chains do
		if not pointPrecedesInvocationChain(index, point, invocationChain) then
			return false
		end
	end
	return #invocationSet.chains > 0
end

local function definitionIsUncommittedAtAnyPoint(
	index: Index,
	definition: Definition,
	commitPoints: { Position }
): boolean
	for _, point in commitPoints do
		if pointPrecedesDefinitionCommit(index, point, definition)
			or pointPrecedesNestedInvocation(index, point, definition)
		then
			return true
		end
	end
	return false
end

local function uniqueReachingDefinition(
	index: Index,
	definitions: { Definition },
	point: Position,
	commitPoints: { Position }
): Definition?
	local selected: Definition? = nil
	for _, candidate in definitions do
		if definitionDominates(index, candidate, point) then
			local supersedesAll = true
			for _, other in definitions do
				if other ~= candidate
					and not definitionIsBefore(index, other, candidate)
					and not definitionIsUncommittedAtAnyPoint(index, other, commitPoints)
				then
					supersedesAll = false
					break
				end
			end
			if supersedesAll then
				assert(selected == nil, "temporal target has more than one unique reaching definition")
				selected = candidate
			end
		end
	end
	return selected
end

local function invocationContext(
	chain: TemporalInvocationFlow.Chain,
	nodePosition: Position
): (Position, { Position })
	local outerInvocation = chain.invocations[#chain.invocations]
	assert(outerInvocation ~= nil, "direct invocation chain has no outer point")
	local commitPoints: { Position } = { outerInvocation }
	if not chain.repeated then
		for chainIndex = 1, #chain.invocations - 1 do
			local intermediate = chain.invocations[chainIndex]
			assert(intermediate ~= nil, "direct invocation chain has a missing intermediate point")
			table.insert(commitPoints, intermediate)
		end
		table.insert(commitPoints, nodePosition)
	end
	return outerInvocation, commitPoints
end

local function finiteInvocationDefinition(
	index: Index,
	definitions: { Definition },
	nodePosition: Position,
	invocationSet: TemporalInvocationFlow.InvocationSet
): Definition?
	local selected: Definition? = nil
	for _, chain in invocationSet.chains do
		if chain.repeated then
			return nil
		end
		local point, commitPoints = invocationContext(chain, nodePosition)
		local candidate = uniqueReachingDefinition(index, definitions, point, commitPoints)
		if candidate == nil or (selected ~= nil and selected ~= candidate) then
			return nil
		end
		selected = candidate
	end
	return selected
end

local function declarationBindingKind(index: Index, location: string): "value" | "place"
	local declaration = index.declarations[location]
	assert(declaration ~= nil, `temporal target declaration {location} is not indexed`)
	if declaration.kind == "local_function" then
		return "place"
	end
	local definitions = index.definitions[location]
	assert(definitions ~= nil and #definitions > 0, `temporal target declaration {location} has no source definition`)
	for _, definition in definitions do
		if definition.kind == "assignment"
			or definition.kind == "compound_assignment"
			or definition.kind == "function_statement"
		then
			return "place"
		end
	end
	return "value"
end

local function initialDefinition(index: Index, location: string): Definition
	local definitions = index.definitions[location]
	assert(definitions ~= nil, `temporal origin declaration {location} has no source definition`)
	local initial: Definition? = nil
	for _, definition in definitions do
		if definition.kind == "declaration"
			or definition.kind == "local_function"
			or definition.kind == "parameter"
			or definition.kind == "loop_variable"
		then
			assert(initial == nil, `temporal origin declaration {location} has ambiguous ownership`)
			initial = definition
		end
	end
	assert(initial ~= nil, `temporal origin declaration {location} has no owning definition`)
	return initial :: Definition
end

local function validateLocalOrigin(index: Index, expression: Record, origin: Record): boolean
	local localNode = expression["local"]
	if expression.type ~= "AstExprLocal" or type(localNode) ~= "table" or type(origin.declaration) ~= "table" then
		return false
	end
	local expressionLocation = declarationLocation(localNode, "temporal local origin expression")
	local originLocation = declarationLocation(origin.declaration, "temporal authenticated local origin")
	if expressionLocation ~= originLocation then
		return false
	end
	local expectedKind = if origin.kind == "local_value" then "value" else "place"
	assert(
		declarationBindingKind(index, originLocation) == expectedKind,
		`temporal authenticated {origin.kind} origin {originLocation} has the wrong binding kind`
	)
	local declaration = index.declarations[originLocation]
	assert(declaration ~= nil)
	local point = pointInOwner(index, expression, declaration.owner)
	assert(point ~= nil, `temporal authenticated local origin {originLocation} crosses an unrelated lexical owner`)
	assert(
		definitionDominates(index, initialDefinition(index, originLocation), point :: Position),
		`temporal authenticated local origin {originLocation} is not available at the selected write`
	)
	return true
end

local function stableCapturedStatementCallee(
	index: Index,
	declaration: Declaration,
	definitions: { Definition },
	useNode: Record
): Definition?
	local selected: Definition?
	if declaration.kind == "local_function" then
		if #definitions ~= 1 or definitions[1].kind ~= "local_function" then
			return nil
		end
		selected = definitions[1]
	elseif declaration.kind == "local" then
		if #definitions ~= 2 then
			return nil
		end
		local ownership: Definition?
		for _, candidate in definitions do
			if candidate.kind == "declaration" then
				local expression = candidate.expression
				if ownership ~= nil
					or candidate.repeated
					or (expression ~= nil and (expression :: Record).type ~= "AstExprConstantNil")
				then
					return nil
				end
				ownership = candidate
			elseif candidate.kind == "function_statement" then
				if selected ~= nil then
					return nil
				end
				selected = candidate
			else
				return nil
			end
		end
		if ownership == nil
			or selected == nil
			or not definitionIsBefore(index, ownership :: Definition, selected :: Definition)
		then
			return nil
		end
	else
		return nil
	end
	local definition = selected :: Definition
	local point = pointInOwner(index, useNode, declaration.owner)
	if definition.repeated
		or definition.expression == nil
		or definition.block == nil
		or index.blockParents[definition.block :: Record] ~= nil
		or point == nil
		or not definitionDominates(index, definition, point :: Position)
	then
		return nil
	end
	return definition
end

local function localCalleeDefinition(index: Index, useNode: Record, localExpression: Record): Record?
	local localNode = localExpression["local"]
	if localExpression.type ~= "AstExprLocal"
		or type(localNode) ~= "table"
		or (localNode :: Record).type ~= "AstLocal"
		or type((localNode :: Record).location) ~= "string"
		or (localNode :: Record).location == ""
	then
		return nil
	end
	local location = (localNode :: Record).location :: string
	local declaration = index.declarations[location]
	local definitions = index.definitions[location]
	if declaration == nil
		or (declaration.kind ~= "local" and declaration.kind ~= "local_function")
		or definitions == nil
		or #definitions > TemporalTargetIdentity.maxLocalCalleeDefinitions
	then
		return nil
	end
	local definition: Definition?
	if declarationBindingKind(index, location) == "value" then
		if #definitions ~= 1 then
			return nil
		end
		local immutableDefinition = definitions[1]
		local point = pointInOwner(index, useNode, declaration.owner)
		if immutableDefinition.kind ~= "declaration"
			or immutableDefinition.repeated
			or immutableDefinition.expression == nil
			or point == nil
			or not definitionDominates(index, immutableDefinition, point :: Position)
		then
			return nil
		end
		definition = immutableDefinition
	else
		local point = index.positions[useNode]
		if point == nil then
			return nil
		elseif point.owner ~= declaration.owner then
			definition = stableCapturedStatementCallee(index, declaration, definitions, useNode)
			if definition == nil then
				return nil
			end
		else
			local reaching = uniqueReachingDefinition(index, definitions, point, { point })
			if reaching == nil
				or (reaching.kind ~= "declaration"
					and reaching.kind ~= "assignment"
					and reaching.kind ~= "local_function"
					and reaching.kind ~= "function_statement")
				or reaching.repeated
				or reaching.expression == nil
			then
				return nil
			end
			definition = reaching
		end
	end
	if (definition :: Definition).resultOrdinal ~= 1 then
		return nil
	end
	return (definition :: Definition).expression
end

local function matchesOrigin(
	index: Index,
	value: any,
	resultOrdinal: number,
	origin: Record,
	matchesResult: ResultMatcher?
): boolean
	return TargetOriginMatcher.matchesResult(value, resultOrdinal, origin, function(expression: Record, localOrigin: Record): boolean
		return validateLocalOrigin(index, expression, localOrigin)
	end, function(call: Record, callee: Record): Record?
		return TemporalCalleeResolver.resolve(call, callee, function(useNode: Record, localExpression: Record): Record?
			return localCalleeDefinition(index, useNode, localExpression)
		end)
	end, matchesResult)
end

type ReachingDefinitions = {
	bindingKind: "value" | "place",
	definitions: { Definition },
	pathConditional: boolean,
}

local function reachingDefinitions(
	index: Index,
	node: Record,
	declaration: Record,
	subject: string,
	allowDefinitionSet: boolean
): ReachingDefinitions
	local location = declarationLocation(declaration, subject .. " origin")
	local declarationInfo = index.declarations[location]
	assert(declarationInfo ~= nil, `{subject} declaration {location} is not indexed`)
	local definitions = index.definitions[location]
	assert(definitions ~= nil and #definitions > 0, `{subject} declaration {location} has no source definition`)
	local nodePosition = index.positions[node]
	assert(nodePosition ~= nil, `{subject} use is not indexed`)
	local bindingKind: "value" | "place" = declarationBindingKind(index, location)

	if bindingKind == "value" then
		assert(#definitions == 1, `{subject} value {location} is not immutable`)
		local definition = definitions[1]
		assert(
			definition.kind == "declaration" or definition.kind == "parameter",
			`{subject} value {location} does not have an immutable value definition`
		)
		local point = pointInOwner(index, node, declarationInfo.owner)
		assert(point ~= nil, `{subject} value {location} crosses an unrelated lexical owner`)
		assert(definitionDominates(index, definition, point :: Position), `{subject} value {location} does not dominate its use`)
		return { bindingKind = bindingKind, definitions = { definition }, pathConditional = false }
	end

	local captured = nodePosition.owner ~= declarationInfo.owner
	local invocationChain = if captured
		then TemporalInvocationFlow.traceToOwner(
			index,
			nodePosition.owner,
			declarationInfo.owner,
			TemporalTargetIdentity.maxInvocationDepth
		)
		else nil
	if captured and invocationChain == nil then
		local invocationSet = TemporalInvocationFlow.traceSetToOwner(
			index,
			nodePosition.owner,
			declarationInfo.owner,
			TemporalTargetIdentity.maxInvocationDepth,
			TemporalTargetIdentity.maxInvocationSites
		)
		if invocationSet ~= nil then
			local finiteDefinition = finiteInvocationDefinition(index, definitions, nodePosition, invocationSet)
			assert(finiteDefinition ~= nil, `{subject} place {location} has no common reaching invocation definition`)
			return {
				bindingKind = bindingKind,
				definitions = { finiteDefinition :: Definition },
				pathConditional = false,
			}
		end
	end
	local invocationPoint: Position? = nil
	local commitPoints: { Position } = {}
	if invocationChain ~= nil then
		invocationPoint, commitPoints = invocationContext(invocationChain, nodePosition)
	end
	local invocationBounded = invocationPoint ~= nil
	local point = if invocationBounded
		then invocationPoint
		elseif captured then pointInOwner(index, node, declarationInfo.owner)
		else nodePosition
	assert(point ~= nil, `{subject} place {location} crosses an unrelated closure boundary`)
	if not captured then
		table.insert(commitPoints, point :: Position)
	end
	local definition = uniqueReachingDefinition(index, definitions, point :: Position, commitPoints)
	local selected: { Definition }
	local pathConditional = false
	if definition ~= nil then
		selected = { definition :: Definition }
	elseif allowDefinitionSet then
		local structuredCandidates: { StructuredCandidate } = {}
		local structuredDefinitions: { Definition } = {}
		for _, candidate in definitions do
			local uncommitted = definitionIsUncommittedAtAnyPoint(index, candidate, commitPoints)
			if not uncommitted then
				table.insert(structuredDefinitions, candidate)
				table.insert(structuredCandidates, {
					owner = candidate.owner,
					statement = candidate.statement,
					repeated = candidate.repeated,
				})
			end
		end
		local candidateIndices = StructuredDefinitionSets.find(index, declarationInfo.owner, point :: Position, structuredCandidates)
		assert(candidateIndices ~= nil, `{subject} place {location} has no feasible structured definition set`)
		selected = {}
		for _, candidateIndex in candidateIndices :: { number } do
			local candidate = structuredDefinitions[candidateIndex]
			assert(candidate ~= nil, `{subject} place {location} has an invalid feasible definition index`)
			table.insert(selected, candidate :: Definition)
		end
		pathConditional = true
	else
		assert(false, `{subject} place {location} has no unique reaching definition`)
	end
	if captured and not invocationBounded then
		local selectedSet: { [any]: boolean } = {}
		for _, candidate in selected do
			selectedSet[candidate] = true
		end
		for _, other in definitions do
			if selectedSet[other] ~= true then
				local beforeEveryCandidate = other.owner == declarationInfo.owner
				for _, candidate in selected do
					if not definitionIsBefore(index, other, candidate) then
						beforeEveryCandidate = false
						break
					end
				end
				assert(beforeEveryCandidate, `{subject} place {location} has a write after or inside its closure snapshot`)
			end
		end
	end
	return { bindingKind = bindingKind, definitions = selected, pathConditional = pathConditional }
end

function TemporalTargetIdentity.analyze(document: Record): Analysis
	return TemporalSourceIndex.analyze(document)
end

function TemporalTargetIdentity.matchesExpression(
	analysis: Analysis,
	expression: Record,
	origin: Record,
	matchesResult: ResultMatcher?
): boolean
	return matchesOrigin(analysis, expression, 1, origin, matchesResult)
end

function TemporalTargetIdentity.verify(
	analysis: Analysis,
	call: Record,
	declarationValue: any,
	authenticatedOrigin: Record,
	matchesResult: ResultMatcher?
): Proof
	local declaration = expectRecord(declarationValue, "temporal target origin")
	local location = declarationLocation(declaration, "temporal target origin")
	local index = analysis
	local reaching = reachingDefinitions(index, call, declaration, "temporal target", true)
	local bindingKind: "value" | "place" = reaching.bindingKind
	local resolvedDefinitions = reaching.definitions
	local resolvedDefinition = resolvedDefinitions[1]
	assert(resolvedDefinition ~= nil)
	local selfOrigin = (authenticatedOrigin.kind == "local_value" or authenticatedOrigin.kind == "local_place")
		and type(authenticatedOrigin.declaration) == "table"
		and declarationLocation(authenticatedOrigin.declaration, "temporal authenticated target origin") == location
	local aliasDepth = 0
	if selfOrigin then
		assert(not reaching.pathConditional, `temporal target {location} cannot authenticate a definition set with itself`)
		local expectedKind = if authenticatedOrigin.kind == "local_value" then "value" else "place"
		assert(bindingKind == expectedKind, `temporal target {location} does not match its authenticated binding kind`)
	else
		local roots: { TemporalAliasGraph.Root } = {}
		for _, candidate in resolvedDefinitions do
			assert(candidate.expression ~= nil, `temporal target {location} has an unauthenticated feasible definition`)
			table.insert(roots, {
				value = candidate.expression :: Record,
				result_ordinal = candidate.resultOrdinal,
				anchor = candidate,
				seen_location = location,
			})
		end
		local results = TemporalAliasGraph.resolve({
			max_depth = TemporalTargetIdentity.maxAliasDepth,
			max_candidates = TemporalTargetIdentity.maxAliasCandidates,
			matches_origin = function(value: Record, resultOrdinal: number, origin: Record): boolean
				return matchesOrigin(index, value, resultOrdinal, origin, matchesResult)
			end,
			reaching = function(node: Record, aliasDeclaration: Record, subject: string): TemporalAliasGraph.Reaching
				local aliasReaching = reachingDefinitions(index, node, aliasDeclaration, subject, true)
				local definitions: { TemporalAliasGraph.Definition } = {}
				for _, definition in aliasReaching.definitions do
					table.insert(definitions, definition)
				end
				return {
					definitions = definitions,
					path_conditional = aliasReaching.pathConditional,
				}
			end,
		}, roots, authenticatedOrigin)
		assert(#results == #resolvedDefinitions)
		local commonAnchor: TemporalAliasGraph.Definition? = nil
		for _, result in results do
			local matched = result.result
			if reaching.pathConditional then
				assert(matched ~= nil, `temporal target {location} has an unauthenticated feasible definition`)
			else
				assert(matched ~= nil, `temporal target definition {location} does not match its authenticated origin`)
			end
			local proof = matched :: TemporalAliasGraph.Match
			assert(proof.anchor.repeated ~= true, `temporal target {location} depends on a repeated dynamic evaluation`)
			aliasDepth = math.max(aliasDepth, proof.depth)
			if reaching.pathConditional then
				if commonAnchor == nil then
					commonAnchor = proof.anchor
				else
					assert(commonAnchor == proof.anchor, `temporal target {location} does not share one stable authenticated identity`)
				end
			end
		end
	end
	local callLocation = expectLocation(call.location, "temporal target call")
	local definitionLocation = if reaching.pathConditional
		then callLocation
		elseif resolvedDefinition.statement ~= nil
		then expectLocation(resolvedDefinition.statement.location, "temporal target definition")
		else location
	return {
		binding_kind = bindingKind,
		declaration = declaration,
		alias_depth = aliasDepth,
		definition_count = #resolvedDefinitions,
		definition_kind = if reaching.pathConditional then "definition_set" else resolvedDefinition.kind,
		definition_location = definitionLocation,
		call_location = callLocation,
	}
end

return table.freeze(TemporalTargetIdentity)
