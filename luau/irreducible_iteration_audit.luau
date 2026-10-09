--!strict

local fs = require("@lune/fs")
local serde = require("@lune/serde")

local function sameArray(left: { any }, right: { any }): boolean
	if #left ~= #right then
		return false
	end
	for index, value in left do
		if right[index] ~= value then
			return false
		end
	end
	return true
end

local function sameEdge(left: any, right: any): boolean
	return left.target == right.target and sameArray(left.arguments, right.arguments)
end

local function isBooleanConstant(program: any, valueId: number, expected: boolean): boolean
	if valueId < 0 or valueId >= #program.values then
		return false
	end
	local value = program.values[valueId + 1]
	local origin = value.origin.instruction_result
	if origin == nil or origin.instruction < 0 or origin.instruction >= #program.instructions then
		return false
	end
	local instruction = program.instructions[origin.instruction + 1]
	if instruction.id ~= origin.instruction
		or origin.index < 0
		or origin.index >= #instruction.results
		or instruction.results[origin.index + 1] ~= valueId
	then
		return false
	end
	local constant = instruction.operation.constant
	return constant ~= nil and constant.boolean == expected
end

local function followHistory(resolved: any, source: number, kind: string, initial: any, used: { [number]: boolean }): (any, number, number)
	local current = initial
	local forwardingCount = 0
	local splitCount = 0
	while true do
		local nextRewrite = nil
		for _, rewrite in resolved.edge_rewrites do
			if not used[rewrite.id]
				and (rewrite.rule == "forwarding_jump" or rewrite.rule == "node_split")
				and rewrite.source == source
				and rewrite.kind == kind
				and sameEdge(rewrite.from, current)
			then
				assert(nextRewrite == nil, "iteration rewrite history forked")
				nextRewrite = rewrite
			end
		end
		if nextRewrite == nil then
			return current, forwardingCount, splitCount
		end
		assert(nextRewrite.certificate == nil, "iteration history acquired a solver certificate")
		used[nextRewrite.id] = true
		current = nextRewrite.to
		if nextRewrite.rule == "forwarding_jump" then
			forwardingCount += 1
		else
			splitCount += 1
		end
		assert(forwardingCount + splitCount <= #resolved.blocks, "iteration rewrite history cycled")
	end
end

local function rewindForwarding(resolved: any, source: number, kind: string, final: any): any
	local current = final
	local count = 0
	while true do
		local previous = nil
		for _, rewrite in resolved.edge_rewrites do
			if rewrite.rule == "forwarding_jump"
				and rewrite.source == source
				and rewrite.kind == kind
				and sameEdge(rewrite.to, current)
			then
				assert(previous == nil, "iteration rewrite history merged ambiguously")
				previous = rewrite
			end
		end
		if previous == nil then
			return current
		end
		current = previous.from
		count += 1
		assert(count <= #resolved.blocks, "iteration rewrite history cycled backward")
	end
end

local function audit(inputPath: string, resolvedPath: string, reresolvedPath: string, generatedPath: string)
	local raw: any = serde.decode("json", fs.readFile(inputPath))
	local resolvedEncoded = fs.readFile(resolvedPath)
	local resolved: any = serde.decode("json", resolvedEncoded)
	assert(resolvedEncoded == fs.readFile(reresolvedPath), "iteration convergence is not byte-idempotent")
	assert(#raw.edge_rewrites == 0, "iteration frontend authored a backend rewrite")
	assert(#resolved.blocks == #raw.blocks + 4, "iteration convergence changed clone allocation")
	assert(#resolved.values == #raw.values + 16, "iteration convergence changed parameter allocation")
	assert(#resolved.value_packs == #raw.value_packs, "iteration convergence changed pack allocation")
	assert(#resolved.instructions == #raw.instructions, "iteration convergence cloned a protocol instruction")
	local used: { [number]: boolean } = {}
	local splits: { any } = {}
	local entrySplits: { any } = {}
	local closureSplits: { any } = {}
	for index, rewrite in resolved.edge_rewrites do
		assert(rewrite.id == index - 1, "iteration rewrite IDs are not canonical")
		assert(rewrite.certificate == nil, "iteration rewrite acquired a solver certificate")
		if rewrite.rule == "node_split" then
			table.insert(splits, rewrite)
			if rewrite.kind == "branch_then" then
				table.insert(entrySplits, rewrite)
			elseif rewrite.kind == "jump" then
				table.insert(closureSplits, rewrite)
			else
				assert(false, "iteration convergence added an unexpected split edge kind")
			end
		end
	end
	assert(#splits == 4, "iteration convergence changed clone authority")
	assert(#entrySplits == 2 and #closureSplits == 2, "iteration convergence changed closure split ownership")

	for _, split in entrySplits do
		assert(sameArray(split.from.arguments, split.to.arguments), "iteration split changed incoming state")
		local entryInitial = rewindForwarding(resolved, split.source, split.kind, split.from)
		local entryFinal, entryForwardCount, entrySplitCount = followHistory(resolved, split.source, split.kind, entryInitial, used)
		assert(entryForwardCount == 2 and entrySplitCount == 1, "iteration entry did not compose forwarding and split authority")

		local firstLatch = resolved.blocks[entryInitial.target + 1]
		local firstClone = resolved.blocks[split.to.target + 1]
		local closureSplit = nil
		for _, candidate in closureSplits do
			if candidate.source == firstClone.id and candidate.kind == "jump" then
				assert(closureSplit == nil, "iteration clone closure has multiple internal split edges")
				closureSplit = candidate
			end
		end
		assert(closureSplit ~= nil, "iteration clone closure lost its internal split edge")
		assert(not used[closureSplit.id], "iteration clone closure reused an internal split edge")
		used[closureSplit.id] = true
		assert(sameArray(closureSplit.from.arguments, closureSplit.to.arguments), "iteration closure split changed internal state")
		local secondLatch = resolved.blocks[closureSplit.from.target + 1]
		local secondClone = resolved.blocks[closureSplit.to.target + 1]
		local header = resolved.blocks[entryFinal.target + 1]
		assert(string.find(firstLatch.name_hint, "forwarding_latch_1", 1, true) ~= nil, "iteration source is not the first forwarding latch")
		assert(string.find(secondLatch.name_hint, "forwarding_latch_2", 1, true) ~= nil, "iteration chain lost its second forwarding latch")
		assert(firstClone.name_hint == firstLatch.name_hint and firstClone.id ~= firstLatch.id, "iteration first-latch clone changed identity metadata")
		assert(secondClone.name_hint == secondLatch.name_hint and secondClone.id ~= secondLatch.id, "iteration second-latch clone changed identity metadata")
		assert(
			#firstLatch.parameters == 4 and #firstClone.parameters == 4 and #secondLatch.parameters == 4 and #secondClone.parameters == 4,
			"iteration latch clone changed hidden-state arity"
		)
		assert(
			#firstLatch.instructions == 0 and #firstClone.instructions == 0 and #secondLatch.instructions == 0 and #secondClone.instructions == 0,
			"iteration latch acquired instructions"
		)
		assert(firstLatch.terminator.jump.target == secondLatch.id, "iteration latch chain lost its second latch")
		assert(firstClone.terminator.jump.target == secondClone.id, "iteration clone chain escaped to its source latch")
		assert(secondClone.terminator.jump.target == header.id and secondLatch.terminator.jump.target == header.id, "iteration latch chain changed its protocol header")
		assert(#header.parameters == 4 and #header.instructions == 1, "iteration header lost canonical shape")
		local transition = resolved.instructions[header.instructions[1] + 1]
		assert(transition.block == header.id and transition.results[1] == header.terminator.branch.condition, "iteration transition lost header ownership")
		local expectedBackedgePrefix: { number } = {}
		if string.find(header.name_hint, "numeric", 1, true) ~= nil then
			assert(transition.operation.numeric_for_next ~= nil and #transition.results == 4, "numeric protocol transition changed shape")
			expectedBackedgePrefix = { transition.results[4], transition.results[2], transition.results[3] }
			local exit = resolved.blocks[header.terminator.branch.else_edge.target + 1]
			assert(
				sameArray(exit.terminator.return_values, { transition.results[2], transition.results[3] }),
				"numeric normalized state did not remain explicit at the exit"
			)
		else
			assert(transition.operation.generic_for_next.variable_count == 2 and #transition.results == 5, "generic protocol transition changed shape")
			expectedBackedgePrefix = { transition.results[2], transition.results[3], transition.results[4] }
		end

		local entry = resolved.blocks[split.source + 1]
		local currentEntry = if split.kind == "branch_then" then entry.terminator.branch.then_edge else entry.terminator.branch.else_edge
		assert(sameEdge(currentEntry, entryFinal), "iteration entry did not converge on the header")

		local body = resolved.blocks[header.terminator.branch.then_edge.target + 1]
		local liveBackedge = body.terminator.jump
		assert(liveBackedge ~= nil, "iteration body lost its backedge")
		local bodyInitial = rewindForwarding(resolved, body.id, "jump", liveBackedge)
		assert(bodyInitial.target == firstLatch.id, "iteration backedge does not enter its first forwarding latch")
		assert(#bodyInitial.arguments == 4, "iteration backedge changed the protocol state arity")
		for index, expected in expectedBackedgePrefix do
			assert(bodyInitial.arguments[index] == expected, "iteration backedge changed the next protocol state")
		end
		assert(
			isBooleanConstant(resolved, bodyInitial.arguments[4], false),
			"iteration backedge did not clear the initial-transition flag"
		)
		local bodyFinal = followHistory(resolved, body.id, "jump", bodyInitial, used)
		assert(sameEdge(liveBackedge, bodyFinal), "iteration backedge history does not match the live CFG")
	end

	for _, rewrite in resolved.edge_rewrites do
		assert(used[rewrite.id], "iteration rewrite history contains an unaudited edge")
	end

	local generated = fs.readFile(generatedPath)
	local _, selectorCount = string.gsub(generated, "local _ = selector%(start_latch%)", "")
	local helperAudit = generated
	helperAudit = string.gsub(helperAudit, "__lifter_getmetatable", "")
	helperAudit = string.gsub(helperAudit, "__lifter_next", "")
	helperAudit = string.gsub(helperAudit, "__lifter_type", "")
	assert(string.find(helperAudit, "__lifter", 1, true) == nil, "iteration convergence emitted an unknown backend helper")
	assert(selectorCount == 2, "converged iteration changed selector effect evaluation")
	assert(string.find(generated, "for numeric_index = initial, limit, step do", 1, true) ~= nil, "numeric transition did not emit a native loop")
	assert(string.find(generated, "return limit, step", 1, true) ~= nil, "numeric normalized state did not reuse evaluated inputs")
	assert(string.find(generated, "for generic_index, generic_value in iterator", 1, true) ~= nil, "generic transition did not emit a native loop")
	assert(string.find(generated, "initial_transition", 1, true) == nil, "native iteration emitted its hidden initial flag")
	assert(string.find(generated, "if start_latch", 1, true) == nil, "converged iteration entry emitted an empty branch")
	assert(string.find(generated, "while true do", 1, true) == nil, "iteration protocol fell back to a synthetic loop")
end

return table.freeze({ run = audit })
