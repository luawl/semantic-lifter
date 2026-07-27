--!strict

local IterationExitTransferRuntimeOracle = {}

function IterationExitTransferRuntimeOracle.run(chunk: any, source: string): (...any) -> any
	local numericWorker, genericWorker, nestedWorker = chunk()
	assert(type(numericWorker) == "function", "numeric iteration exit-transfer worker changed category")
	assert(type(genericWorker) == "function", "generic iteration exit-transfer worker changed category")
	assert(type(nestedWorker) == "function", "nested iteration exit-transfer worker changed category")

	local numericSeen: { number } = {}
	local numericLoop = numericWorker(true, 1, 3, 1, "numeric-loop", "numeric-bypass", function(value: number)
		table.insert(numericSeen, value)
	end)
	assert(numericLoop == "numeric-loop", "numeric loop exit selected the wrong invariant value")
	assert(#numericSeen == 3 and numericSeen[1] == 1 and numericSeen[2] == 2 and numericSeen[3] == 3, "numeric loop execution changed")
	local numericBypass = numericWorker(false, 1, 3, 1, "numeric-loop", "numeric-bypass", function(_: number)
		error("numeric bypass executed the loop observer")
	end)
	assert(numericBypass == "numeric-bypass", "numeric bypass exit selected the wrong invariant value")

	local items = { 11, 22 }
	local function iterator(state: { number }, control: number): (number?, number?)
		local nextControl = control + 1
		if nextControl > #state then
			return nil, nil
		end
		return nextControl, state[nextControl]
	end
	local genericSeen: { number } = {}
	local genericLoop = genericWorker(true, iterator, items, 0, "generic-loop", "generic-bypass", function(index: number, value: number)
		table.insert(genericSeen, index * 100 + value)
	end)
	assert(genericLoop == "generic-loop", "generic loop exit selected the wrong invariant value")
	assert(#genericSeen == 2 and genericSeen[1] == 111 and genericSeen[2] == 222, "generic loop execution changed")
	local genericBypass = genericWorker(false, iterator, items, 0, "generic-loop", "generic-bypass", function(_: number, _: number)
		error("generic bypass executed the loop observer")
	end)
	assert(genericBypass == "generic-bypass", "generic bypass exit selected the wrong invariant value")

	local nestedSeen: { number } = {}
	local nestedMarkers: { string } = {}
	nestedWorker(
		1,
		2,
		1,
		10,
		11,
		1,
		function(outerIndex: number): string
			return `outer-{outerIndex}`
		end,
		function(outerIndex: number, innerIndex: number)
			table.insert(nestedSeen, outerIndex * 100 + innerIndex)
		end,
		function(marker: string, outerIndex: number)
			assert(marker == `outer-{outerIndex}`, "nested loop exit selected a stale enclosing-loop value")
			table.insert(nestedMarkers, marker)
		end
	)
	assert(
		#nestedSeen == 4
			and nestedSeen[1] == 110
			and nestedSeen[2] == 111
			and nestedSeen[3] == 210
			and nestedSeen[4] == 211,
		"nested numeric loop execution changed"
	)
	assert(
		#nestedMarkers == 2 and nestedMarkers[1] == "outer-1" and nestedMarkers[2] == "outer-2",
		"nested loop exit did not preserve each enclosing-loop definition"
	)

	assert(select(2, string.gsub(source, "for%s+[%a_][%w_]*%s*=", "")) == 3, "numeric iteration did not use three native loops")
	assert(select(2, string.gsub(source, "for%s+[%a_][%w_]*,%s*[%a_][%w_]*%s+in%s+", "")) == 1, "generic iteration did not use one native loop")
	assert(string.find(source, "while true", 1, true) == nil, "iteration exit transfer fell back to a while loop")
	local markerDefinition = string.find(source, "local iteration_marker = make_marker(outer_index)", 1, true)
	local innerLoop = string.find(source, "for inner_index =", 1, true)
	local transfer = string.find(source, "inner_exit_marker, inner_exit_outer_index = iteration_marker, outer_index", 1, true)
	local afterInner = string.find(source, "after_inner(inner_exit_marker, inner_exit_outer_index)", 1, true)
	assert(
		markerDefinition ~= nil
			and innerLoop ~= nil
			and transfer ~= nil
			and afterInner ~= nil
			and markerDefinition < innerLoop
			and innerLoop < transfer
			and transfer < afterInner,
		"nested iteration exit transfer moved across its semantic boundary"
	)
	return numericWorker
end

return IterationExitTransferRuntimeOracle
