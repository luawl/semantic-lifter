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

local function sameType(left: any, right: any): boolean
	return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed
end

local function sameEffects(left: any, right: any): boolean
	return left.precision == right.precision
		and left.reads_memory == right.reads_memory
		and left.writes_memory == right.writes_memory
		and left.may_throw == right.may_throw
		and left.may_yield == right.may_yield
		and left.invokes_unknown_code == right.invokes_unknown_code
end

local function resultValue(resolved: any, instruction: any): any
	assert(#instruction.results == 1, "expected one closure-lane result")
	return resolved.values[instruction.results[1] + 1]
end

local function audit(inputPath: string, resolvedPath: string, reresolvedPath: string, generatedPath: string)
	local raw: any = serde.decode("json", fs.readFile(inputPath))
	local resolvedEncoded = fs.readFile(resolvedPath)
	local resolved: any = serde.decode("json", resolvedEncoded)
	assert(resolvedEncoded == fs.readFile(reresolvedPath), "closure node splitting is not byte-idempotent")
	assert(#raw.edge_rewrites == 0, "closure frontend authored a backend rewrite")
	assert(#resolved.functions == #raw.functions, "closure node splitting changed lexical function allocation")
	assert(#resolved.captures == #raw.captures, "closure node splitting changed capture allocation")
	assert(#resolved.places == #raw.places, "closure node splitting changed place allocation")
	assert(#resolved.blocks == #raw.blocks + 1, "closure node splitting did not create one exact block")
	assert(#resolved.values == #raw.values + 4, "closure node splitting changed value allocation")
	assert(#resolved.value_packs == #raw.value_packs, "closure node splitting changed pack allocation")
	assert(#resolved.instructions == #raw.instructions + 4, "closure node splitting changed instruction allocation")
	assert(#resolved.edge_rewrites == 1, "closure node splitting changed rewrite history")

	local rewrite = resolved.edge_rewrites[1]
	assert(rewrite.id == 0 and rewrite.rule == "node_split", "closure control used the wrong rewrite authority")
	assert(rewrite.certificate == nil, "closure node splitting acquired a solver certificate")
	assert(#rewrite.from.arguments == 1 and sameArray(rewrite.from.arguments, rewrite.to.arguments), "closure entry arguments changed")
	local source = resolved.blocks[rewrite.from.target + 1]
	local clone = resolved.blocks[rewrite.to.target + 1]
	assert(source.id ~= clone.id and source["function"] == clone["function"], "closure clone crossed a function boundary")
	assert(source.name_hint == "closure_entry" and clone.name_hint == source.name_hint, "closure clone changed its block name")
	assert(#source.parameters == 1 and #clone.parameters == 1, "closure clone changed parameter arity")
	assert(#source.instructions == 4 and #clone.instructions == 4, "closure clone changed instruction arity")
	local sourceParameter = resolved.values[source.parameters[1] + 1]
	local cloneParameter = resolved.values[clone.parameters[1] + 1]
	assert(sourceParameter.id ~= cloneParameter.id, "closure clone reused its source parameter")
	assert(sameType(sourceParameter.type, cloneParameter.type) and sourceParameter.type.kind == "integer", "closure parameter type changed")

	local factory = resolved.functions[source["function"] + 1]
	assert(#factory.local_places == 1, "closure factory lost its shared local place")
	local state = resolved.places[factory.local_places[1] + 1]
	assert(state["function"] == factory.id and state.origin["local"] == 0, "closure factory place is not canonical")
	assert(#state.evidence == 1, "closure factory place lost provenance")

	local sourceKey = resolved.instructions[source.instructions[1] + 1]
	local cloneKey = resolved.instructions[clone.instructions[1] + 1]
	assert(sourceKey.operation.constant.string == "closure" and cloneKey.operation.constant.string == "closure", "closure publication key changed")
	local sourceKeyValue = resultValue(resolved, sourceKey)
	local cloneKeyValue = resultValue(resolved, cloneKey)
	assert(sourceKeyValue.id ~= cloneKeyValue.id and sameType(sourceKeyValue.type, cloneKeyValue.type), "closure key value did not replay")

	local sourceSnapshotInstruction = resolved.instructions[source.instructions[2] + 1]
	local cloneSnapshotInstruction = resolved.instructions[clone.instructions[2] + 1]
	local sourceSnapshotOperation = sourceSnapshotInstruction.operation.binary
	local cloneSnapshotOperation = cloneSnapshotInstruction.operation.binary
	assert(sourceSnapshotOperation.operator == "add" and cloneSnapshotOperation.operator == "add", "closure snapshot operation changed")
	assert(sourceSnapshotOperation.left == cloneSnapshotOperation.left, "closure snapshot changed its external seed")
	assert(
		sourceSnapshotOperation.right == sourceParameter.id and cloneSnapshotOperation.right == cloneParameter.id,
		"closure snapshot parameter was not remapped"
	)
	local sourceSnapshot = resultValue(resolved, sourceSnapshotInstruction)
	local cloneSnapshot = resultValue(resolved, cloneSnapshotInstruction)
	assert(sourceSnapshot.id ~= cloneSnapshot.id, "closure snapshot identity was reused")
	assert(sameType(sourceSnapshot.type, cloneSnapshot.type) and sourceSnapshot.type.kind == "integer", "closure snapshot type changed")

	local sourceInstruction = resolved.instructions[source.instructions[3] + 1]
	local cloneInstruction = resolved.instructions[clone.instructions[3] + 1]
	local sourceClosure = sourceInstruction.operation.make_closure
	local cloneClosure = cloneInstruction.operation.make_closure
	assert(sourceInstruction.id ~= cloneInstruction.id, "closure instruction identity was reused")
	assert(sourceClosure["function"] == cloneClosure["function"], "closure replay changed its lexical child")
	assert(#sourceClosure.bindings == 2 and #cloneClosure.bindings == 2, "closure replay changed binding arity")
	assert(
		sourceClosure.bindings[1].value == sourceSnapshot.id and cloneClosure.bindings[1].value == cloneSnapshot.id,
		"closure immutable binding was not remapped"
	)
	assert(
		sourceClosure.bindings[2].place == state.id and cloneClosure.bindings[2].place == state.id,
		"closure shared-place identity changed"
	)
	assert(sameEffects(sourceInstruction.effects, cloneInstruction.effects), "closure effects changed during replay")
	assert(
		sourceInstruction.effects.precision == "exact"
			and sourceInstruction.effects.reads_memory == false
			and sourceInstruction.effects.writes_memory == false
			and sourceInstruction.effects.may_throw == false
			and sourceInstruction.effects.may_yield == false
			and sourceInstruction.effects.invokes_unknown_code == false,
		"closure construction lost exact-pure effects"
	)
	local sourceClosureValue = resultValue(resolved, sourceInstruction)
	local cloneClosureValue = resultValue(resolved, cloneInstruction)
	assert(sourceClosureValue.id ~= cloneClosureValue.id, "closure result identity was reused")
	assert(sameType(sourceClosureValue.type, cloneClosureValue.type) and sourceClosureValue.type.kind == "function", "closure result type changed")

	local child = resolved.functions[sourceClosure["function"] + 1]
	assert(child.lexical_parent == factory.id and #child.captures == 2, "closure child ownership or capture order changed")
	assert(#child.evidence == 1, "closure child lost provenance")
	local valueCapture = resolved.captures[child.captures[1] + 1]
	local placeCapture = resolved.captures[child.captures[2] + 1]
	assert(valueCapture["function"] == child.id and valueCapture.kind.immutable_value ~= nil, "closure immutable capture changed kind")
	assert(placeCapture["function"] == child.id and placeCapture.kind.shared_place ~= nil, "closure shared capture changed kind")
	assert(#valueCapture.evidence == 1 and #placeCapture.evidence == 1, "closure capture provenance disappeared")
	local capturedValue = resolved.values[valueCapture.kind.immutable_value + 1]
	local capturedPlace = resolved.places[placeCapture.kind.shared_place + 1]
	assert(capturedValue.origin.capture == valueCapture.id, "closure immutable slot origin changed")
	assert(capturedPlace.origin.capture == placeCapture.id and #capturedPlace.evidence == 1, "closure shared slot origin or provenance changed")

	local sourceWrite = resolved.instructions[source.instructions[4] + 1]
	local cloneWrite = resolved.instructions[clone.instructions[4] + 1]
	assert(sourceWrite.operation.table_set.mode == "raw" and cloneWrite.operation.table_set.mode == "raw", "closure publication changed mode")
	assert(sourceWrite.operation.table_set.table == cloneWrite.operation.table_set.table, "closure publication changed sink identity")
	assert(
		sourceWrite.operation.table_set.key == sourceKeyValue.id
			and cloneWrite.operation.table_set.key == cloneKeyValue.id
			and sourceWrite.operation.table_set.value == sourceClosureValue.id
			and cloneWrite.operation.table_set.value == cloneClosureValue.id,
		"closure publication operands were not remapped"
	)
	assert(sameEffects(sourceWrite.effects, cloneWrite.effects), "closure publication effects changed")

	assert(source.terminator.jump.target == clone.terminator.jump.target, "closure clone changed successor")
	assert(sameArray(source.terminator.jump.arguments, { sourceParameter.id }), "closure source lost continuation value")
	assert(sameArray(clone.terminator.jump.arguments, { cloneParameter.id }), "closure clone lost mapped continuation value")

	local generated = fs.readFile(generatedPath)
	local helperAudit = string.gsub(generated, "__lifter_rawset", "")
	assert(string.find(helperAudit, "__lifter", 1, true) == nil, "closure node splitting emitted an unknown backend helper")
	assert(string.find(generated, "local __lifter_rawset = rawset", 1, true) ~= nil, "rawset target capability was not captured")
	assert(string.find(generated, "snapshot_counter", 1, true) ~= nil, "closure lexical child disappeared")
	assert(string.find(generated, "state", 1, true) ~= nil, "closure shared place disappeared")
end

return table.freeze({ run = audit })
