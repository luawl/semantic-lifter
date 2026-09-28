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
	assert(#instruction.results == 1, "expected one interpolation-lane result")
	return resolved.values[instruction.results[1] + 1]
end

local function audit(inputPath: string, resolvedPath: string, reresolvedPath: string, generatedPath: string)
	local raw: any = serde.decode("json", fs.readFile(inputPath))
	local resolvedEncoded = fs.readFile(resolvedPath)
	local resolved: any = serde.decode("json", resolvedEncoded)
	assert(resolvedEncoded == fs.readFile(reresolvedPath), "interpolation node splitting is not byte-idempotent")
	assert(#raw.edge_rewrites == 0, "interpolation frontend authored a backend rewrite")
	assert(#resolved.blocks == #raw.blocks + 1, "interpolation node splitting did not create one exact block")
	assert(#resolved.values == #raw.values + 4, "interpolation node splitting changed value allocation")
	assert(#resolved.value_packs == #raw.value_packs, "interpolation node splitting changed pack allocation")
	assert(#resolved.instructions == #raw.instructions + 4, "interpolation node splitting changed instruction allocation")
	assert(#resolved.edge_rewrites == 1, "interpolation node splitting changed rewrite history")

	local rewrite = resolved.edge_rewrites[1]
	assert(rewrite.id == 0 and rewrite.rule == "node_split", "interpolation control used the wrong rewrite authority")
	assert(rewrite.certificate == nil, "interpolation node splitting acquired a solver certificate")
	assert(
		#rewrite.from.arguments == 1 and sameArray(rewrite.from.arguments, rewrite.to.arguments),
		"interpolation entry arguments changed"
	)
	local source = resolved.blocks[rewrite.from.target + 1]
	local clone = resolved.blocks[rewrite.to.target + 1]
	assert(source.id ~= clone.id and source["function"] == clone["function"], "interpolation clone crossed a function boundary")
	assert(source.name_hint == "interpolation_entry" and clone.name_hint == source.name_hint, "interpolation clone changed its block name")
	assert(#source.parameters == 1 and #clone.parameters == 1, "interpolation clone changed parameter arity")
	assert(#source.instructions == 4 and #clone.instructions == 4, "interpolation clone changed instruction arity")
	local sourceParameter = resolved.values[source.parameters[1] + 1]
	local cloneParameter = resolved.values[clone.parameters[1] + 1]
	assert(sourceParameter.id ~= cloneParameter.id, "interpolation clone reused its source parameter")
	assert(sameType(sourceParameter.type, cloneParameter.type) and sourceParameter.type.kind == "integer", "interpolation parameter type changed")

	local sourceKey = resolved.instructions[source.instructions[1] + 1]
	local cloneKey = resolved.instructions[clone.instructions[1] + 1]
	assert(sourceKey.operation.constant.string == "result" and cloneKey.operation.constant.string == "result", "interpolation result key changed")
	assert(sourceKey.id ~= cloneKey.id and sameEffects(sourceKey.effects, cloneKey.effects), "interpolation result key did not replay")
	local sourceKeyValue = resultValue(resolved, sourceKey)
	local cloneKeyValue = resultValue(resolved, cloneKey)
	assert(sourceKeyValue.id ~= cloneKeyValue.id and sameType(sourceKeyValue.type, cloneKeyValue.type), "interpolation result-key value did not replay")

	local sourceInstruction = resolved.instructions[source.instructions[2] + 1]
	local cloneInstruction = resolved.instructions[clone.instructions[2] + 1]
	local sourceInterpolation = sourceInstruction.operation.string_interpolate
	local cloneInterpolation = cloneInstruction.operation.string_interpolate
	assert(sourceInstruction.id ~= cloneInstruction.id, "interpolation instruction identity was reused")
	assert(
		sameArray(sourceInterpolation.segments, { "prefix:", ":counter:", ":suffix" })
			and sameArray(sourceInterpolation.segments, cloneInterpolation.segments),
		"interpolation segment bytes or order changed"
	)
	assert(
		#sourceInterpolation.segments == #sourceInterpolation.values + 1
			and #cloneInterpolation.segments == #cloneInterpolation.values + 1,
		"interpolation segment/value shape changed"
	)
	assert(#sourceInterpolation.values == 2 and #cloneInterpolation.values == 2, "interpolation value arity changed")
	assert(sourceInterpolation.values[1] == cloneInterpolation.values[1], "interpolation external object identity changed")
	assert(
		sourceInterpolation.values[2] == sourceParameter.id and cloneInterpolation.values[2] == cloneParameter.id,
		"interpolation counter value was not remapped"
	)
	local dynamicObject = resolved.values[sourceInterpolation.values[1] + 1]
	assert(dynamicObject.type.kind == "dynamic", "interpolation external object lost its dynamic domain")
	assert(sameEffects(sourceInstruction.effects, cloneInstruction.effects), "interpolation effects changed during replay")
	assert(
		sourceInstruction.effects.precision == "conservative"
			and sourceInstruction.effects.reads_memory == true
			and sourceInstruction.effects.writes_memory == true
			and sourceInstruction.effects.may_throw == true
			and sourceInstruction.effects.may_yield == true
			and sourceInstruction.effects.invokes_unknown_code == true,
		"interpolation lost the full dynamic string-conversion boundary"
	)
	local sourceRendered = resultValue(resolved, sourceInstruction)
	local cloneRendered = resultValue(resolved, cloneInstruction)
	assert(sourceRendered.id ~= cloneRendered.id, "interpolation result identity was reused")
	assert(sameType(sourceRendered.type, cloneRendered.type) and sourceRendered.type.kind == "string", "interpolation result type changed")

	local sourceWrite = resolved.instructions[source.instructions[3] + 1]
	local cloneWrite = resolved.instructions[clone.instructions[3] + 1]
	assert(sourceWrite.operation.table_set.mode == "raw" and cloneWrite.operation.table_set.mode == "raw", "interpolation publication changed mode")
	assert(sourceWrite.operation.table_set.table == cloneWrite.operation.table_set.table, "interpolation publication changed external sink")
	assert(
		sourceWrite.operation.table_set.key == sourceKeyValue.id
			and cloneWrite.operation.table_set.key == cloneKeyValue.id
			and sourceWrite.operation.table_set.value == sourceRendered.id
			and cloneWrite.operation.table_set.value == cloneRendered.id,
		"interpolation publication operands were not remapped"
	)
	assert(sameEffects(sourceWrite.effects, cloneWrite.effects), "interpolation publication effects changed")

	local sourceContinuation = resolved.instructions[source.instructions[4] + 1]
	local cloneContinuation = resolved.instructions[clone.instructions[4] + 1]
	assert(
		sourceContinuation.operation.constant.integer == "2" and cloneContinuation.operation.constant.integer == "2",
		"interpolation continuation constant changed"
	)
	local sourceForwarded = resultValue(resolved, sourceContinuation)
	local cloneForwarded = resultValue(resolved, cloneContinuation)
	assert(source.terminator.jump.target == clone.terminator.jump.target, "interpolation clone changed successor")
	assert(sameArray(source.terminator.jump.arguments, { sourceForwarded.id }), "interpolation source lost continuation value")
	assert(sameArray(clone.terminator.jump.arguments, { cloneForwarded.id }), "interpolation clone lost mapped continuation value")

	local generated = fs.readFile(generatedPath)
	local helperAudit = string.gsub(generated, "__lifter_rawset", "")
	helperAudit = string.gsub(helperAudit, "__lifter_string_format", "")
	assert(string.find(helperAudit, "__lifter", 1, true) == nil, "interpolation node splitting emitted an unknown backend helper")
	assert(string.find(generated, "local __lifter_rawset = rawset", 1, true) ~= nil, "rawset target capability was not captured")
	assert(string.find(generated, "local __lifter_string_format = string.format", 1, true) ~= nil, "string.format target capability was not captured")
	assert(string.find(generated, "prefix:%*:counter:%*:suffix", 1, true) ~= nil, "interpolation format segments disappeared")
	assert(string.find(generated, "__lifter_string_format(", 1, true) ~= nil, "interpolation conversion boundary disappeared")
end

return table.freeze({ run = audit })
