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
	assert(#instruction.results == 1, "expected one constructor result")
	return resolved.values[instruction.results[1] + 1]
end

local function audit(inputPath: string, resolvedPath: string, reresolvedPath: string, generatedPath: string)
	local raw: any = serde.decode("json", fs.readFile(inputPath))
	local resolvedEncoded = fs.readFile(resolvedPath)
	local resolved: any = serde.decode("json", resolvedEncoded)
	assert(resolvedEncoded == fs.readFile(reresolvedPath), "table node splitting is not byte-idempotent")
	assert(#raw.edge_rewrites == 0, "table frontend authored a backend rewrite")
	assert(#resolved.blocks == #raw.blocks + 1, "table node splitting did not create one exact block")
	assert(#resolved.values == #raw.values + 8, "table node splitting changed value allocation")
	assert(#resolved.value_packs == #raw.value_packs + 1, "table node splitting changed pack allocation")
	assert(#resolved.instructions == #raw.instructions + 9, "table node splitting changed instruction allocation")
	assert(#resolved.edge_rewrites == 1, "table node splitting changed rewrite history")

	local rewrite = resolved.edge_rewrites[1]
	assert(rewrite.id == 0 and rewrite.rule == "node_split", "table control used the wrong rewrite authority")
	assert(rewrite.certificate == nil, "table node splitting acquired a solver certificate")
	assert(#rewrite.from.arguments == 1 and sameArray(rewrite.from.arguments, rewrite.to.arguments), "table entry arguments changed")
	local source = resolved.blocks[rewrite.from.target + 1]
	local clone = resolved.blocks[rewrite.to.target + 1]
	assert(source.id ~= clone.id and source["function"] == clone["function"], "table clone crossed a function boundary")
	assert(source.name_hint == "table_entry" and clone.name_hint == source.name_hint, "table clone changed its block name")
	assert(#source.parameters == 1 and #clone.parameters == 1, "table clone changed parameter arity")
	assert(#source.instructions == 9 and #clone.instructions == 9, "table clone changed instruction arity")
	local sourceParameter = resolved.values[source.parameters[1] + 1]
	local cloneParameter = resolved.values[clone.parameters[1] + 1]
	assert(sourceParameter.id ~= cloneParameter.id and sameType(sourceParameter.type, cloneParameter.type), "table parameter identity or type changed")

	local worker = resolved.functions[source["function"] + 1]
	assert(worker.is_variadic == true and worker.vararg_pack ~= nil, "table worker lost direct varargs")
	local varargPack = resolved.value_packs[worker.vararg_pack + 1]
	assert(varargPack.origin.varargs == worker.id and varargPack.shape.tail == "open", "table vararg pack is not canonical")

	local sourceNestedKey = resolved.instructions[source.instructions[1] + 1]
	local cloneNestedKey = resolved.instructions[clone.instructions[1] + 1]
	local sourceEmptyKey = resolved.instructions[source.instructions[2] + 1]
	local cloneEmptyKey = resolved.instructions[clone.instructions[2] + 1]
	local sourceResultKey = resolved.instructions[source.instructions[3] + 1]
	local cloneResultKey = resolved.instructions[clone.instructions[3] + 1]
	for _, pair in {
		{ sourceNestedKey, cloneNestedKey, "nested" },
		{ sourceEmptyKey, cloneEmptyKey, "empty" },
		{ sourceResultKey, cloneResultKey, "result" },
	} do
		local original = pair[1]
		local copied = pair[2]
		assert(original.operation.constant.string == pair[3] and copied.operation.constant.string == pair[3], "table key constant changed")
		assert(original.id ~= copied.id and sameEffects(original.effects, copied.effects), "table key instruction did not replay")
		local originalValue = resultValue(resolved, original)
		local copiedValue = resultValue(resolved, copied)
		assert(originalValue.id ~= copiedValue.id and sameType(originalValue.type, copiedValue.type), "table key value did not replay")
	end

	local sourceEmpty = resolved.instructions[source.instructions[4] + 1]
	local cloneEmpty = resolved.instructions[clone.instructions[4] + 1]
	assert(sourceEmpty.operation.make_table ~= nil and cloneEmpty.operation.make_table ~= nil, "empty table allocation changed operation")
	local sourceEmptyValue = resultValue(resolved, sourceEmpty)
	local cloneEmptyValue = resultValue(resolved, cloneEmpty)
	assert(sourceEmptyValue.id ~= cloneEmptyValue.id and sourceEmptyValue.type.kind == "table", "empty table identity or type was reused")
	assert(sameEffects(sourceEmpty.effects, cloneEmpty.effects), "empty table effects changed")
	assert(
		sourceEmpty.effects.precision == "exact"
			and sourceEmpty.effects.writes_memory == true
			and sourceEmpty.effects.may_throw == true
			and sourceEmpty.effects.reads_memory == false
			and sourceEmpty.effects.may_yield == false
			and sourceEmpty.effects.invokes_unknown_code == false,
		"empty table lost exact allocation effects"
	)

	local sourceDirect = resolved.instructions[source.instructions[5] + 1]
	local cloneDirect = resolved.instructions[clone.instructions[5] + 1]
	local sourceDirectConstructor = sourceDirect.operation.make_table_literal
	local cloneDirectConstructor = cloneDirect.operation.make_table_literal
	assert(#sourceDirectConstructor.fields == 1 and #cloneDirectConstructor.fields == 1, "direct table field count changed")
	assert(
		sourceDirectConstructor.fields[1].list == sourceParameter.id
			and cloneDirectConstructor.fields[1].list == cloneParameter.id,
		"direct table list field was not remapped"
	)
	assert(
		sourceDirectConstructor.tail_pack == varargPack.id and cloneDirectConstructor.tail_pack == varargPack.id,
		"direct table did not share function varargs"
	)
	local sourceDirectValue = resultValue(resolved, sourceDirect)
	local cloneDirectValue = resultValue(resolved, cloneDirect)
	assert(sourceDirectValue.id ~= cloneDirectValue.id and sourceDirectValue.type.kind == "table", "direct table identity was reused")
	assert(sameEffects(sourceDirect.effects, cloneDirect.effects), "direct table effects changed")

	local sourceProducer = resolved.instructions[source.instructions[6] + 1]
	local cloneProducer = resolved.instructions[clone.instructions[6] + 1]
	assert(sourceProducer.operation.call.callee == cloneProducer.operation.call.callee, "table tail producer changed callee")
	assert(
		sourceProducer.operation.call.arguments[1] == sourceParameter.id
			and cloneProducer.operation.call.arguments[1] == cloneParameter.id,
		"table tail producer argument was not remapped"
	)
	assert(sourceProducer.pack_result ~= nil and cloneProducer.pack_result ~= nil, "table tail producer lost its pack")
	assert(sourceProducer.pack_result ~= cloneProducer.pack_result, "table tail producer reused source pack identity")
	local sourcePack = resolved.value_packs[sourceProducer.pack_result + 1]
	local clonePack = resolved.value_packs[cloneProducer.pack_result + 1]
	assert(
		sourcePack.origin.instruction_result == sourceProducer.id
			and clonePack.origin.instruction_result == cloneProducer.id,
		"table tail pack origins were not remapped"
	)
	assert(sourcePack.shape.tail == "open" and #sourcePack.shape.prefix == 3, "table tail pack shape changed")
	assert(sourcePack.shape.prefix[2].kind == "nil_value", "table tail pack lost its nil hole")

	local sourceFinal = resolved.instructions[source.instructions[7] + 1]
	local cloneFinal = resolved.instructions[clone.instructions[7] + 1]
	local sourceFinalConstructor = sourceFinal.operation.make_table_literal
	local cloneFinalConstructor = cloneFinal.operation.make_table_literal
	assert(#sourceFinalConstructor.fields == 3 and #cloneFinalConstructor.fields == 3, "final table field count changed")
	assert(sourceFinalConstructor.fields[1].list == sourceParameter.id, "source final list field changed")
	assert(cloneFinalConstructor.fields[1].list == cloneParameter.id, "clone final list field was not remapped")
	assert(
		sourceFinalConstructor.fields[2].keyed.key == resultValue(resolved, sourceNestedKey).id
			and cloneFinalConstructor.fields[2].keyed.key == resultValue(resolved, cloneNestedKey).id
			and sourceFinalConstructor.fields[2].keyed.value == sourceDirectValue.id
			and cloneFinalConstructor.fields[2].keyed.value == cloneDirectValue.id,
		"nested keyed field was not remapped"
	)
	assert(
		sourceFinalConstructor.fields[3].keyed.key == resultValue(resolved, sourceEmptyKey).id
			and cloneFinalConstructor.fields[3].keyed.key == resultValue(resolved, cloneEmptyKey).id
			and sourceFinalConstructor.fields[3].keyed.value == sourceEmptyValue.id
			and cloneFinalConstructor.fields[3].keyed.value == cloneEmptyValue.id,
		"empty keyed field was not remapped"
	)
	assert(sourceFinalConstructor.tail_pack == sourcePack.id and cloneFinalConstructor.tail_pack == clonePack.id, "final table did not consume mapped tail pack")
	local sourceFinalValue = resultValue(resolved, sourceFinal)
	local cloneFinalValue = resultValue(resolved, cloneFinal)
	assert(sourceFinalValue.id ~= cloneFinalValue.id and sourceFinalValue.type.kind == "table", "final table identity was reused")

	local sourceWrite = resolved.instructions[source.instructions[8] + 1]
	local cloneWrite = resolved.instructions[clone.instructions[8] + 1]
	assert(sourceWrite.operation.table_set.mode == "raw" and cloneWrite.operation.table_set.mode == "raw", "table publication changed mode")
	assert(sourceWrite.operation.table_set.table == cloneWrite.operation.table_set.table, "table publication changed external sink")
	assert(
		sourceWrite.operation.table_set.key == resultValue(resolved, sourceResultKey).id
			and cloneWrite.operation.table_set.key == resultValue(resolved, cloneResultKey).id
			and sourceWrite.operation.table_set.value == sourceFinalValue.id
			and cloneWrite.operation.table_set.value == cloneFinalValue.id,
		"table publication operands were not remapped"
	)

	local sourceContinuation = resolved.instructions[source.instructions[9] + 1]
	local cloneContinuation = resolved.instructions[clone.instructions[9] + 1]
	assert(
		sourceContinuation.operation.constant.integer == "2"
			and cloneContinuation.operation.constant.integer == "2",
		"table continuation constant changed"
	)
	local sourceForwarded = resultValue(resolved, sourceContinuation)
	local cloneForwarded = resultValue(resolved, cloneContinuation)
	assert(source.terminator.jump.target == clone.terminator.jump.target, "table clone changed successor")
	assert(sameArray(source.terminator.jump.arguments, { sourceForwarded.id }), "table source lost continuation value")
	assert(sameArray(clone.terminator.jump.arguments, { cloneForwarded.id }), "table clone lost mapped continuation value")

	local generated = fs.readFile(generatedPath)
	local helperAudit = string.gsub(generated, "__lifter_rawset", "")
	assert(string.find(helperAudit, "__lifter", 1, true) == nil, "table node splitting emitted an unknown backend helper")
	assert(string.find(generated, "local __lifter_rawset = rawset", 1, true) ~= nil, "rawset target capability was not captured")
	assert(string.find(generated, "tail_producer", 1, true) ~= nil, "table tail producer disappeared")
	assert(string.find(generated, "...", 1, true) ~= nil, "direct-vararg table tail disappeared")
	assert(string.find(generated, "nested", 1, true) ~= nil and string.find(generated, "empty", 1, true) ~= nil, "keyed table fields disappeared")
end

return table.freeze({ run = audit })
