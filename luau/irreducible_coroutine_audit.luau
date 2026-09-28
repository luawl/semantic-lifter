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

local function audit(inputPath: string, resolvedPath: string, reresolvedPath: string, generatedPath: string)
	local raw: any = serde.decode("json", fs.readFile(inputPath))
	local resolvedEncoded = fs.readFile(resolvedPath)
	local resolved: any = serde.decode("json", resolvedEncoded)
	assert(resolvedEncoded == fs.readFile(reresolvedPath), "coroutine node splitting is not byte-idempotent")
	assert(#raw.edge_rewrites == 0, "coroutine frontend authored a backend rewrite")
	assert(#resolved.blocks == #raw.blocks + 3, "coroutine node splitting changed block allocation")
	assert(#resolved.values == #raw.values + 28, "coroutine node splitting changed value allocation")
	assert(#resolved.value_packs == #raw.value_packs + 3, "coroutine node splitting changed pack allocation")
	assert(#resolved.instructions == #raw.instructions + 16, "coroutine node splitting changed instruction allocation")
	assert(#resolved.edge_rewrites == 4, "coroutine node splitting changed rewrite history")

	local function findNodeSplit(nameHint: string, kind: string): any
		for _, candidate in resolved.edge_rewrites do
			if candidate.rule == "node_split" and candidate.kind == kind then
				local sourceBlock = resolved.blocks[candidate.from.target + 1]
				if sourceBlock.name_hint == nameHint then
					return candidate
				end
			end
		end
		error(`missing {nameHint} {kind} node split`)
	end

	local rewrite = findNodeSplit("yield_entry", "branch_then")
	assert(rewrite.rule == "node_split", "coroutine control used the wrong rewrite authority")
	assert(rewrite.certificate == nil, "coroutine node splitting acquired a solver certificate")
	assert(#rewrite.from.arguments == 1 and sameArray(rewrite.from.arguments, rewrite.to.arguments), "coroutine entry arguments changed")
	local source = resolved.blocks[rewrite.from.target + 1]
	local clone = resolved.blocks[rewrite.to.target + 1]
	assert(source.id ~= clone.id and source["function"] == clone["function"], "coroutine clone crossed an ownership boundary")
	assert(source.name_hint == "yield_entry" and clone.name_hint == source.name_hint, "coroutine clone changed its stable block name")
	assert(#source.parameters == 1 and #clone.parameters == 1, "coroutine clone changed parameter arity")
	assert(#source.instructions == 2 and #clone.instructions == 2, "coroutine clone changed instruction arity")
	assert(sameArray(source.evidence, clone.evidence), "coroutine clone changed block provenance")

	local sourceParameter = resolved.values[source.parameters[1] + 1]
	local cloneParameter = resolved.values[clone.parameters[1] + 1]
	assert(sourceParameter.id ~= cloneParameter.id, "coroutine clone reused source parameter identity")
	assert(sameType(sourceParameter.type, cloneParameter.type), "coroutine clone changed parameter type")
	assert(
		sourceParameter.origin.block_parameter.block == source.id
			and cloneParameter.origin.block_parameter.block == clone.id,
		"coroutine parameter origins were not remapped"
	)

	local worker = resolved.functions[source["function"] + 1]
	assert(worker.is_variadic == true and worker.vararg_pack ~= nil, "coroutine worker lost direct varargs")
	local varargPack = resolved.value_packs[worker.vararg_pack + 1]
	assert(varargPack.id == worker.vararg_pack and varargPack["function"] == worker.id, "coroutine vararg pack is not canonical")
	assert(varargPack.origin.varargs == worker.id, "coroutine vararg origin changed ownership")
	assert(varargPack.shape.tail == "open" and #varargPack.shape.prefix == 0, "coroutine vararg shape changed")

	local sourceYield = resolved.instructions[source.instructions[1] + 1]
	local cloneYield = resolved.instructions[clone.instructions[1] + 1]
	assert(sourceYield.id ~= cloneYield.id, "coroutine yield clone reused source instruction identity")
	assert(sourceYield.block == source.id and cloneYield.block == clone.id, "coroutine yield ownership was not remapped")
	assert(
		#sourceYield.operation.coroutine_yield.arguments == 1
			and #cloneYield.operation.coroutine_yield.arguments == 1
			and sourceYield.operation.coroutine_yield.arguments[1] == sourceParameter.id
			and cloneYield.operation.coroutine_yield.arguments[1] == cloneParameter.id,
		"coroutine yield fixed argument was not remapped"
	)
	assert(
		sourceYield.operation.coroutine_yield.argument_pack == varargPack.id
			and cloneYield.operation.coroutine_yield.argument_pack == varargPack.id,
		"coroutine yield did not share canonical function varargs"
	)
	assert(
		sourceYield.operation.coroutine_yield.result_arity.variadic ~= nil
			and cloneYield.operation.coroutine_yield.result_arity.variadic ~= nil,
		"coroutine yield changed open result arity"
	)
	assert(#sourceYield.results == 0 and #cloneYield.results == 0, "coroutine yield created ordinary result identities")
	assert(sourceYield.pack_result ~= nil and cloneYield.pack_result ~= nil, "coroutine yield lost its resumed-value pack")
	assert(sourceYield.pack_result ~= cloneYield.pack_result, "coroutine yield reused source pack identity")
	assert(#sourceYield.claims == 0 and #cloneYield.claims == 0, "coroutine yield acquired proof authority")
	assert(sameEffects(sourceYield.effects, cloneYield.effects), "coroutine yield changed effects")
	assert(
		sourceYield.effects.precision == "conservative"
			and sourceYield.effects.reads_memory == true
			and sourceYield.effects.writes_memory == true
			and sourceYield.effects.may_throw == true
			and sourceYield.effects.may_yield == true
			and sourceYield.effects.invokes_unknown_code == true,
		"coroutine yield lost its suspension boundary"
	)
	assert(sameArray(sourceYield.evidence, cloneYield.evidence), "coroutine yield changed provenance")

	local sourcePack = resolved.value_packs[sourceYield.pack_result + 1]
	local clonePack = resolved.value_packs[cloneYield.pack_result + 1]
	assert(sourcePack.id ~= clonePack.id, "coroutine resumed-value pack identities collapsed")
	assert(
		sourcePack.origin.instruction_result == sourceYield.id
			and clonePack.origin.instruction_result == cloneYield.id,
		"coroutine resumed-value pack origins were not remapped"
	)
	assert(
		sourcePack.shape.tail == "open"
			and clonePack.shape.tail == "open"
			and #sourcePack.shape.prefix == 1
			and #clonePack.shape.prefix == 1
			and sourcePack.shape.prefix[1].kind == "integer",
		"coroutine resumed-value pack shape changed"
	)
	assert(sameArray(sourcePack.evidence, clonePack.evidence), "coroutine resumed-value pack changed provenance")

	local sourceAdjust = resolved.instructions[source.instructions[2] + 1]
	local cloneAdjust = resolved.instructions[clone.instructions[2] + 1]
	assert(
		sourceAdjust.operation.adjust_pack == sourcePack.id and cloneAdjust.operation.adjust_pack == clonePack.id,
		"coroutine adjustment did not consume the mapped pack"
	)
	assert(#sourceAdjust.results == 1 and #cloneAdjust.results == 1, "coroutine adjustment changed result arity")
	assert(sameEffects(sourceAdjust.effects, cloneAdjust.effects), "coroutine adjustment changed effects")
	local sourceResumed = resolved.values[sourceAdjust.results[1] + 1]
	local cloneResumed = resolved.values[cloneAdjust.results[1] + 1]
	assert(sourceResumed.id ~= cloneResumed.id and sameType(sourceResumed.type, cloneResumed.type), "coroutine resumed value changed identity or type")
	assert(
		sourceResumed.origin.instruction_result.instruction == sourceAdjust.id
			and cloneResumed.origin.instruction_result.instruction == cloneAdjust.id,
		"coroutine resumed-value origins were not remapped"
	)
	assert(source.terminator.jump.target == clone.terminator.jump.target, "coroutine clone changed its successor")
	assert(sameArray(source.terminator.jump.arguments, { sourceResumed.id }), "coroutine source lost resumed state")
	assert(sameArray(clone.terminator.jump.arguments, { cloneResumed.id }), "coroutine clone lost mapped resumed state")

	local probeThenRewrite = findNodeSplit("resume_entry", "branch_then")
	local probeElseRewrite = findNodeSplit("resume_entry", "branch_else")
	assert(probeThenRewrite.to.target ~= probeElseRewrite.to.target, "probe entries reused one clone identity")
	assert(probeThenRewrite.certificate == nil and probeElseRewrite.certificate == nil, "probe node split acquired a certificate")
	local provedForward: any = nil
	for _, candidate in resolved.edge_rewrites do
		if candidate.rule == "proved_branch" and candidate.kind == "branch_else" then
			provedForward = candidate
			break
		end
	end
	assert(provedForward ~= nil, "probe control did not retain its proved forwarding rewrite")
	assert(
		resolved.blocks[provedForward.from.target + 1].name_hint == "probe_header"
			and resolved.blocks[provedForward.to.target + 1].name_hint == "resume_entry",
		"proved forwarding selected the wrong probe path"
	)
	assert(
		probeElseRewrite.from.target == provedForward.to.target and probeElseRewrite.id > provedForward.id,
		"post-proof node splitting is not connected to the forwarding rewrite"
	)

	local function auditProbeClone(probeRewrite: any)
		assert(sameArray(probeRewrite.from.arguments, probeRewrite.to.arguments), "probe entry arguments changed")
		local probeSource = resolved.blocks[probeRewrite.from.target + 1]
		local probeClone = resolved.blocks[probeRewrite.to.target + 1]
		assert(probeSource.name_hint == "resume_entry" and probeClone.name_hint == "resume_entry", "probe block identity changed")
		assert(probeSource["function"] == probeClone["function"], "probe clone crossed a function boundary")
		assert(#probeSource.parameters == 2 and #probeClone.parameters == 2, "probe clone changed parameter arity")
		assert(#probeSource.instructions == 7 and #probeClone.instructions == 7, "probe clone changed instruction arity")
		assert(sameArray(probeSource.evidence, probeClone.evidence), "probe clone changed block provenance")

		local valueMap: { [number]: number } = {}
		local packMap: { [number]: number } = {}
		for index, sourceParameterId in probeSource.parameters do
			local cloneParameterId = probeClone.parameters[index]
			local sourceValue = resolved.values[sourceParameterId + 1]
			local cloneValue = resolved.values[cloneParameterId + 1]
			assert(sourceValue.id ~= cloneValue.id and sameType(sourceValue.type, cloneValue.type), "probe parameter identity changed")
			assert(
				sourceValue.origin.block_parameter.block == probeSource.id
					and cloneValue.origin.block_parameter.block == probeClone.id
					and sourceValue.origin.block_parameter.index == index - 1
					and cloneValue.origin.block_parameter.index == index - 1,
				"probe parameter origin was not remapped"
			)
			valueMap[sourceValue.id] = cloneValue.id
		end

		for instructionIndex, sourceInstructionId in probeSource.instructions do
			local cloneInstructionId = probeClone.instructions[instructionIndex]
			local sourceInstruction = resolved.instructions[sourceInstructionId + 1]
			local cloneInstruction = resolved.instructions[cloneInstructionId + 1]
			assert(sourceInstruction.id ~= cloneInstruction.id, "probe clone reused source instruction identity")
			assert(sourceInstruction.block == probeSource.id and cloneInstruction.block == probeClone.id, "probe instruction ownership changed")
			assert(#sourceInstruction.results == #cloneInstruction.results, "probe instruction result arity changed")
			assert(#sourceInstruction.claims == 0 and #cloneInstruction.claims == 0, "probe instruction acquired proof authority")
			assert(sameEffects(sourceInstruction.effects, cloneInstruction.effects), "probe instruction effects changed")
			assert(sameArray(sourceInstruction.evidence, cloneInstruction.evidence), "probe instruction provenance changed")
			for resultIndex, sourceResultId in sourceInstruction.results do
				local cloneResultId = cloneInstruction.results[resultIndex]
				local sourceValue = resolved.values[sourceResultId + 1]
				local cloneValue = resolved.values[cloneResultId + 1]
				assert(sourceValue.id ~= cloneValue.id and sameType(sourceValue.type, cloneValue.type), "probe result identity changed")
				assert(
					sourceValue.origin.instruction_result.instruction == sourceInstruction.id
						and cloneValue.origin.instruction_result.instruction == cloneInstruction.id
						and sourceValue.origin.instruction_result.index == resultIndex - 1
						and cloneValue.origin.instruction_result.index == resultIndex - 1,
					"probe result origin was not remapped"
				)
				valueMap[sourceValue.id] = cloneValue.id
			end
			if sourceInstruction.pack_result ~= nil then
				assert(cloneInstruction.pack_result ~= nil and sourceInstruction.pack_result ~= cloneInstruction.pack_result, "probe pack identity collapsed")
				local sourceResultPack = resolved.value_packs[sourceInstruction.pack_result + 1]
				local cloneResultPack = resolved.value_packs[cloneInstruction.pack_result + 1]
				assert(
					sourceResultPack.origin.instruction_result == sourceInstruction.id
						and cloneResultPack.origin.instruction_result == cloneInstruction.id,
					"probe pack producer origin was not remapped"
				)
				assert(sourceResultPack.shape.tail == cloneResultPack.shape.tail, "probe pack tail changed")
				assert(#sourceResultPack.shape.prefix == #cloneResultPack.shape.prefix, "probe pack prefix arity changed")
				for prefixIndex, sourceType in sourceResultPack.shape.prefix do
					assert(sameType(sourceType, cloneResultPack.shape.prefix[prefixIndex]), "probe pack prefix type changed")
				end
				assert(sameArray(sourceResultPack.evidence, cloneResultPack.evidence), "probe pack provenance changed")
				packMap[sourceResultPack.id] = cloneResultPack.id
			else
				assert(cloneInstruction.pack_result == nil, "probe clone introduced a result pack")
			end
		end

		local function mappedValue(valueId: number): number
			return valueMap[valueId] or valueId
		end
		local function mappedPack(packId: number): number
			return packMap[packId] or packId
		end

		local sourceFunctionRef = resolved.instructions[probeSource.instructions[1] + 1]
		local cloneFunctionRef = resolved.instructions[probeClone.instructions[1] + 1]
		assert(sourceFunctionRef.operation.function_ref == cloneFunctionRef.operation.function_ref, "worker function reference changed")

		local sourceCreate = resolved.instructions[probeSource.instructions[2] + 1]
		local cloneCreate = resolved.instructions[probeClone.instructions[2] + 1]
		assert(
			cloneCreate.operation.coroutine_create.callee == mappedValue(sourceCreate.operation.coroutine_create.callee),
			"coroutine creation did not consume the mapped worker"
		)
		local sourceThread = resolved.values[sourceCreate.results[1] + 1]
		local cloneThread = resolved.values[cloneCreate.results[1] + 1]
		assert(sourceThread.type.kind == "thread" and cloneThread.type.kind == "thread", "coroutine thread type changed")
		assert(
			sourceCreate.effects.precision == "exact"
				and sourceCreate.effects.may_throw == true
				and sourceCreate.effects.reads_memory == false
				and sourceCreate.effects.writes_memory == false
				and sourceCreate.effects.may_yield == false
				and sourceCreate.effects.invokes_unknown_code == false,
			"coroutine creation effects changed"
		)

		local probeFunction = resolved.functions[probeSource["function"] + 1]
		local probeVarargPack = resolved.value_packs[probeFunction.vararg_pack + 1]
		assert(probeFunction.is_variadic == true and probeVarargPack.origin.varargs == probeFunction.id, "probe varargs are not canonical")
		local sourceFixedResume = resolved.instructions[probeSource.instructions[3] + 1]
		local cloneFixedResume = resolved.instructions[probeClone.instructions[3] + 1]
		assert(
			cloneFixedResume.operation.coroutine_resume.thread == mappedValue(sourceFixedResume.operation.coroutine_resume.thread),
			"fixed resume did not consume the mapped thread"
		)
		assert(
			sourceFixedResume.operation.coroutine_resume.argument_pack == probeVarargPack.id
				and cloneFixedResume.operation.coroutine_resume.argument_pack == probeVarargPack.id,
			"fixed resume did not share function varargs"
		)
		assert(
			sourceFixedResume.operation.coroutine_resume.result_arity.fixed == 5
				and cloneFixedResume.operation.coroutine_resume.result_arity.fixed == 5
				and #sourceFixedResume.results == 5
				and #cloneFixedResume.results == 5,
			"fixed resume result arity changed"
		)
		assert(resolved.values[sourceFixedResume.results[1] + 1].type.kind == "boolean", "fixed resume lost status type")

		local sourceOpenResume = resolved.instructions[probeSource.instructions[4] + 1]
		local cloneOpenResume = resolved.instructions[probeClone.instructions[4] + 1]
		assert(
			cloneOpenResume.operation.coroutine_resume.thread == mappedValue(sourceOpenResume.operation.coroutine_resume.thread),
			"open resume did not consume the mapped thread"
		)
		assert(sourceOpenResume.operation.coroutine_resume.result_arity.variadic ~= nil, "open resume changed result arity")
		assert(cloneOpenResume.pack_result == mappedPack(sourceOpenResume.pack_result), "open resume result pack was not remapped")
		local sourceOpenPack = resolved.value_packs[sourceOpenResume.pack_result + 1]
		assert(
			sourceOpenPack.shape.tail == "open"
				and #sourceOpenPack.shape.prefix == 2
				and sourceOpenPack.shape.prefix[1].kind == "boolean"
				and sourceOpenPack.shape.prefix[2].kind == "integer",
			"open resume lost its status-prefix shape"
		)

		local sourceResumeAdjust = resolved.instructions[probeSource.instructions[5] + 1]
		local cloneResumeAdjust = resolved.instructions[probeClone.instructions[5] + 1]
		assert(
			cloneResumeAdjust.operation.adjust_pack == mappedPack(sourceResumeAdjust.operation.adjust_pack),
			"resume adjustment did not consume the mapped pack"
		)

		local sourceVerifier = resolved.instructions[probeSource.instructions[6] + 1]
		local cloneVerifier = resolved.instructions[probeClone.instructions[6] + 1]
		assert(#sourceVerifier.operation.call.arguments == 7 and #cloneVerifier.operation.call.arguments == 7, "verifier arity changed")
		for argumentIndex, sourceArgument in sourceVerifier.operation.call.arguments do
			assert(cloneVerifier.operation.call.arguments[argumentIndex] == mappedValue(sourceArgument), "verifier argument was not remapped")
		end
		assert(sourceVerifier.operation.call.result_arity.fixed == 1, "verifier result arity changed")

		local sourceOne = resolved.instructions[probeSource.instructions[7] + 1]
		local cloneOne = resolved.instructions[probeClone.instructions[7] + 1]
		assert(sourceOne.operation.constant.integer == "1" and cloneOne.operation.constant.integer == "1", "probe constant changed")
		assert(probeSource.terminator.jump.target == probeClone.terminator.jump.target, "probe clone changed its successor")
		for argumentIndex, sourceArgument in probeSource.terminator.jump.arguments do
			assert(probeClone.terminator.jump.arguments[argumentIndex] == mappedValue(sourceArgument), "probe terminator argument was not remapped")
		end
	end

	auditProbeClone(probeThenRewrite)
	auditProbeClone(probeElseRewrite)

	local generated = fs.readFile(generatedPath)
	local helperAudit = string.gsub(generated, "__lifter_coroutine_create", "")
	helperAudit = string.gsub(helperAudit, "__lifter_coroutine_resume", "")
	helperAudit = string.gsub(helperAudit, "__lifter_coroutine_yield", "")
	assert(string.find(helperAudit, "__lifter", 1, true) == nil, "coroutine node splitting emitted an unknown backend helper")
	assert(string.find(generated, "local __lifter_coroutine_create = coroutine.create", 1, true) ~= nil, "coroutine target capability was not captured")
	assert(string.find(generated, "__lifter_coroutine_create(", 1, true) ~= nil, "coroutine creation disappeared from readable Luau")
	assert(string.find(generated, "__lifter_coroutine_resume(", 1, true) ~= nil, "coroutine resume disappeared from readable Luau")
	assert(string.find(generated, "__lifter_coroutine_yield(", 1, true) ~= nil, "coroutine suspension disappeared from readable Luau")
	assert(string.find(generated, "...", 1, true) ~= nil, "coroutine yield lost direct varargs")
end

return table.freeze({ run = audit })
