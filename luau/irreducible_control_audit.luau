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

local function currentEdge(resolved: any, rewrite: any): any
	local source = resolved.blocks[rewrite.source + 1]
	return if rewrite.kind == "branch_then"
		then source.terminator.branch.then_edge
		elseif rewrite.kind == "branch_else" then source.terminator.branch.else_edge
		else source.terminator.jump
end

local function audit(inputPath: string, resolvedPath: string, reresolvedPath: string, generatedPath: string)
	local raw: any = serde.decode("json", fs.readFile(inputPath))
	local resolvedEncoded = fs.readFile(resolvedPath)
	local resolved: any = serde.decode("json", resolvedEncoded)
	assert(resolvedEncoded == fs.readFile(reresolvedPath), "node-split resolution is not byte-idempotent")
	assert(#raw.edge_rewrites == 0, "frontend authored a backend structural rewrite")
	assert(#resolved.blocks == #raw.blocks + 3, "node splitting did not create exactly three blocks")
	assert(#resolved.values == #raw.values + 20, "instruction-bearing node splitting did not create exact value identities")
	assert(#resolved.value_packs == #raw.value_packs + 3, "node splitting did not create exact pack identities")
	assert(#resolved.instructions == #raw.instructions + 20, "node splitting did not create exact instruction identities")
	assert(#resolved.places == #raw.places, "node splitting cloned lexical storage identity")
	assert(#resolved.edge_rewrites == 4, "node splitting did not create the exact structural rewrite history")

	local rewrite = resolved.edge_rewrites[1]
	assert(rewrite.id == 0 and rewrite.rule == "node_split", "irreducible control used the wrong rewrite authority")
	assert(rewrite.certificate == nil, "structural node splitting acquired a solver certificate")
	assert(#rewrite.from.arguments == 1, "parameterized entry lost its incoming argument")
	assert(sameArray(rewrite.from.arguments, rewrite.to.arguments), "node splitting changed incoming arguments")
	assert(rewrite.from.target ~= rewrite.to.target, "node splitting did not redirect the entry")
	local forwarding = resolved.edge_rewrites[4]
	assert(forwarding.id == 3 and forwarding.rule == "forwarding_jump", "copy-only split clone was not structurally forwarded")
	assert(forwarding.certificate == nil, "clone forwarding acquired a solver certificate")
	assert(forwarding.source == rewrite.source and forwarding.kind == rewrite.kind, "structural rewrite identity changed")
	assert(forwarding.from.target == rewrite.to.target, "node-split history is disconnected")

	local original = resolved.blocks[rewrite.from.target + 1]
	local clone = resolved.blocks[rewrite.to.target + 1]
	assert(original.id == rewrite.from.target and clone.id == rewrite.to.target, "rewrite targets are not canonical blocks")
	assert(original["function"] == clone["function"], "clone crossed a function boundary")
	assert(original.name_hint == clone.name_hint, "clone changed its stable name hint")
	assert(#original.parameters == 1 and #clone.parameters == 1, "clone changed parameter arity")
	assert(#original.instructions == 1 and #clone.instructions == 1, "clone changed pure instruction arity")
	assert(sameArray(original.evidence, clone.evidence), "clone changed structural provenance")
	local originalParameter = resolved.values[original.parameters[1] + 1]
	local cloneParameter = resolved.values[clone.parameters[1] + 1]
	assert(originalParameter.id ~= cloneParameter.id, "clone reused source parameter identity")
	assert(originalParameter["function"] == cloneParameter["function"], "cloned parameter crossed a function boundary")
	assert(originalParameter.name_hint == cloneParameter.name_hint, "cloned parameter changed its name hint")
	assert(
		originalParameter.type.kind == cloneParameter.type.kind
			and originalParameter.type.bit_width == cloneParameter.type.bit_width
			and originalParameter.type.signed == cloneParameter.type.signed,
		"cloned parameter changed its value type"
	)
	assert(
		originalParameter.origin.block_parameter.block == original.id
			and originalParameter.origin.block_parameter.index == 0,
		"source parameter origin is not canonical"
	)
	assert(
		cloneParameter.origin.block_parameter.block == clone.id and cloneParameter.origin.block_parameter.index == 0,
		"clone parameter origin is not canonical"
	)
	local originalInstruction = resolved.instructions[original.instructions[1] + 1]
	local cloneInstruction = resolved.instructions[clone.instructions[1] + 1]
	assert(originalInstruction.id ~= cloneInstruction.id, "clone reused source instruction identity")
	assert(originalInstruction.block == original.id and cloneInstruction.block == clone.id, "instruction ownership was not remapped")
	assert(
		originalInstruction.operation.copy == originalParameter.id
			and cloneInstruction.operation.copy == cloneParameter.id,
		"copy operands were not parameter-substituted"
	)
	assert(#originalInstruction.results == 1 and #cloneInstruction.results == 1, "clone changed instruction result arity")
	assert(sameArray(originalInstruction.evidence, cloneInstruction.evidence), "clone changed instruction provenance")
	local originalResult = resolved.values[originalInstruction.results[1] + 1]
	local cloneResult = resolved.values[cloneInstruction.results[1] + 1]
	assert(originalResult.id ~= cloneResult.id, "clone reused source result identity")
	assert(
		originalResult.origin.instruction_result.instruction == originalInstruction.id
			and originalResult.origin.instruction_result.index == 0,
		"source result origin is not canonical"
	)
	assert(
		cloneResult.origin.instruction_result.instruction == cloneInstruction.id
			and cloneResult.origin.instruction_result.index == 0,
		"clone result origin is not canonical"
	)
	assert(original.terminator.jump ~= nil and clone.terminator.jump ~= nil, "split witness is not a forwarding block")
	assert(original.terminator.jump.target == clone.terminator.jump.target, "clone changed its successor")
	assert(sameArray(original.terminator.jump.arguments, { originalResult.id }), "source terminator lost its result use")
	assert(sameArray(clone.terminator.jump.arguments, { cloneResult.id }), "clone terminator was not result-substituted")
	assert(forwarding.to.target == clone.terminator.jump.target, "forwarding rewrite selected the wrong clone successor")
	assert(sameArray(forwarding.from.arguments, rewrite.to.arguments), "forwarding history lost clone inputs")
	assert(sameArray(forwarding.to.arguments, rewrite.to.arguments), "forwarding did not substitute the cloned parameter")

	local liveEdge = currentEdge(resolved, rewrite)
	assert(liveEdge ~= nil and liveEdge.target == forwarding.to.target, "live CFG does not contain the authenticated rewrite chain")

	local semanticRewrite = resolved.edge_rewrites[2]
	assert(semanticRewrite.id == 1 and semanticRewrite.rule == "node_split", "semantic entry used the wrong rewrite authority")
	assert(semanticRewrite.certificate == nil, "semantic node splitting acquired a solver certificate")
	assert(#semanticRewrite.from.arguments == 1, "semantic entry lost its incoming argument")
	assert(sameArray(semanticRewrite.from.arguments, semanticRewrite.to.arguments), "semantic node splitting changed incoming arguments")
	local semanticOriginal = resolved.blocks[semanticRewrite.from.target + 1]
	local semanticClone = resolved.blocks[semanticRewrite.to.target + 1]
	assert(semanticOriginal.id == semanticRewrite.from.target and semanticClone.id == semanticRewrite.to.target, "semantic rewrite targets are not canonical")
	assert(semanticOriginal["function"] == semanticClone["function"], "semantic clone crossed a function boundary")
	local semanticFunction = resolved.functions[semanticOriginal["function"] + 1]
	local rawSemanticFunction = raw.functions[semanticOriginal["function"] + 1]
	assert(semanticFunction.id == semanticOriginal["function"], "semantic function ID is not canonical")
	assert(semanticFunction.is_variadic == true and semanticFunction.vararg_pack ~= nil, "semantic function lost its canonical vararg pack")
	assert(rawSemanticFunction.vararg_pack == semanticFunction.vararg_pack, "node splitting replaced the admitted function-vararg identity")
	local semanticVarargPack = resolved.value_packs[semanticFunction.vararg_pack + 1]
	local rawSemanticVarargPack = raw.value_packs[rawSemanticFunction.vararg_pack + 1]
	assert(semanticVarargPack.id == semanticFunction.vararg_pack, "function-vararg pack ID is not canonical")
	assert(
		semanticVarargPack["function"] == semanticFunction.id
			and semanticVarargPack.origin.varargs == semanticFunction.id,
		"function-vararg pack ownership is not canonical"
	)
	assert(rawSemanticVarargPack.id == semanticVarargPack.id, "node splitting cloned the external function-vararg pack")
	assert(semanticVarargPack.shape.tail == "open" and #semanticVarargPack.shape.prefix == 0, "function-vararg pack shape changed")
	assert(sameArray(rawSemanticVarargPack.evidence, semanticVarargPack.evidence), "function-vararg pack provenance changed")
	assert(semanticOriginal.name_hint == semanticClone.name_hint, "semantic clone changed its stable name hint")
	assert(#semanticOriginal.parameters == 1 and #semanticClone.parameters == 1, "semantic clone changed parameter arity")
	assert(#semanticOriginal.instructions == 15 and #semanticClone.instructions == 15, "semantic clone changed instruction arity")
	assert(sameArray(semanticOriginal.evidence, semanticClone.evidence), "semantic clone changed structural provenance")
	local semanticOriginalParameter = resolved.values[semanticOriginal.parameters[1] + 1]
	local semanticCloneParameter = resolved.values[semanticClone.parameters[1] + 1]
	assert(semanticOriginalParameter.id ~= semanticCloneParameter.id, "semantic clone reused source parameter identity")
	assert(sameType(semanticOriginalParameter.type, semanticCloneParameter.type), "semantic clone changed parameter type")
	assert(
		semanticOriginalParameter.origin.block_parameter.block == semanticOriginal.id
			and semanticCloneParameter.origin.block_parameter.block == semanticClone.id,
		"semantic parameter origins were not remapped"
	)

	local originalRead = resolved.instructions[semanticOriginal.instructions[1] + 1]
	local cloneRead = resolved.instructions[semanticClone.instructions[1] + 1]
	assert(originalRead.id ~= cloneRead.id, "raw-read clone reused source instruction identity")
	assert(originalRead.block == semanticOriginal.id and cloneRead.block == semanticClone.id, "raw-read ownership was not remapped")
	assert(originalRead.operation.table_get.mode == "semantic" and cloneRead.operation.table_get.mode == "semantic", "semantic-read mode changed")
	assert(
		originalRead.operation.table_get.table == cloneRead.operation.table_get.table
			and originalRead.operation.table_get.key == cloneRead.operation.table_get.key,
		"external semantic-read operands changed identity"
	)
	assert(sameEffects(originalRead.effects, cloneRead.effects), "semantic-read clone changed effects")
	assert(
		originalRead.effects.precision == "conservative"
			and originalRead.effects.reads_memory == true
			and originalRead.effects.may_throw == true
			and originalRead.effects.writes_memory == true
			and originalRead.effects.may_yield == true
			and originalRead.effects.invokes_unknown_code == true,
		"semantic-read source effects lost dynamic dispatch"
	)
	assert(#originalRead.results == 1 and #cloneRead.results == 1, "semantic-read clone changed result arity")
	assert(originalRead.pack_result == nil and cloneRead.pack_result == nil, "semantic-read clone introduced a pack result")
	assert(#originalRead.claims == 0 and #cloneRead.claims == 0, "semantic-read clone acquired proof authority")
	assert(sameArray(originalRead.evidence, cloneRead.evidence), "semantic-read clone changed provenance")
	local originalReadValue = resolved.values[originalRead.results[1] + 1]
	local cloneReadValue = resolved.values[cloneRead.results[1] + 1]
	assert(originalReadValue.id ~= cloneReadValue.id, "semantic-read clone reused source result identity")
	assert(sameType(originalReadValue.type, cloneReadValue.type), "semantic-read clone changed result type")
	assert(originalReadValue.name_hint == cloneReadValue.name_hint, "semantic-read clone changed result name hint")
	assert(
		originalReadValue.origin.instruction_result.instruction == originalRead.id
			and cloneReadValue.origin.instruction_result.instruction == cloneRead.id,
		"semantic-read result origins were not remapped"
	)

	local originalEnvironmentRead = resolved.instructions[semanticOriginal.instructions[2] + 1]
	local cloneEnvironmentRead = resolved.instructions[semanticClone.instructions[2] + 1]
	assert(originalEnvironmentRead.id ~= cloneEnvironmentRead.id, "environment clone reused source instruction identity")
	assert(originalEnvironmentRead.block == semanticOriginal.id and cloneEnvironmentRead.block == semanticClone.id, "environment ownership was not remapped")
	assert(
		originalEnvironmentRead.operation.environment_get.mode == "semantic"
			and cloneEnvironmentRead.operation.environment_get.mode == "semantic",
		"environment read mode changed"
	)
	assert(
		originalEnvironmentRead.operation.environment_get.target.value
			== cloneEnvironmentRead.operation.environment_get.target.value,
		"environment target changed identity"
	)
	assert(
		originalEnvironmentRead.operation.environment_get.name == "counter"
			and cloneEnvironmentRead.operation.environment_get.name == "counter",
		"environment name changed"
	)
	assert(sameEffects(originalEnvironmentRead.effects, cloneEnvironmentRead.effects), "environment clone changed effects")
	assert(sameEffects(originalEnvironmentRead.effects, originalRead.effects), "dynamic read summaries diverged")
	assert(#originalEnvironmentRead.results == 1 and #cloneEnvironmentRead.results == 1, "environment clone changed result arity")
	assert(originalEnvironmentRead.pack_result == nil and cloneEnvironmentRead.pack_result == nil, "environment clone introduced a pack result")
	assert(#originalEnvironmentRead.claims == 0 and #cloneEnvironmentRead.claims == 0, "environment clone acquired proof authority")
	assert(sameArray(originalEnvironmentRead.evidence, cloneEnvironmentRead.evidence), "environment clone changed provenance")
	local originalEnvironmentValue = resolved.values[originalEnvironmentRead.results[1] + 1]
	local cloneEnvironmentValue = resolved.values[cloneEnvironmentRead.results[1] + 1]
	assert(originalEnvironmentValue.id ~= cloneEnvironmentValue.id, "environment clone reused source result identity")
	assert(sameType(originalEnvironmentValue.type, cloneEnvironmentValue.type), "environment clone changed result type")
	assert(originalEnvironmentValue.name_hint == cloneEnvironmentValue.name_hint, "environment clone changed result name hint")
	assert(
		originalEnvironmentValue.origin.instruction_result.instruction == originalEnvironmentRead.id
			and cloneEnvironmentValue.origin.instruction_result.instruction == cloneEnvironmentRead.id,
		"environment result origins were not remapped"
	)

	local originalNamecall = resolved.instructions[semanticOriginal.instructions[3] + 1]
	local cloneNamecall = resolved.instructions[semanticClone.instructions[3] + 1]
	assert(originalNamecall.id ~= cloneNamecall.id, "namecall clone reused source instruction identity")
	assert(originalNamecall.block == semanticOriginal.id and cloneNamecall.block == semanticClone.id, "namecall ownership was not remapped")
	assert(originalNamecall.operation.namecall.receiver == cloneNamecall.operation.namecall.receiver, "namecall changed its external receiver")
	assert(
		originalNamecall.operation.namecall.method == "observe" and cloneNamecall.operation.namecall.method == "observe",
		"namecall changed its native method"
	)
	assert(
		#originalNamecall.operation.namecall.arguments == 1
			and #cloneNamecall.operation.namecall.arguments == 1
			and originalNamecall.operation.namecall.arguments[1] == semanticOriginalParameter.id
			and cloneNamecall.operation.namecall.arguments[1] == semanticCloneParameter.id,
		"namecall block-parameter argument was not remapped"
	)
	assert(
		originalNamecall.operation.namecall.argument_pack == semanticVarargPack.id
			and cloneNamecall.operation.namecall.argument_pack == semanticVarargPack.id,
		"namecall did not share the canonical function-vararg pack"
	)
	assert(
		originalNamecall.operation.namecall.result_arity.fixed == 1
			and cloneNamecall.operation.namecall.result_arity.fixed == 1,
		"namecall changed fixed result arity"
	)
	assert(#originalNamecall.results == 1 and #cloneNamecall.results == 1, "namecall clone changed ordinary results")
	assert(originalNamecall.pack_result == nil and cloneNamecall.pack_result == nil, "fixed namecall introduced a result pack")
	assert(#originalNamecall.claims == 0 and #cloneNamecall.claims == 0, "namecall clone acquired proof authority")
	assert(sameEffects(originalNamecall.effects, cloneNamecall.effects), "namecall clone changed effects")
	assert(
		originalNamecall.effects.precision == "conservative"
			and originalNamecall.effects.reads_memory == true
			and originalNamecall.effects.writes_memory == true
			and originalNamecall.effects.may_throw == true
			and originalNamecall.effects.may_yield == true
			and originalNamecall.effects.invokes_unknown_code == true,
		"namecall effects lost the full dynamic invocation boundary"
	)
	assert(sameArray(originalNamecall.evidence, cloneNamecall.evidence), "namecall clone changed provenance")
	local originalNamecallValue = resolved.values[originalNamecall.results[1] + 1]
	local cloneNamecallValue = resolved.values[cloneNamecall.results[1] + 1]
	assert(originalNamecallValue.id ~= cloneNamecallValue.id, "namecall clone reused source result identity")
	assert(sameType(originalNamecallValue.type, cloneNamecallValue.type), "namecall clone changed result type")
	assert(originalNamecallValue.name_hint == cloneNamecallValue.name_hint, "namecall clone changed result name hint")
	assert(
		originalNamecallValue.origin.instruction_result.instruction == originalNamecall.id
			and cloneNamecallValue.origin.instruction_result.instruction == cloneNamecall.id,
		"namecall result origins were not remapped"
	)

	local originalProtectedSuccess = resolved.instructions[semanticOriginal.instructions[4] + 1]
	local cloneProtectedSuccess = resolved.instructions[semanticClone.instructions[4] + 1]
	assert(originalProtectedSuccess.id ~= cloneProtectedSuccess.id, "successful protected-call clone reused source instruction identity")
	assert(
		originalProtectedSuccess.block == semanticOriginal.id and cloneProtectedSuccess.block == semanticClone.id,
		"successful protected-call ownership was not remapped"
	)
	assert(
		originalProtectedSuccess.operation.protected_call.callee == cloneProtectedSuccess.operation.protected_call.callee,
		"successful protected call changed its external callee"
	)
	assert(
		originalProtectedSuccess.operation.protected_call.error_handler == nil
			and cloneProtectedSuccess.operation.protected_call.error_handler == nil,
		"pcall-shaped protected call acquired an error handler"
	)
	assert(
		#originalProtectedSuccess.operation.protected_call.arguments == 1
			and #cloneProtectedSuccess.operation.protected_call.arguments == 1
			and originalProtectedSuccess.operation.protected_call.arguments[1] == semanticOriginalParameter.id
			and cloneProtectedSuccess.operation.protected_call.arguments[1] == semanticCloneParameter.id,
		"successful protected-call block parameter was not remapped"
	)
	assert(
		originalProtectedSuccess.operation.protected_call.argument_pack == semanticVarargPack.id
			and cloneProtectedSuccess.operation.protected_call.argument_pack == semanticVarargPack.id,
		"successful protected call did not share canonical function varargs"
	)
	assert(
		originalProtectedSuccess.operation.protected_call.result_arity.fixed == 2
			and cloneProtectedSuccess.operation.protected_call.result_arity.fixed == 2,
		"successful protected call changed fixed result arity"
	)
	assert(
		#originalProtectedSuccess.results == 2 and #cloneProtectedSuccess.results == 2,
		"successful protected call changed ordinary result count"
	)
	assert(
		originalProtectedSuccess.pack_result == nil and cloneProtectedSuccess.pack_result == nil,
		"fixed protected call introduced a result pack"
	)
	assert(
		#originalProtectedSuccess.claims == 0 and #cloneProtectedSuccess.claims == 0,
		"successful protected call acquired proof authority"
	)
	assert(sameEffects(originalProtectedSuccess.effects, cloneProtectedSuccess.effects), "successful protected call changed effects")
	assert(sameEffects(originalProtectedSuccess.effects, originalNamecall.effects), "successful protected-call dynamic boundary diverged")
	assert(
		sameArray(originalProtectedSuccess.evidence, cloneProtectedSuccess.evidence),
		"successful protected call changed provenance"
	)
	local originalProtectedSuccessStatus = resolved.values[originalProtectedSuccess.results[1] + 1]
	local originalProtectedSuccessValue = resolved.values[originalProtectedSuccess.results[2] + 1]
	local cloneProtectedSuccessStatus = resolved.values[cloneProtectedSuccess.results[1] + 1]
	local cloneProtectedSuccessValue = resolved.values[cloneProtectedSuccess.results[2] + 1]
	for resultIndex = 1, 2 do
		local originalValue = resolved.values[originalProtectedSuccess.results[resultIndex] + 1]
		local cloneValue = resolved.values[cloneProtectedSuccess.results[resultIndex] + 1]
		assert(originalValue.id ~= cloneValue.id, "successful protected call reused source result identity")
		assert(sameType(originalValue.type, cloneValue.type), "successful protected call changed result type")
		assert(
			originalValue.origin.instruction_result.instruction == originalProtectedSuccess.id
				and originalValue.origin.instruction_result.index == resultIndex - 1
				and cloneValue.origin.instruction_result.instruction == cloneProtectedSuccess.id
				and cloneValue.origin.instruction_result.index == resultIndex - 1,
			"successful protected-call result origins were not positionally remapped"
		)
	end
	assert(
		originalProtectedSuccessStatus.type.kind == "boolean" and originalProtectedSuccessValue.type.kind == "integer",
		"successful protected call lost its fixed status/payload contract"
	)

	local originalProtected = resolved.instructions[semanticOriginal.instructions[5] + 1]
	local cloneProtected = resolved.instructions[semanticClone.instructions[5] + 1]
	assert(originalProtected.id ~= cloneProtected.id, "protected-call clone reused source instruction identity")
	assert(originalProtected.block == semanticOriginal.id and cloneProtected.block == semanticClone.id, "protected-call ownership was not remapped")
	assert(originalProtected.operation.protected_call.callee == cloneProtected.operation.protected_call.callee, "protected call changed its external callee")
	assert(
		originalProtected.operation.protected_call.error_handler == cloneProtected.operation.protected_call.error_handler
			and originalProtected.operation.protected_call.error_handler ~= nil,
		"protected call changed its external error handler"
	)
	assert(
		#originalProtected.operation.protected_call.arguments == 1
			and #cloneProtected.operation.protected_call.arguments == 1
			and originalProtected.operation.protected_call.arguments[1] == semanticOriginalParameter.id
			and cloneProtected.operation.protected_call.arguments[1] == semanticCloneParameter.id,
		"protected-call block parameter was not remapped"
	)
	assert(
		originalProtected.operation.protected_call.argument_pack == semanticVarargPack.id
			and cloneProtected.operation.protected_call.argument_pack == semanticVarargPack.id,
		"protected call did not share canonical function varargs"
	)
	assert(
		originalProtected.operation.protected_call.result_arity.variadic ~= nil
			and cloneProtected.operation.protected_call.result_arity.variadic ~= nil,
		"protected call changed variadic result arity"
	)
	assert(#originalProtected.results == 0 and #cloneProtected.results == 0, "protected call created ordinary results")
	assert(originalProtected.pack_result ~= nil and cloneProtected.pack_result ~= nil, "protected call lost its result pack")
	assert(originalProtected.pack_result ~= cloneProtected.pack_result, "protected call reused its source result pack")
	assert(#originalProtected.claims == 0 and #cloneProtected.claims == 0, "protected call acquired proof authority")
	assert(sameEffects(originalProtected.effects, cloneProtected.effects), "protected call changed effects")
	assert(sameEffects(originalProtected.effects, originalNamecall.effects), "protected and ordinary dynamic boundaries diverged")
	assert(sameArray(originalProtected.evidence, cloneProtected.evidence), "protected call changed provenance")
	local originalProtectedPack = resolved.value_packs[originalProtected.pack_result + 1]
	local cloneProtectedPack = resolved.value_packs[cloneProtected.pack_result + 1]
	assert(originalProtectedPack.id ~= cloneProtectedPack.id, "protected result pack identities collapsed")
	assert(
		originalProtectedPack.origin.instruction_result == originalProtected.id
			and cloneProtectedPack.origin.instruction_result == cloneProtected.id,
		"protected result pack origins were not remapped"
	)
	assert(
		originalProtectedPack.shape.tail == "open"
			and cloneProtectedPack.shape.tail == "open"
			and #originalProtectedPack.shape.prefix == 2
			and #cloneProtectedPack.shape.prefix == 2
			and originalProtectedPack.shape.prefix[1].kind == "boolean"
			and originalProtectedPack.shape.prefix[2].kind == "string",
		"protected result pack lost its status-prefix contract"
	)
	assert(sameArray(originalProtectedPack.evidence, cloneProtectedPack.evidence), "protected result pack changed provenance")

	local originalProtectedAdjust = resolved.instructions[semanticOriginal.instructions[6] + 1]
	local cloneProtectedAdjust = resolved.instructions[semanticClone.instructions[6] + 1]
	assert(
		originalProtectedAdjust.operation.adjust_pack == originalProtectedPack.id
			and cloneProtectedAdjust.operation.adjust_pack == cloneProtectedPack.id,
		"protected adjustment did not consume the mapped status pack"
	)
	assert(#originalProtectedAdjust.results == 2 and #cloneProtectedAdjust.results == 2, "protected adjustment changed result count")
	assert(sameEffects(originalProtectedAdjust.effects, cloneProtectedAdjust.effects), "protected adjustment changed effects")
	local originalProtectedStatus = resolved.values[originalProtectedAdjust.results[1] + 1]
	local originalProtectedMessage = resolved.values[originalProtectedAdjust.results[2] + 1]
	local cloneProtectedStatus = resolved.values[cloneProtectedAdjust.results[1] + 1]
	local cloneProtectedMessage = resolved.values[cloneProtectedAdjust.results[2] + 1]
	for resultIndex = 1, 2 do
		local originalValue = resolved.values[originalProtectedAdjust.results[resultIndex] + 1]
		local cloneValue = resolved.values[cloneProtectedAdjust.results[resultIndex] + 1]
		assert(originalValue.id ~= cloneValue.id, "protected adjustment reused source value identity")
		assert(sameType(originalValue.type, cloneValue.type), "protected adjustment changed result type")
		assert(
			originalValue.origin.instruction_result.instruction == originalProtectedAdjust.id
				and originalValue.origin.instruction_result.index == resultIndex - 1
				and cloneValue.origin.instruction_result.instruction == cloneProtectedAdjust.id
				and cloneValue.origin.instruction_result.index == resultIndex - 1,
			"protected adjustment result origins were not positionally remapped"
		)
	end

	local originalCall = resolved.instructions[semanticOriginal.instructions[7] + 1]
	local cloneCall = resolved.instructions[semanticClone.instructions[7] + 1]
	assert(originalCall.id ~= cloneCall.id, "call clone reused source instruction identity")
	assert(originalCall.block == semanticOriginal.id and cloneCall.block == semanticClone.id, "call ownership was not remapped")
	assert(originalCall.operation.call.callee == cloneCall.operation.call.callee, "call clone changed the external callee identity")
	assert(
		originalCall.operation.call.result_arity.variadic ~= nil
			and cloneCall.operation.call.result_arity.variadic ~= nil,
		"call clone changed variadic result arity"
	)
	assert(
		originalCall.operation.call.argument_pack == semanticVarargPack.id
			and cloneCall.operation.call.argument_pack == semanticVarargPack.id,
		"call clone did not share the canonical function-vararg pack"
	)
	assert(
		#originalCall.operation.call.arguments == 6 and #cloneCall.operation.call.arguments == 6,
		"call clone changed argument arity"
	)
	assert(
		originalCall.operation.call.arguments[1] == semanticOriginalParameter.id
			and cloneCall.operation.call.arguments[1] == semanticCloneParameter.id,
		"call block-parameter argument was not remapped"
	)
	assert(
		originalCall.operation.call.arguments[2] == originalNamecallValue.id
			and cloneCall.operation.call.arguments[2] == cloneNamecallValue.id,
		"call namecall-result argument was not remapped"
	)
	assert(
		originalCall.operation.call.arguments[3] == originalProtectedSuccessStatus.id
			and cloneCall.operation.call.arguments[3] == cloneProtectedSuccessStatus.id
			and originalCall.operation.call.arguments[4] == originalProtectedSuccessValue.id
			and cloneCall.operation.call.arguments[4] == cloneProtectedSuccessValue.id,
		"call successful-protected-result arguments were not remapped"
	)
	assert(
		originalCall.operation.call.arguments[5] == originalProtectedStatus.id
			and cloneCall.operation.call.arguments[5] == cloneProtectedStatus.id
			and originalCall.operation.call.arguments[6] == originalProtectedMessage.id
			and cloneCall.operation.call.arguments[6] == cloneProtectedMessage.id,
		"call protected-result arguments were not remapped"
	)
	assert(#originalCall.results == 0 and #cloneCall.results == 0, "variadic call clone created ordinary result identities")
	assert(originalCall.pack_result ~= nil and cloneCall.pack_result ~= nil, "variadic call clone lost its result pack")
	assert(originalCall.pack_result ~= cloneCall.pack_result, "variadic call clone reused source pack identity")
	assert(#originalCall.claims == 0 and #cloneCall.claims == 0, "call clone acquired proof authority")
	assert(sameEffects(originalCall.effects, cloneCall.effects), "call clone changed effects")
	assert(sameEffects(originalCall.effects, originalNamecall.effects), "call and namecall dynamic boundaries diverged")
	assert(
		originalCall.effects.precision == "conservative"
			and originalCall.effects.reads_memory == true
			and originalCall.effects.writes_memory == true
			and originalCall.effects.may_throw == true
			and originalCall.effects.may_yield == true
			and originalCall.effects.invokes_unknown_code == true,
		"call effects lost the full dynamic invocation boundary"
	)
	assert(sameArray(originalCall.evidence, cloneCall.evidence), "call clone changed provenance")
	local originalPack = resolved.value_packs[originalCall.pack_result + 1]
	local clonePack = resolved.value_packs[cloneCall.pack_result + 1]
	assert(originalPack.id == originalCall.pack_result and clonePack.id == cloneCall.pack_result, "call pack IDs are not canonical")
	assert(originalPack.id ~= semanticVarargPack.id and clonePack.id ~= semanticVarargPack.id, "local result pack reused the function-vararg identity")
	assert(originalPack["function"] == semanticOriginal["function"] and clonePack["function"] == semanticClone["function"], "call pack crossed a function boundary")
	assert(
		originalPack.origin.instruction_result == originalCall.id
			and clonePack.origin.instruction_result == cloneCall.id,
		"call pack producer origins were not remapped"
	)
	assert(originalPack.shape.tail == "open" and clonePack.shape.tail == "open", "call pack open tail changed")
	assert(#originalPack.shape.prefix == 3 and #clonePack.shape.prefix == 3, "call pack prefix arity changed")
	for prefixIndex = 1, 3 do
		assert(sameType(originalPack.shape.prefix[prefixIndex], clonePack.shape.prefix[prefixIndex]), "call pack prefix type changed")
	end
	assert(
		originalPack.shape.prefix[1].kind == "integer"
			and originalPack.shape.prefix[2].kind == "nil_value"
			and originalPack.shape.prefix[3].kind == "integer",
		"call pack prefix lost its nil-hole domain"
	)
	assert(sameArray(originalPack.evidence, clonePack.evidence), "call pack provenance changed")

	local originalForward = resolved.instructions[semanticOriginal.instructions[8] + 1]
	local cloneForward = resolved.instructions[semanticClone.instructions[8] + 1]
	assert(originalForward.id ~= cloneForward.id, "argument-pack call clone reused source instruction identity")
	assert(originalForward.block == semanticOriginal.id and cloneForward.block == semanticClone.id, "argument-pack call ownership was not remapped")
	assert(originalForward.operation.call.callee == cloneForward.operation.call.callee, "argument-pack call changed the external callee")
	assert(
		originalForward.operation.call.result_arity.variadic ~= nil
			and cloneForward.operation.call.result_arity.variadic ~= nil,
		"argument-pack call changed variadic result arity"
	)
	assert(
		#originalForward.operation.call.arguments == 1 and #cloneForward.operation.call.arguments == 1
			and originalForward.operation.call.arguments[1] == semanticOriginalParameter.id
			and cloneForward.operation.call.arguments[1] == semanticCloneParameter.id,
		"argument-pack call fixed prefix was not remapped"
	)
	assert(
		originalForward.operation.call.argument_pack == originalPack.id
			and cloneForward.operation.call.argument_pack == clonePack.id,
		"argument-pack call did not consume the mapped producer pack"
	)
	assert(#originalForward.results == 0 and #cloneForward.results == 0, "argument-pack call created ordinary results")
	assert(originalForward.pack_result ~= nil and cloneForward.pack_result ~= nil, "argument-pack call lost its result pack")
	assert(originalForward.pack_result ~= cloneForward.pack_result, "argument-pack call reused source result-pack identity")
	assert(#originalForward.claims == 0 and #cloneForward.claims == 0, "argument-pack call acquired proof authority")
	assert(sameEffects(originalForward.effects, cloneForward.effects), "argument-pack call changed effects")
	assert(sameEffects(originalForward.effects, originalCall.effects), "producer and forwarding call effects diverged")
	assert(sameArray(originalForward.evidence, cloneForward.evidence), "argument-pack call changed provenance")
	local originalForwardPack = resolved.value_packs[originalForward.pack_result + 1]
	local cloneForwardPack = resolved.value_packs[cloneForward.pack_result + 1]
	assert(originalForwardPack.id == originalForward.pack_result and cloneForwardPack.id == cloneForward.pack_result, "forwarded pack IDs are not canonical")
	assert(originalForwardPack.id ~= originalPack.id and cloneForwardPack.id ~= clonePack.id, "forwarding call collapsed producer and result packs")
	assert(
		originalForwardPack.origin.instruction_result == originalForward.id
			and cloneForwardPack.origin.instruction_result == cloneForward.id,
		"forwarded pack producer origins were not remapped"
	)
	assert(originalForwardPack.shape.tail == "open" and cloneForwardPack.shape.tail == "open", "forwarded pack open tail changed")
	assert(#originalForwardPack.shape.prefix == 2 and #cloneForwardPack.shape.prefix == 2, "forwarded pack prefix arity changed")
	for prefixIndex = 1, 2 do
		assert(sameType(originalForwardPack.shape.prefix[prefixIndex], cloneForwardPack.shape.prefix[prefixIndex]), "forwarded pack prefix type changed")
		assert(originalForwardPack.shape.prefix[prefixIndex].kind == "integer", "forwarded pack prefix lost its integer domain")
	end
	assert(sameArray(originalForwardPack.evidence, cloneForwardPack.evidence), "forwarded pack provenance changed")

	local originalAdjust = resolved.instructions[semanticOriginal.instructions[9] + 1]
	local cloneAdjust = resolved.instructions[semanticClone.instructions[9] + 1]
	assert(originalAdjust.id ~= cloneAdjust.id, "adjust-pack clone reused source instruction identity")
	assert(originalAdjust.block == semanticOriginal.id and cloneAdjust.block == semanticClone.id, "adjust-pack ownership was not remapped")
	assert(
		originalAdjust.operation.adjust_pack == originalForwardPack.id
			and cloneAdjust.operation.adjust_pack == cloneForwardPack.id,
		"adjust-pack consumer did not use the mapped pack"
	)
	assert(#originalAdjust.results == 2 and #cloneAdjust.results == 2, "adjust-pack clone changed result arity")
	assert(originalAdjust.pack_result == nil and cloneAdjust.pack_result == nil, "adjust-pack clone created a result pack")
	assert(#originalAdjust.claims == 0 and #cloneAdjust.claims == 0, "adjust-pack clone acquired proof authority")
	assert(sameEffects(originalAdjust.effects, cloneAdjust.effects), "adjust-pack clone changed effects")
	assert(
		originalAdjust.effects.precision == "exact"
			and originalAdjust.effects.reads_memory == false
			and originalAdjust.effects.writes_memory == false
			and originalAdjust.effects.may_throw == false
			and originalAdjust.effects.may_yield == false
			and originalAdjust.effects.invokes_unknown_code == false,
		"adjust-pack effects are not exact-pure"
	)
	assert(sameArray(originalAdjust.evidence, cloneAdjust.evidence), "adjust-pack provenance changed")
	local originalCallValue = resolved.values[originalAdjust.results[1] + 1]
	local originalCallMirrorValue = resolved.values[originalAdjust.results[2] + 1]
	local cloneCallValue = resolved.values[cloneAdjust.results[1] + 1]
	local cloneCallMirrorValue = resolved.values[cloneAdjust.results[2] + 1]
	for resultIndex = 1, 2 do
		local originalValue = resolved.values[originalAdjust.results[resultIndex] + 1]
		local cloneValue = resolved.values[cloneAdjust.results[resultIndex] + 1]
		assert(originalValue.id ~= cloneValue.id, "adjust-pack clone reused source result identity")
		assert(sameType(originalValue.type, cloneValue.type), "adjust-pack clone changed result type")
		assert(originalValue.name_hint == cloneValue.name_hint, "adjust-pack clone changed result name hint")
		assert(
			originalValue.origin.instruction_result.instruction == originalAdjust.id
				and originalValue.origin.instruction_result.index == resultIndex - 1
				and cloneValue.origin.instruction_result.instruction == cloneAdjust.id
				and cloneValue.origin.instruction_result.index == resultIndex - 1,
			"adjust-pack result origins were not positionally remapped"
		)
	end

	local originalTableWrite = resolved.instructions[semanticOriginal.instructions[10] + 1]
	local cloneTableWrite = resolved.instructions[semanticClone.instructions[10] + 1]
	assert(originalTableWrite.id ~= cloneTableWrite.id, "table-write clone reused source instruction identity")
	assert(originalTableWrite.block == semanticOriginal.id and cloneTableWrite.block == semanticClone.id, "table-write ownership was not remapped")
	assert(originalTableWrite.operation.table_set.mode == "semantic" and cloneTableWrite.operation.table_set.mode == "semantic", "table-write mode changed")
	assert(
		originalTableWrite.operation.table_set.table == cloneTableWrite.operation.table_set.table
			and originalTableWrite.operation.table_set.key == cloneTableWrite.operation.table_set.key,
		"external table-write operands changed identity"
	)
	assert(
		originalTableWrite.operation.table_set.value == originalCallValue.id
			and cloneTableWrite.operation.table_set.value == cloneCallValue.id,
		"table-write value dependency was not remapped"
	)
	assert(#originalTableWrite.results == 0 and #cloneTableWrite.results == 0, "table-write clone created a value identity")
	assert(originalTableWrite.pack_result == nil and cloneTableWrite.pack_result == nil, "table-write clone introduced a pack result")
	assert(#originalTableWrite.claims == 0 and #cloneTableWrite.claims == 0, "table-write clone acquired proof authority")
	assert(sameEffects(originalTableWrite.effects, cloneTableWrite.effects), "table-write clone changed effects")
	assert(
		originalTableWrite.effects.precision == "conservative"
			and originalTableWrite.effects.reads_memory == true
			and originalTableWrite.effects.writes_memory == true
			and originalTableWrite.effects.may_throw == true
			and originalTableWrite.effects.may_yield == true
			and originalTableWrite.effects.invokes_unknown_code == true,
		"semantic table-write effects lost dynamic dispatch"
	)
	assert(sameArray(originalTableWrite.evidence, cloneTableWrite.evidence), "table-write clone changed provenance")

	local originalEnvironmentWrite = resolved.instructions[semanticOriginal.instructions[11] + 1]
	local cloneEnvironmentWrite = resolved.instructions[semanticClone.instructions[11] + 1]
	assert(originalEnvironmentWrite.id ~= cloneEnvironmentWrite.id, "environment-write clone reused source instruction identity")
	assert(
		originalEnvironmentWrite.block == semanticOriginal.id and cloneEnvironmentWrite.block == semanticClone.id,
		"environment-write ownership was not remapped"
	)
	assert(
		originalEnvironmentWrite.operation.environment_set.mode == "semantic"
			and cloneEnvironmentWrite.operation.environment_set.mode == "semantic",
		"environment-write mode changed"
	)
	assert(
		originalEnvironmentWrite.operation.environment_set.target.value
			== cloneEnvironmentWrite.operation.environment_set.target.value,
		"environment-write target changed identity"
	)
	assert(
		originalEnvironmentWrite.operation.environment_set.name == "mirror"
			and cloneEnvironmentWrite.operation.environment_set.name == "mirror",
		"environment-write name changed"
	)
	assert(
		originalEnvironmentWrite.operation.environment_set.value == originalCallMirrorValue.id
			and cloneEnvironmentWrite.operation.environment_set.value == cloneCallMirrorValue.id,
		"environment-write value dependency was not remapped"
	)
	assert(#originalEnvironmentWrite.results == 0 and #cloneEnvironmentWrite.results == 0, "environment-write clone created a value identity")
	assert(originalEnvironmentWrite.pack_result == nil and cloneEnvironmentWrite.pack_result == nil, "environment-write clone introduced a pack result")
	assert(#originalEnvironmentWrite.claims == 0 and #cloneEnvironmentWrite.claims == 0, "environment-write clone acquired proof authority")
	assert(sameEffects(originalEnvironmentWrite.effects, cloneEnvironmentWrite.effects), "environment-write clone changed effects")
	assert(sameEffects(originalEnvironmentWrite.effects, originalTableWrite.effects), "dynamic write summaries diverged")
	assert(sameArray(originalEnvironmentWrite.evidence, cloneEnvironmentWrite.evidence), "environment-write clone changed provenance")

	local originalPlaceWrite = resolved.instructions[semanticOriginal.instructions[12] + 1]
	local clonePlaceWrite = resolved.instructions[semanticClone.instructions[12] + 1]
	assert(originalPlaceWrite.id ~= clonePlaceWrite.id, "place-write clone reused source instruction identity")
	assert(originalPlaceWrite.block == semanticOriginal.id and clonePlaceWrite.block == semanticClone.id, "place-write ownership was not remapped")
	assert(originalPlaceWrite.operation.place_write.place == clonePlaceWrite.operation.place_write.place, "place-write changed lexical cell identity")
	assert(
		originalPlaceWrite.operation.place_write.value == originalCallValue.id
			and clonePlaceWrite.operation.place_write.value == cloneCallValue.id,
		"place-write input dependency was not remapped"
	)
	assert(#originalPlaceWrite.results == 0 and #clonePlaceWrite.results == 0, "place-write clone created a value identity")
	assert(originalPlaceWrite.pack_result == nil and clonePlaceWrite.pack_result == nil, "place-write clone introduced a pack result")
	assert(#originalPlaceWrite.claims == 0 and #clonePlaceWrite.claims == 0, "place-write clone acquired proof authority")
	assert(sameEffects(originalPlaceWrite.effects, clonePlaceWrite.effects), "place-write clone changed effects")
	assert(
		originalPlaceWrite.effects.precision == "exact"
			and originalPlaceWrite.effects.reads_memory == false
			and originalPlaceWrite.effects.writes_memory == true
			and originalPlaceWrite.effects.may_throw == false
			and originalPlaceWrite.effects.may_yield == false
			and originalPlaceWrite.effects.invokes_unknown_code == false,
		"place-write effects are not exact"
	)
	assert(sameArray(originalPlaceWrite.evidence, clonePlaceWrite.evidence), "place-write clone changed provenance")

	local originalPlaceRead = resolved.instructions[semanticOriginal.instructions[13] + 1]
	local clonePlaceRead = resolved.instructions[semanticClone.instructions[13] + 1]
	assert(originalPlaceRead.id ~= clonePlaceRead.id, "place-read clone reused source instruction identity")
	assert(originalPlaceRead.block == semanticOriginal.id and clonePlaceRead.block == semanticClone.id, "place-read ownership was not remapped")
	assert(originalPlaceRead.operation.place_read == clonePlaceRead.operation.place_read, "place-read changed lexical cell identity")
	local place = resolved.places[originalPlaceRead.operation.place_read + 1]
	assert(place.origin["local"] ~= nil, "node splitting admitted a non-local conformance place")
	assert(place["function"] == semanticOriginal["function"], "place-read crossed a function boundary")
	assert(sameEffects(originalPlaceRead.effects, clonePlaceRead.effects), "place-read clone changed effects")
	assert(
		originalPlaceRead.effects.precision == "exact"
			and originalPlaceRead.effects.reads_memory == true
			and originalPlaceRead.effects.writes_memory == false
			and originalPlaceRead.effects.may_throw == false
			and originalPlaceRead.effects.may_yield == false
			and originalPlaceRead.effects.invokes_unknown_code == false,
		"place-read effects are not exact"
	)
	assert(#originalPlaceRead.results == 1 and #clonePlaceRead.results == 1, "place-read clone changed result arity")
	assert(originalPlaceRead.pack_result == nil and clonePlaceRead.pack_result == nil, "place-read clone introduced a pack result")
	assert(#originalPlaceRead.claims == 0 and #clonePlaceRead.claims == 0, "place-read clone acquired proof authority")
	assert(sameArray(originalPlaceRead.evidence, clonePlaceRead.evidence), "place-read clone changed provenance")
	local originalPlaceValue = resolved.values[originalPlaceRead.results[1] + 1]
	local clonePlaceValue = resolved.values[clonePlaceRead.results[1] + 1]
	assert(originalPlaceValue.id ~= clonePlaceValue.id, "place-read clone reused source result identity")
	assert(sameType(originalPlaceValue.type, clonePlaceValue.type), "place-read clone changed result type")
	assert(originalPlaceValue.name_hint == clonePlaceValue.name_hint, "place-read clone changed result name hint")
	assert(
		originalPlaceValue.origin.instruction_result.instruction == originalPlaceRead.id
			and clonePlaceValue.origin.instruction_result.instruction == clonePlaceRead.id,
		"place-read result origins were not remapped"
	)

	local originalOperand = originalPlaceValue.id
	local cloneOperand = clonePlaceValue.id
	for instructionIndex = 14, 15 do
		local originalInstruction = resolved.instructions[semanticOriginal.instructions[instructionIndex] + 1]
		local cloneInstruction = resolved.instructions[semanticClone.instructions[instructionIndex] + 1]
		assert(originalInstruction.id ~= cloneInstruction.id, "semantic clone reused source instruction identity")
		assert(originalInstruction.block == semanticOriginal.id and cloneInstruction.block == semanticClone.id, "semantic instruction ownership was not remapped")
		assert(originalInstruction.operation.unary.operator == "negate", "semantic source operation changed")
		assert(cloneInstruction.operation.unary.operator == "negate", "semantic clone operation changed")
		assert(originalInstruction.operation.unary.mode == "semantic" and cloneInstruction.operation.unary.mode == "semantic", "semantic mode was not preserved")
		assert(
			originalInstruction.operation.unary.operand == originalOperand
				and cloneInstruction.operation.unary.operand == cloneOperand,
			"semantic operand dependency was not remapped"
		)
		assert(#originalInstruction.results == 1 and #cloneInstruction.results == 1, "semantic clone changed result arity")
		assert(originalInstruction.pack_result == nil and cloneInstruction.pack_result == nil, "semantic clone introduced a pack result")
		assert(#originalInstruction.claims == 0 and #cloneInstruction.claims == 0, "semantic clone acquired proof authority")
		assert(sameEffects(originalInstruction.effects, cloneInstruction.effects), "semantic clone changed effects")
		assert(sameArray(originalInstruction.evidence, cloneInstruction.evidence), "semantic clone changed instruction provenance")
		local originalValue = resolved.values[originalInstruction.results[1] + 1]
		local cloneValue = resolved.values[cloneInstruction.results[1] + 1]
		assert(originalValue.id ~= cloneValue.id, "semantic clone reused source result identity")
		assert(sameType(originalValue.type, cloneValue.type), "semantic clone changed result type")
		assert(originalValue.name_hint == cloneValue.name_hint, "semantic clone changed result name hint")
		assert(
			originalValue.origin.instruction_result.instruction == originalInstruction.id
				and cloneValue.origin.instruction_result.instruction == cloneInstruction.id,
			"semantic result origins were not remapped"
		)
		originalOperand = originalValue.id
		cloneOperand = cloneValue.id
	end
	assert(semanticOriginal.terminator.jump.target == semanticClone.terminator.jump.target, "semantic clone changed its successor")
	assert(sameArray(semanticOriginal.terminator.jump.arguments, { originalOperand }), "semantic source terminator lost its result")
	assert(sameArray(semanticClone.terminator.jump.arguments, { cloneOperand }), "semantic clone terminator lost its mapped result")
	local semanticLiveEdge = currentEdge(resolved, semanticRewrite)
	assert(semanticLiveEdge.target == semanticClone.id, "effect-preserving semantic clone was incorrectly bypassed")
	assert(forwarding.source ~= semanticRewrite.source or forwarding.kind ~= semanticRewrite.kind, "semantic clone acquired copy forwarding")

	local selfRewrite = resolved.edge_rewrites[3]
	assert(selfRewrite.id == 2 and selfRewrite.rule == "node_split", "self-loop entry used the wrong rewrite authority")
	assert(selfRewrite.certificate == nil, "self-loop node splitting acquired a solver certificate")
	assert(#selfRewrite.from.arguments == 1, "self-loop entry lost its incoming argument")
	assert(sameArray(selfRewrite.from.arguments, selfRewrite.to.arguments), "self-loop node splitting changed incoming arguments")
	local selfOriginal = resolved.blocks[selfRewrite.from.target + 1]
	local selfClone = resolved.blocks[selfRewrite.to.target + 1]
	assert(selfOriginal.name_hint == "self_loop_secondary" and selfClone.name_hint == selfOriginal.name_hint, "self-loop clone changed identity")
	assert(selfOriginal["function"] == selfClone["function"], "self-loop clone crossed a function boundary")
	assert(#selfOriginal.parameters == 1 and #selfClone.parameters == 1, "self-loop clone changed parameter arity")
	assert(#selfOriginal.instructions == 4 and #selfClone.instructions == 4, "self-loop clone changed instruction arity")
	assert(sameArray(selfOriginal.evidence, selfClone.evidence), "self-loop clone changed structural provenance")
	local selfOriginalParameter = resolved.values[selfOriginal.parameters[1] + 1]
	local selfCloneParameter = resolved.values[selfClone.parameters[1] + 1]
	assert(selfOriginalParameter.id ~= selfCloneParameter.id, "self-loop clone reused its source parameter")
	assert(sameType(selfOriginalParameter.type, selfCloneParameter.type), "self-loop clone changed parameter type")
	assert(
		selfOriginalParameter.origin.block_parameter.block == selfOriginal.id
			and selfCloneParameter.origin.block_parameter.block == selfClone.id,
		"self-loop parameter origins were not remapped"
	)
	for instructionIndex = 1, 4 do
		local selfOriginalInstruction = resolved.instructions[selfOriginal.instructions[instructionIndex] + 1]
		local selfCloneInstruction = resolved.instructions[selfClone.instructions[instructionIndex] + 1]
		assert(selfOriginalInstruction.id ~= selfCloneInstruction.id, "self-loop clone reused an instruction identity")
		assert(selfOriginalInstruction.block == selfOriginal.id and selfCloneInstruction.block == selfClone.id, "self-loop instruction ownership was not remapped")
		assert(#selfOriginalInstruction.results == 1 and #selfCloneInstruction.results == 1, "self-loop clone changed result arity")
		assert(sameEffects(selfOriginalInstruction.effects, selfCloneInstruction.effects), "self-loop clone changed effects")
		assert(sameArray(selfOriginalInstruction.evidence, selfCloneInstruction.evidence), "self-loop clone changed instruction provenance")
		local selfOriginalValue = resolved.values[selfOriginalInstruction.results[1] + 1]
		local selfCloneValue = resolved.values[selfCloneInstruction.results[1] + 1]
		assert(selfOriginalValue.id ~= selfCloneValue.id, "self-loop clone reused a result identity")
		assert(sameType(selfOriginalValue.type, selfCloneValue.type), "self-loop clone changed result type")
		assert(selfOriginalValue.name_hint == selfCloneValue.name_hint, "self-loop clone changed result name hint")
	end
	local selfOriginalNext = resolved.instructions[selfOriginal.instructions[2] + 1]
	local selfCloneNext = resolved.instructions[selfClone.instructions[2] + 1]
	local selfOriginalNextValue = selfOriginalNext.results[1]
	local selfCloneNextValue = selfCloneNext.results[1]
	assert(
		selfOriginalNext.operation.binary.left == selfOriginalParameter.id
			and selfCloneNext.operation.binary.left == selfCloneParameter.id,
		"self-loop arithmetic did not remap its parameter"
	)
	local selfOriginalCondition = resolved.instructions[selfOriginal.instructions[4] + 1].results[1]
	local selfCloneCondition = resolved.instructions[selfClone.instructions[4] + 1].results[1]
	assert(selfOriginal.terminator.branch.condition == selfOriginalCondition, "source self-loop lost its condition")
	assert(selfClone.terminator.branch.condition == selfCloneCondition, "cloned self-loop lost its mapped condition")
	assert(selfOriginal.terminator.branch.then_edge.target == selfOriginal.id, "source self edge changed target")
	assert(selfClone.terminator.branch.then_edge.target == selfClone.id, "cloned self edge points back to the source")
	assert(selfOriginal.terminator.branch.else_edge.target == selfClone.terminator.branch.else_edge.target, "self-loop clone changed its primary successor")
	assert(sameArray(selfOriginal.terminator.branch.then_edge.arguments, { selfOriginalNextValue }), "source self edge lost its next value")
	assert(sameArray(selfClone.terminator.branch.then_edge.arguments, { selfCloneNextValue }), "cloned self edge lost its mapped next value")
	assert(sameArray(selfOriginal.terminator.branch.else_edge.arguments, { selfOriginalNextValue }), "source primary edge lost its next value")
	assert(sameArray(selfClone.terminator.branch.else_edge.arguments, { selfCloneNextValue }), "cloned primary edge lost its mapped next value")
	local selfLiveEdge = currentEdge(resolved, selfRewrite)
	assert(selfLiveEdge.target == selfClone.id, "live CFG does not enter the authenticated self-loop clone")
	assert(forwarding.source ~= selfRewrite.source or forwarding.kind ~= selfRewrite.kind, "self-loop clone acquired copy forwarding")

	local generated = fs.readFile(generatedPath)
	local helperAudit = string.gsub(generated, "__lifter_pcall", "")
	helperAudit = string.gsub(helperAudit, "__lifter_xpcall", "")
	helperAudit = string.gsub(helperAudit, "__lifter_escape_%d+", "")
	assert(string.find(helperAudit, "__lifter", 1, true) == nil, "node splitting emitted an unknown backend helper")
	assert(string.find(generated, "local __lifter_pcall = pcall", 1, true) ~= nil, "pcall target capability was not captured")
	assert(string.find(generated, "local __lifter_xpcall = xpcall", 1, true) ~= nil, "xpcall target capability was not captured")
	assert(string.find(generated, "counter", 1, true) ~= nil, "finite loop state disappeared from readable Luau")
	assert(string.find(generated, "semantic_irreducible_loop", 1, true) ~= nil, "semantic loop disappeared from readable Luau")
	assert(string.find(generated, "self_loop_irreducible_loop", 1, true) ~= nil, "self-loop worker disappeared from readable Luau")
	assert(string.find(generated, ":observe(", 1, true) ~= nil, "native namecall disappeared from readable Luau")
	assert(string.find(generated, "__lifter_pcall(", 1, true) ~= nil, "successful protected call disappeared from readable Luau")
	assert(string.find(generated, "__lifter_xpcall(", 1, true) ~= nil, "handled protected call disappeared from readable Luau")
	assert(string.find(generated, "observer", 1, true) ~= nil, "cloned invocation disappeared from readable Luau")
	assert(string.find(generated, "forwarder", 1, true) ~= nil, "argument-pack forwarding call disappeared from readable Luau")
end

return table.freeze({ run = audit })
