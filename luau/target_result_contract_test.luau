--!strict

local RecoveryManifest = require("./recovery_manifest")
local TargetProofBundle = require("./target_proof_bundle")
local TargetRecovery = require("./target_recovery")
local AstFrontend = require("./ast_frontend")
local LifterIR = require("./lifter_ir")
local TemporalSupport = require("./temporal_test_support")

type Record = { [string]: any }

local source = "opaque-result-source"
local sourceDigest = TargetRecovery.sha256(source)
local producerLocation = "0,34 - 0,51"
local selectedCallLocation = "1,7 - 1,37"
local origin = { intrinsic = "pcall" }
local proofContent = "opaque provider result two is the protected-call capability"

local resultProofDigest = TargetRecovery.targetResultProofDigest(
	sourceDigest,
	producerLocation,
	2,
	origin,
	proofContent
)
assert(#resultProofDigest == 64 and string.match(resultProofDigest, "^[0-9a-f]+$") ~= nil, "result proof digest is not SHA-256")
assert(
	resultProofDigest == "e462d08a7bc9f1a19d4197aa368f47556cbc8e192e47f318493dace78408bb88",
	"result proof digest vector changed"
)
assert(
	resultProofDigest ~= TargetRecovery.targetResultProofDigest(sourceDigest, producerLocation, 1, origin, proofContent)
		and resultProofDigest ~= TargetRecovery.targetResultProofDigest(sourceDigest, selectedCallLocation, 2, origin, proofContent)
		and resultProofDigest ~= TargetRecovery.targetResultProofDigest(sourceDigest, producerLocation, 2, { intrinsic = "error" }, proofContent)
		and resultProofDigest ~= TargetRecovery.targetResultProofDigest(sourceDigest, producerLocation, 2, origin, proofContent .. "!"),
	"result proof digest is not bound to source, producer, ordinal, origin, and content"
)
assert(
	TargetProofBundle.targetOriginKey(origin) == TargetProofBundle.targetOriginKey({ intrinsic = "pcall" })
		and TargetProofBundle.targetOriginKey(origin) ~= TargetProofBundle.targetOriginKey({ intrinsic = "error" }),
	"target origin key is not canonical"
)

local ignoredDeclaration: Record = {
	type = "AstLocal",
	name = "_",
	location = "0,6 - 0,7",
}
local targetDeclaration: Record = {
	type = "AstLocal",
	name = "unresolvedResultTarget",
	location = "0,9 - 0,31",
}
local producerCall: Record = {
	type = "AstExprCall",
	location = producerLocation,
	func = {
		type = "AstExprIndexName",
		location = "0,34 - 0,49",
		expr = { type = "AstExprGlobal", location = "0,34 - 0,42", global = "provider" },
		index = "target",
		indexLocation = "0,43 - 0,49",
	},
	args = {},
	self = false,
	argLocation = "0,49 - 0,51",
}
local callback: Record = {
	type = "AstExprFunction",
	location = "1,31 - 1,52",
	args = {},
	vararg = false,
	body = {
		type = "AstStatBlock",
		location = "1,41 - 1,49",
		body = {
			{
				type = "AstStatReturn",
				location = "1,42 - 1,48",
				list = { { type = "AstExprConstantNumber", location = "1,47 - 1,48", value = 1 } },
			},
		},
	},
}
local selectedCall: Record = {
	type = "AstExprCall",
	location = selectedCallLocation,
	func = {
		type = "AstExprLocal",
		location = "1,7 - 1,29",
		["local"] = targetDeclaration,
	},
	args = { callback },
	self = false,
	argLocation = "1,29 - 1,31",
}
local declarationStatement: Record = {
	type = "AstStatLocal",
	location = "0,0 - 0,51",
	vars = { ignoredDeclaration, targetDeclaration },
	values = { producerCall },
}
local returnStatement: Record = {
	type = "AstStatReturn",
	location = "1,0 - 1,37",
	list = { selectedCall },
}
local document: Record = {
	root = {
		type = "AstStatBlock",
		location = "0,0 - 2,0",
		body = { declarationStatement, returnStatement },
	},
}

local function deepClone(value: any): any
	if type(value) ~= "table" then
		return value
	end
	local result = {}
	for key, child in value do
		result[deepClone(key)] = deepClone(child)
	end
	return result
end

local function bindContractProof(contract: any)
	contract.proof.evidence.digest = TargetRecovery.targetResultProofDigest(
		sourceDigest,
		contract.producer_call_location,
		contract.result_ordinal,
		contract.origin,
		contract.proof.content
	)
end

local function manifestRecord(): any
	return {
		schema_version = "lifter_recovery_manifest_v17",
		target_recovery = {
			source_sha256 = sourceDigest,
			call_site_count = 2,
			unresolved_call_count = 1,
			lowered_unresolved_call_count = 1,
			unresolved_target_selectors = {
				{ kind = "local_name", value = "unresolvedResultTarget" },
			},
			target_resolutions = {
				{
					call_location = selectedCallLocation,
					origin = { intrinsic = "pcall" },
					evidence = {
						kind = "dynamic_fixture",
						locator = "fixture:result-resolution-source",
						digest = sourceDigest,
					},
				},
			},
			result_contracts = {
				{
					producer_call_location = producerLocation,
					result_ordinal = 2,
					origin = { intrinsic = "pcall" },
					evidence = {
						kind = "dynamic_fixture",
						locator = "fixture:result-contract-source",
						digest = sourceDigest,
					},
					proof = {
						content = proofContent,
						evidence = {
							kind = "frontend_proof",
							locator = "fixture:result-contract-proof",
							digest = resultProofDigest,
						},
					},
				},
			},
			detail = "selected target requires an authenticated opaque producer result",
			evidence = {
				kind = "structural_derivation",
				locator = "fixture:result-contract-frontier",
				digest = sourceDigest,
			},
		},
	}
end

local function decode(record: any, label: string): any
	local manifest = RecoveryManifest.fromDecoded(record, label)
	assert(manifest.target_recovery ~= nil, `{label} lost target recovery`)
	return manifest.target_recovery
end

local recovery = decode(manifestRecord(), "result-contract-manifest")
assert(recovery.result_contracts ~= nil and #recovery.result_contracts == 1, "V17 lost its result contract")
local verified = TargetRecovery.verify(document, source, recovery)
local verifiedSite = verified.by_call_location[selectedCallLocation]
assert(verifiedSite ~= nil and verifiedSite.resolution ~= nil, "result contract did not resolve the selected call")
local resultEvidence = (verifiedSite :: any).resolution.result_contract_evidence
assert(type(resultEvidence) == "table" and #resultEvidence == 2, "result contract provenance was not attached")
assert(
	resultEvidence[1].locator == "fixture:result-contract-source"
		and resultEvidence[2].locator == "fixture:result-contract-proof",
	"result contract source and proof provenance changed"
)
assert(
	(verifiedSite :: any).resolution.temporal_identity.definition_kind == "declaration"
		and (verifiedSite :: any).resolution.temporal_identity.definition_location == declarationStatement.location,
	"result contract did not bind the selected local to its existing declaration"
)

local oldVersion = manifestRecord()
oldVersion.schema_version = "lifter_recovery_manifest_v16"
assert(
	not pcall(RecoveryManifest.fromDecoded, oldVersion, "v16-result-contract"),
	"V16 accepted a V17 result contract field"
)

local duplicate = manifestRecord()
table.insert(duplicate.target_recovery.result_contracts, deepClone(duplicate.target_recovery.result_contracts[1]))
assert(
	not pcall(RecoveryManifest.fromDecoded, duplicate, "duplicate-result-contract"),
	"V17 accepted a duplicate producer result ordinal"
)

local staleProof = manifestRecord()
staleProof.target_recovery.result_contracts[1].proof.content ..= " tampered"
assert(not pcall(RecoveryManifest.fromDecoded, staleProof, "stale-result-proof"), "V17 accepted mutated proof content")

local wrongOrdinal = manifestRecord()
wrongOrdinal.target_recovery.result_contracts[1].result_ordinal = 1
bindContractProof(wrongOrdinal.target_recovery.result_contracts[1])
assert(
	not pcall(TargetRecovery.verify, document, source, decode(wrongOrdinal, "wrong-result-ordinal")),
	"target recovery accepted the wrong opaque result ordinal"
)

local wrongCall = manifestRecord()
wrongCall.target_recovery.result_contracts[1].producer_call_location = selectedCallLocation
bindContractProof(wrongCall.target_recovery.result_contracts[1])
assert(
	not pcall(TargetRecovery.verify, document, source, decode(wrongCall, "wrong-result-call")),
	"target recovery rebound a contract to a different call"
)

local absentCall = manifestRecord()
absentCall.target_recovery.result_contracts[1].producer_call_location = "9,0 - 9,8"
bindContractProof(absentCall.target_recovery.result_contracts[1])
assert(
	not pcall(TargetRecovery.verify, document, source, decode(absentCall, "absent-result-call")),
	"target recovery accepted an absent producer call"
)

local nonCall = manifestRecord()
nonCall.target_recovery.result_contracts[1].producer_call_location = targetDeclaration.location
bindContractProof(nonCall.target_recovery.result_contracts[1])
assert(
	not pcall(TargetRecovery.verify, document, source, decode(nonCall, "non-call-result-producer")),
	"target recovery accepted a non-call producer location"
)

local unused = manifestRecord()
local unusedContract = deepClone(unused.target_recovery.result_contracts[1])
unusedContract.result_ordinal = 1
unusedContract.origin = { intrinsic = "error" }
unusedContract.evidence.locator = "fixture:unused-result-contract-source"
unusedContract.proof.evidence.locator = "fixture:unused-result-contract-proof"
bindContractProof(unusedContract)
table.insert(unused.target_recovery.result_contracts, unusedContract)
assert(
	not pcall(TargetRecovery.verify, document, source, decode(unused, "unused-result-contract")),
	"target recovery accepted an unused result contract"
)

local sharedResolutionEvidence = manifestRecord()
sharedResolutionEvidence.target_recovery.result_contracts[1].evidence.locator = "fixture:result-resolution-source"
assert(
	not pcall(TargetRecovery.verify, document, source, decode(sharedResolutionEvidence, "shared-result-source-evidence")),
	"target recovery accepted result evidence reused as promoted-call evidence"
)

local mutatedRecovery: any = deepClone(recovery)
mutatedRecovery.result_contracts[1].proof.content ..= " post-decode mutation"
assert(
	not pcall(TargetRecovery.verify, document, source, mutatedRecovery),
	"target recovery trusted result proof content mutated after manifest decoding"
)

local function opaqueProducerCall(prefix: string): Record
	return {
		type = "AstExprCall",
		location = prefix .. "-producer-call",
		func = TemporalSupport.globalExpression("opaqueProducer", prefix .. "-producer"),
		args = {},
		self = false,
	}
end

local function returnValues(values: { Record }, prefix: string): Record
	return { type = "AstStatReturn", location = prefix .. "-return", list = values }
end

local function projectedDeclaration(value: Record, prefix: string): (Record, Record)
	local ignored = TemporalSupport.declaration(prefix .. "Ignored", prefix .. "-ignored")
	local target = TemporalSupport.declaration(prefix .. "Target", prefix .. "-target")
	return target, {
		type = "AstStatLocal",
		location = prefix .. "-projection",
		vars = { ignored, target },
		values = { value },
	}
end

local function verifyComposedResult(
	caseName: string,
	documentValue: Record,
	producerCallValue: Record,
	selectedCall: Record,
	selectedDeclaration: Record,
	callCount: number,
	expectedDefinitionKind: string
)
	local caseSource = "target-result-composition:" .. caseName
	local caseDigest = TargetRecovery.sha256(caseSource)
	local caseOrigin = { intrinsic = "pcall" }
	local caseProof = "authenticated producer result survives " .. caseName
	local selectedName = selectedDeclaration.name
	assert(type(selectedName) == "string", `{caseName} selected declaration has no name`)
	local selectors: { TargetRecovery.TargetSelector } = {
		{ kind = "local_name", value = selectedName },
	}
	local spec: TargetRecovery.Spec = {
		source_sha256 = caseDigest,
		call_site_count = callCount,
		unresolved_call_count = 1,
		lowered_unresolved_call_count = 1,
		allow_direct_target_expressions = true,
		require_independent_proof = false,
		unresolved_target_selectors = selectors,
		target_resolutions = {
			{
				call_location = selectedCall.location,
				origin = caseOrigin,
				evidence = {
					kind = "dynamic_fixture",
					locator = "fixture:" .. caseName .. ":resolution",
					digest = caseDigest,
				},
			},
		},
		result_contracts = {
			{
				producer_call_location = producerCallValue.location,
				result_ordinal = 2,
				origin = caseOrigin,
				evidence = {
					kind = "dynamic_fixture",
					locator = "fixture:" .. caseName .. ":contract",
					digest = caseDigest,
				},
				proof = {
					content = caseProof,
					evidence = {
						kind = "frontend_proof",
						locator = "fixture:" .. caseName .. ":proof",
						digest = TargetRecovery.targetResultProofDigest(
							caseDigest,
							producerCallValue.location,
							2,
							caseOrigin,
							caseProof
						),
					},
				},
			},
		},
		detail = "composed authenticated producer result",
		evidence = {
			kind = "structural_derivation",
			locator = "fixture:" .. caseName .. ":frontier",
			digest = caseDigest,
		},
	}
	local verifiedCase = TargetRecovery.verify(documentValue, caseSource, spec)
	local site = verifiedCase.by_call_location[selectedCall.location]
	assert(site ~= nil and site.resolution ~= nil, `{caseName} did not resolve its selected call`)
	local resolution = (site :: any).resolution
	assert(
		resolution.temporal_identity ~= nil
			and resolution.temporal_identity.definition_kind == expectedDefinitionKind,
		`{caseName} lost its temporal definition kind`
	)
	assert(
		type(resolution.result_contract_evidence) == "table"
			and #resolution.result_contract_evidence == 2,
		`{caseName} lost result-contract provenance`
	)
end

local function expectRejectedComposedResult(
	caseName: string,
	documentValue: Record,
	producerCallValue: Record,
	selectedCallValue: Record,
	selectedDeclaration: Record,
	callCount: number,
	expected: string
)
	local ok, message = pcall(function()
		verifyComposedResult(
			caseName,
			documentValue,
			producerCallValue,
			selectedCallValue,
			selectedDeclaration,
			callCount,
			"declaration"
		)
	end)
	assert(not ok, `{caseName} invented an authenticated result transfer`)
	assert(
		string.find(tostring(message), expected, 1, true) ~= nil,
		`{caseName} rejection lost its semantic diagnostic: {tostring(message)}`
	)
end

do
	local producer = opaqueProducerCall("result-alias")
	local target, projection = projectedDeclaration(producer, "result-alias")
	local alias = TemporalSupport.declaration("resultAliasSelected", "result-alias-selected")
	local aliasCall = TemporalSupport.callExpression(alias, "result-alias-call")
	verifyComposedResult("result-alias", TemporalSupport.document({
		projection,
		TemporalSupport.localStatement(
			alias,
			"result-alias-declaration",
			TemporalSupport.localExpression(target, "result-alias-value")
		),
		TemporalSupport.callStatement(aliasCall, "result-alias-call-statement"),
	}), producer, aliasCall, alias, 2, "declaration")
end

do
	local producer = opaqueProducerCall("result-assignment")
	local ignored = TemporalSupport.declaration("resultAssignmentIgnored", "result-assignment-ignored")
	local target = TemporalSupport.declaration("resultAssignmentSelected", "result-assignment-selected")
	local assignmentCall = TemporalSupport.callExpression(target, "result-assignment-call")
	verifyComposedResult("result-assignment", TemporalSupport.document({
		{
			type = "AstStatLocal",
			location = "result-assignment-declaration",
			vars = { ignored, target },
			values = {},
		},
		{
			type = "AstStatAssign",
			location = "result-assignment-write",
			vars = {
				TemporalSupport.localExpression(ignored, "result-assignment-ignored-write"),
				TemporalSupport.localExpression(target, "result-assignment-target-write"),
			},
			values = { producer },
		},
		TemporalSupport.callStatement(assignmentCall, "result-assignment-call-statement"),
	}), producer, assignmentCall, target, 2, "assignment")
end

local function forwardedResultUse(caseName: string, invocation: Record): (Record, Record, Record)
	local target, projection = projectedDeclaration(invocation, caseName)
	local forwardedCall = TemporalSupport.callExpression(target, caseName .. "-call")
	return TemporalSupport.document({
		projection,
		TemporalSupport.callStatement(forwardedCall, caseName .. "-call-statement"),
	}), forwardedCall, target
end

local function verifyForwardedResult(caseName: string, functionValue: Record, invocation: Record, producer: Record)
	local documentValue, forwardedCall, target = forwardedResultUse(caseName, invocation)
	verifyComposedResult(caseName, documentValue, producer, forwardedCall, target, 3, "declaration")
	assert(functionValue.body ~= nil, `{caseName} lost its forwarding function`)
end

do
	local producer = opaqueProducerCall("result-direct-return")
	local functionValue, invocation = TemporalSupport.invocationFromBody({
		returnValues({ producer }, "result-direct-return"),
	}, "result-direct-return", nil, nil)
	verifyForwardedResult("result-direct-return", functionValue, invocation, producer)
end

do
	local producer = opaqueProducerCall("result-parameter-forward")
	local first = TemporalSupport.declaration("resultParameterFirst", "result-parameter-first")
	local second = TemporalSupport.declaration("resultParameterSecond", "result-parameter-second")
	local functionValue, invocation = TemporalSupport.invocationFromBody({
		returnValues({
			TemporalSupport.localExpression(first, "result-parameter-first-read"),
			TemporalSupport.localExpression(second, "result-parameter-second-read"),
		}, "result-parameter-forward"),
	}, "result-parameter-forward", nil, { producer })
	functionValue.args = { first, second }
	functionValue.vararg = false
	verifyForwardedResult("result-parameter-forward", functionValue, invocation, producer)
end

do
	local producer = opaqueProducerCall("result-vararg-forward")
	local functionValue, invocation = TemporalSupport.invocationFromBody({
		returnValues({
			{ type = "AstExprVarargs", location = "result-vararg-forward-read" },
		}, "result-vararg-forward"),
	}, "result-vararg-forward", nil, { producer })
	functionValue.vararg = true
	verifyForwardedResult("result-vararg-forward", functionValue, invocation, producer)
end

do
	local caseName = "result-nonfinal-return"
	local producer = opaqueProducerCall(caseName)
	local _, invocation = TemporalSupport.invocationFromBody({
		returnValues({
			producer,
			TemporalSupport.globalExpression("differentTarget", caseName .. "-different"),
		}, caseName),
	}, caseName, nil, nil)
	local documentValue, forwardedCall, target = forwardedResultUse(caseName, invocation)
	expectRejectedComposedResult(
		caseName,
		documentValue,
		producer,
		forwardedCall,
		target,
		3,
		"does not match its authenticated origin"
	)
end

do
	local caseName = "result-nonfinal-argument"
	local producer = opaqueProducerCall(caseName)
	local first = TemporalSupport.declaration("resultNonfinalFirst", caseName .. "-first")
	local second = TemporalSupport.declaration("resultNonfinalSecond", caseName .. "-second")
	local functionValue, invocation = TemporalSupport.invocationFromBody({
		returnValues({ TemporalSupport.localExpression(second, caseName .. "-second-read") }, caseName),
	}, caseName, nil, {
		producer,
		TemporalSupport.globalExpression("differentTarget", caseName .. "-different"),
	})
	functionValue.args = { first, second }
	functionValue.vararg = false
	local documentValue, forwardedCall, target = forwardedResultUse(caseName, invocation)
	expectRejectedComposedResult(
		caseName,
		documentValue,
		producer,
		forwardedCall,
		target,
		3,
		"does not match its authenticated origin"
	)
end

do
	local caseName = "result-nonfinal-vararg"
	local producer = opaqueProducerCall(caseName)
	local functionValue, invocation = TemporalSupport.invocationFromBody({
		returnValues({ { type = "AstExprVarargs", location = caseName .. "-read" } }, caseName),
	}, caseName, nil, {
		producer,
		TemporalSupport.globalExpression("differentTarget", caseName .. "-different"),
	})
	functionValue.vararg = true
	local documentValue, forwardedCall, target = forwardedResultUse(caseName, invocation)
	expectRejectedComposedResult(
		caseName,
		documentValue,
		producer,
		forwardedCall,
		target,
		3,
		"does not match its authenticated origin"
	)
end

local lifted = AstFrontend.tryLift(document, {
	program_id = "opaque-result-contract",
	source_name = "opaque-result-contract",
	source_text = source,
	target_recovery = recovery,
})
assert(
	lifted.program ~= nil and #lifted.diagnostics == 0,
	`result-contract frontend lift failed: {if lifted.diagnostics[1] ~= nil then lifted.diagnostics[1].code .. ": " .. lifted.diagnostics[1].detail else "no diagnostic"}`
)
local encoded = LifterIR.encodeJson(lifted.program :: any)
for _, privateValue in {
	"result_contracts",
	"producer_call_location",
	"result_ordinal",
	"lifter_recovery_manifest_v17",
	proofContent,
} do
	assert(string.find(encoded, privateValue, 1, true) == nil, `frontend-private result field leaked into IR: {privateValue}`)
end
local admittedProgram = lifted.program :: any
local resolutionEvidenceId: number? = nil
local contractEvidenceId: number? = nil
local contractProofEvidenceId: number? = nil
for _, evidence in admittedProgram.evidence do
	if evidence.locator == "fixture:result-resolution-source" then
		resolutionEvidenceId = evidence.id
	elseif evidence.locator == "fixture:result-contract-source" then
		contractEvidenceId = evidence.id
	elseif evidence.locator == "fixture:result-contract-proof" then
		contractProofEvidenceId = evidence.id
	end
end
local foundAuthenticatedCall = false
for _, instruction in admittedProgram.instructions do
	if instruction.operation.protected_call ~= nil
		and table.find(instruction.evidence, resolutionEvidenceId)
		and table.find(instruction.evidence, contractEvidenceId)
		and table.find(instruction.evidence, contractProofEvidenceId)
	then
		foundAuthenticatedCall = true
	end
end
assert(foundAuthenticatedCall, "promoted call lost resolution, result-contract, or proof provenance")

return true
