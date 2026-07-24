--!strict

local LifterIR = require("./lifter_ir")
local IntrinsicBindings = require("./intrinsic_bindings")
local RecoveryAdmission = require("./recovery_admission")
local TargetRecovery = require("./target_recovery")
local TargetProofBundle = require("./target_proof_bundle")

local RecoveryManifest = {}

type Record = { [string]: any }

export type Evidence = {
	kind: string,
	locator: string,
	digest: string?,
}

export type IntrinsicBinding = {
	path: string,
	evidence: Evidence,
}

export type TargetSelector = {
	kind: "local_name" | "local_name_prefix" | "global_name" | "global_name_prefix",
	value: string,
}

export type TargetValueOrigin =
	{ local_value: string }
	| { local_place: string }
	| { environment: string }

export type TargetAccessLiteral = { boolean: boolean } | { number: number }

export type TargetAccessKey = string | TargetValueOrigin | { literal: TargetAccessLiteral }

export type TargetTableKey = TargetAccessKey | { source_expression: string }

export type TargetAccessPath = {
	root: TargetValueOrigin,
	keys: { TargetAccessKey },
}

export type TargetReceiverOrigin = TargetValueOrigin | { access_path: TargetAccessPath }

export type TargetOrigin =
	{ intrinsic: string }
	| TargetValueOrigin
	| { closure_value: string }
	| { table_get: { table: TargetValueOrigin, key: TargetTableKey } }
	| { access_path: TargetAccessPath }
	| { namecall: { receiver: TargetReceiverOrigin, method: string } }

export type TargetProof = {
	content: string,
	evidence: Evidence,
}

export type TargetResolution = {
	call_location: string,
	origin: TargetOrigin,
	evidence: Evidence,
	proof: TargetProof?,
}

export type TargetResultContract = {
	producer_call_location: string,
	result_ordinal: number,
	origin: TargetOrigin,
	evidence: Evidence,
	proof: TargetProof,
}

export type TargetRecovery = {
	source_sha256: string,
	call_site_count: number,
	unresolved_call_count: number,
	lowered_unresolved_call_count: number,
	allow_direct_target_expressions: boolean,
	require_independent_proof: boolean,
	proof_bundle_evidence: Evidence?,
	unresolved_targets: { { kind: "local" | "global" | "expression", locator: string } }?,
	unresolved_target_selectors: { TargetSelector }?,
	target_resolutions: { TargetResolution }?,
	result_contracts: { TargetResultContract }?,
	detail: string,
	evidence: Evidence,
}

export type Manifest = {
	program_obligations: { any },
	intrinsic_bindings: { IntrinsicBinding },
	target_recovery: TargetRecovery?,
}

export type ProofBundleInput = TargetProofBundle.Input
export type Decoder = (string) -> any

type TargetRecoveryCapabilities = {
	frontier: "locators" | "selectors",
	resolutionOrigins: { [string]: boolean }?,
	allowDynamicAccessKeys: boolean,
	allowLiteralAccessKeys: boolean,
	allowSourceExpressionTableKeys: boolean,
	allowDirectTargetExpressions: boolean,
	requireIndependentProof: boolean,
	useDetachedProofBundle: boolean,
	allowResultContracts: boolean,
}

type ManifestContentRequirement = "program_obligations" | "recovery_facts" | "target_recovery_resolutions"

type ManifestCapabilities = {
	allowIntrinsicBindings: boolean,
	targetRecovery: TargetRecoveryCapabilities?,
	contentRequirement: ManifestContentRequirement,
}

local function allowedOriginFields(fields: { string }): { [string]: boolean }
	local allowed = {}
	for _, field in fields do
		allowed[field] = true
	end
	return table.freeze(allowed)
end

local function newTargetRecoveryCapabilities(
	frontier: "locators" | "selectors",
	resolutionOrigins: { [string]: boolean }?,
	allowDynamicAccessKeys: boolean,
	allowLiteralAccessKeys: boolean,
	allowDirectTargetExpressions: boolean,
	requireIndependentProof: boolean?,
	useDetachedProofBundle: boolean?,
	allowSourceExpressionTableKeys: boolean?,
	allowResultContracts: boolean?
): TargetRecoveryCapabilities
	return table.freeze({
		frontier = frontier,
		resolutionOrigins = resolutionOrigins,
		allowDynamicAccessKeys = allowDynamicAccessKeys,
		allowLiteralAccessKeys = allowLiteralAccessKeys,
		allowSourceExpressionTableKeys = allowSourceExpressionTableKeys == true,
		allowDirectTargetExpressions = allowDirectTargetExpressions,
		requireIndependentProof = requireIndependentProof == true,
		useDetachedProofBundle = useDetachedProofBundle == true,
		allowResultContracts = allowResultContracts == true,
	})
end

local function newManifestCapabilities(
	allowIntrinsicBindings: boolean,
	targetRecovery: TargetRecoveryCapabilities?,
	contentRequirement: ManifestContentRequirement
): ManifestCapabilities
	return table.freeze({
		allowIntrinsicBindings = allowIntrinsicBindings,
		targetRecovery = targetRecovery,
		contentRequirement = contentRequirement,
	})
end

local intrinsicResolutionOrigins = allowedOriginFields({ "intrinsic" })
local valueResolutionOrigins = allowedOriginFields({ "intrinsic", "local_value", "local_place", "environment" })
local accessResolutionOrigins = allowedOriginFields({ "intrinsic", "local_value", "local_place", "environment", "table_get" })
local namecallResolutionOrigins = allowedOriginFields({ "intrinsic", "local_value", "local_place", "environment", "table_get", "namecall" })
local compositionalResolutionOrigins = allowedOriginFields({
	"intrinsic",
	"local_value",
	"local_place",
	"environment",
	"table_get",
	"namecall",
	"access_path",
})
local closureResolutionOrigins = allowedOriginFields({
	"intrinsic",
	"local_value",
	"local_place",
	"environment",
	"table_get",
	"namecall",
	"access_path",
	"closure_value",
})

local targetRecoveryCapabilities = table.freeze({
	locatorFrontier = newTargetRecoveryCapabilities("locators", nil, false, false, false),
	selectorFrontier = newTargetRecoveryCapabilities("selectors", nil, false, false, false),
	intrinsicResolution = newTargetRecoveryCapabilities("selectors", intrinsicResolutionOrigins, false, false, false),
	valueResolution = newTargetRecoveryCapabilities("selectors", valueResolutionOrigins, false, false, false),
	accessResolution = newTargetRecoveryCapabilities("selectors", accessResolutionOrigins, false, false, false),
	dynamicAccessResolution = newTargetRecoveryCapabilities("selectors", accessResolutionOrigins, true, false, false),
	namecallResolution = newTargetRecoveryCapabilities("selectors", namecallResolutionOrigins, true, false, false),
	compositionalResolution = newTargetRecoveryCapabilities("selectors", compositionalResolutionOrigins, true, false, false),
	literalAccessResolution = newTargetRecoveryCapabilities("selectors", compositionalResolutionOrigins, true, true, false),
	directTargetResolution = newTargetRecoveryCapabilities("selectors", compositionalResolutionOrigins, true, true, true),
	proofBoundTargetResolution = newTargetRecoveryCapabilities("selectors", compositionalResolutionOrigins, true, true, true, true),
	detachedProofTargetResolution = newTargetRecoveryCapabilities("selectors", compositionalResolutionOrigins, true, true, true, true, true),
	closureResolution = newTargetRecoveryCapabilities("selectors", closureResolutionOrigins, true, true, true),
	computedTableKeyResolution = newTargetRecoveryCapabilities("selectors", closureResolutionOrigins, true, true, true, false, false, true),
	resultContractResolution = newTargetRecoveryCapabilities("selectors", closureResolutionOrigins, true, true, true, false, false, true, true),
})

local manifestCapabilities: { [string]: ManifestCapabilities } = table.freeze({
	lifter_recovery_manifest_v1 = newManifestCapabilities(false, nil, "program_obligations"),
	lifter_recovery_manifest_v2 = newManifestCapabilities(true, nil, "recovery_facts"),
	lifter_recovery_manifest_v3 = newManifestCapabilities(true, targetRecoveryCapabilities.locatorFrontier, "recovery_facts"),
	lifter_recovery_manifest_v4 = newManifestCapabilities(true, targetRecoveryCapabilities.selectorFrontier, "recovery_facts"),
	lifter_recovery_manifest_v5 = newManifestCapabilities(true, targetRecoveryCapabilities.intrinsicResolution, "target_recovery_resolutions"),
	lifter_recovery_manifest_v6 = newManifestCapabilities(true, targetRecoveryCapabilities.valueResolution, "target_recovery_resolutions"),
	lifter_recovery_manifest_v7 = newManifestCapabilities(true, targetRecoveryCapabilities.accessResolution, "target_recovery_resolutions"),
	lifter_recovery_manifest_v8 = newManifestCapabilities(true, targetRecoveryCapabilities.dynamicAccessResolution, "target_recovery_resolutions"),
	lifter_recovery_manifest_v9 = newManifestCapabilities(true, targetRecoveryCapabilities.namecallResolution, "target_recovery_resolutions"),
	lifter_recovery_manifest_v10 = newManifestCapabilities(true, targetRecoveryCapabilities.compositionalResolution, "target_recovery_resolutions"),
	lifter_recovery_manifest_v11 = newManifestCapabilities(true, targetRecoveryCapabilities.literalAccessResolution, "target_recovery_resolutions"),
	lifter_recovery_manifest_v12 = newManifestCapabilities(true, targetRecoveryCapabilities.directTargetResolution, "target_recovery_resolutions"),
	lifter_recovery_manifest_v13 = newManifestCapabilities(true, targetRecoveryCapabilities.proofBoundTargetResolution, "target_recovery_resolutions"),
	lifter_recovery_manifest_v14 = newManifestCapabilities(true, targetRecoveryCapabilities.detachedProofTargetResolution, "target_recovery_resolutions"),
	lifter_recovery_manifest_v15 = newManifestCapabilities(true, targetRecoveryCapabilities.closureResolution, "target_recovery_resolutions"),
	lifter_recovery_manifest_v16 = newManifestCapabilities(true, targetRecoveryCapabilities.computedTableKeyResolution, "target_recovery_resolutions"),
	lifter_recovery_manifest_v17 = newManifestCapabilities(true, targetRecoveryCapabilities.resultContractResolution, "target_recovery_resolutions"),
})

local allowedEvidenceKinds = table.freeze({
	source_span = true,
	decoded_record = true,
	dynamic_fixture = true,
	frontend_proof = true,
	solver_certificate = true,
	conformance_oracle = true,
	structural_derivation = true,
})

local function containsValue(values: Record, expected: string): boolean
	for _, value in values do
		if value == expected then
			return true
		end
	end
	return false
end

local function expectRecord(value: any, label: string): Record
	assert(type(value) == "table", `{label} must be an object`)
	return value :: Record
end

local function expectString(value: any, label: string): string
	assert(type(value) == "string" and value ~= "", `{label} must be a non-empty string`)
	return value
end

local function expectNatural(value: any, label: string): number
	assert(type(value) == "number" and value >= 0 and value % 1 == 0, `{label} must be a non-negative integer`)
	return value
end

local function rejectUnknownKeys(value: Record, allowed: { [string]: boolean }, label: string)
	for key in value do
		assert(allowed[key] == true, `{label} contains unknown field {key}`)
	end
end

local function normalizeEvidence(value: any, label: string): Evidence
	local evidence = expectRecord(value, label)
	rejectUnknownKeys(evidence, { kind = true, locator = true, digest = true }, label)
	local evidenceKind = expectString(evidence.kind, label .. ".kind")
	assert(allowedEvidenceKinds[evidenceKind] == true, `{label}.kind is not a contract evidence kind`)
	local normalized: Evidence = {
		kind = evidenceKind,
		locator = expectString(evidence.locator, label .. ".locator"),
		digest = nil,
	}
	if evidence.digest ~= nil then
		normalized.digest = expectString(evidence.digest, label .. ".digest")
	end
	return normalized
end

local function decodeObligations(items: any, manifestName: string): { any }
	local array = RecoveryAdmission.expectDenseArray(
		items,
		manifestName .. ".program_obligations",
		RecoveryAdmission.maxCollectionItems
	)
	local obligations = {}
	for index = 1, #array do
		local item = array[index]
		local label = `{manifestName}.program_obligations[{index}]`
		local obligation = expectRecord(item, label)
		rejectUnknownKeys(obligation, {
			kind = true,
			blocks_profile = true,
			detail = true,
			evidence = true,
		}, label)
		local kind = expectString(obligation.kind, label .. ".kind")
		local blocksProfile = expectString(obligation.blocks_profile, label .. ".blocks_profile")
		assert(containsValue(LifterIR.ObligationKind, kind), `{label}.kind is not a contract obligation kind`)
		assert(containsValue(LifterIR.AdmissionProfile, blocksProfile), `{label}.blocks_profile is not an admission profile`)

		table.insert(obligations, {
			kind = kind,
			blocks_profile = blocksProfile,
			detail = expectString(obligation.detail, label .. ".detail"),
			evidence = normalizeEvidence(obligation.evidence, label .. ".evidence"),
		})
	end
	return obligations
end

local function decodeIntrinsicBindings(items: any, manifestName: string): { IntrinsicBinding }
	local array = RecoveryAdmission.expectDenseArray(
		items,
		manifestName .. ".intrinsic_bindings",
		RecoveryAdmission.maxIntrinsicBindings
	)
	local bindings: { IntrinsicBinding } = {}
	local seen = {}
	for index = 1, #array do
		local item = array[index]
		local label = `{manifestName}.intrinsic_bindings[{index}]`
		local binding = expectRecord(item, label)
		rejectUnknownKeys(binding, { path = true, evidence = true }, label)
		local path = expectString(binding.path, label .. ".path")
		assert(IntrinsicBindings.kindForPath(path) ~= nil, `{label}.path is not a supported Luau intrinsic`)
		assert(seen[path] ~= true, `{label}.path is duplicated`)
		seen[path] = true
		table.insert(bindings, {
			path = path,
			evidence = normalizeEvidence(binding.evidence, label .. ".evidence"),
		})
	end
	return bindings
end

local function decodeTargetValueOrigin(value: any, label: string): TargetValueOrigin
	local origin = expectRecord(value, label)
	rejectUnknownKeys(origin, { local_value = true, local_place = true, environment = true }, label)
	local fieldCount = 0
	for _ in origin do
		fieldCount += 1
	end
	assert(fieldCount == 1, `{label} must contain exactly one value origin`)
	if origin.local_value ~= nil then
		return { local_value = expectString(origin.local_value, label .. ".local_value") }
	elseif origin.local_place ~= nil then
		return { local_place = expectString(origin.local_place, label .. ".local_place") }
	end
	return { environment = expectString(origin.environment, label .. ".environment") }
end

local function decodeTargetAccessLiteral(value: any, label: string): TargetAccessLiteral
	local literal = expectRecord(value, label)
	rejectUnknownKeys(literal, { boolean = true, number = true }, label)
	local fieldCount = 0
	for _ in literal do
		fieldCount += 1
	end
	assert(fieldCount == 1, `{label} must contain exactly one literal`)
	if literal.boolean ~= nil then
		assert(type(literal.boolean) == "boolean", `{label}.boolean must be a Boolean`)
		return { boolean = literal.boolean }
	end
	local numberValue = literal.number
	assert(
		type(numberValue) == "number"
			and numberValue == numberValue
			and numberValue ~= math.huge
			and numberValue ~= -math.huge,
		`{label}.number must be finite`
	)
	return { number = if numberValue == 0 then 0 else numberValue }
end

local function decodeTargetAccessKey(
	value: any,
	label: string,
	allowDynamicAccessKeys: boolean,
	allowLiteralAccessKeys: boolean
): TargetAccessKey
	if type(value) == "string" then
		return value
	end
	if type(value) == "table" and value.literal ~= nil then
		assert(allowLiteralAccessKeys, `{label} does not support literal keys`)
		local literalKey = value :: Record
		rejectUnknownKeys(literalKey, { literal = true }, label)
		return { literal = decodeTargetAccessLiteral(literalKey.literal, label .. ".literal") }
	end
	assert(allowDynamicAccessKeys, `{label} must be a string`)
	return decodeTargetValueOrigin(value, label)
end

local function decodeTargetTableKey(value: any, label: string, capabilities: TargetRecoveryCapabilities): TargetTableKey
	if type(value) == "table" and value.source_expression ~= nil then
		assert(capabilities.allowSourceExpressionTableKeys, `{label} does not support source-expression keys`)
		local expressionKey = value :: Record
		rejectUnknownKeys(expressionKey, { source_expression = true }, label)
		return { source_expression = expectString(expressionKey.source_expression, label .. ".source_expression") }
	end
	return decodeTargetAccessKey(
		value,
		label,
		capabilities.allowDynamicAccessKeys,
		capabilities.allowLiteralAccessKeys
	)
end

local function decodeTargetAccessPath(
	value: any,
	label: string,
	allowLiteralAccessKeys: boolean
): TargetAccessPath
	local path = expectRecord(value, label)
	rejectUnknownKeys(path, { root = true, keys = true }, label)
	local keys = RecoveryAdmission.expectDenseArray(path.keys, label .. ".keys", TargetRecovery.maxAccessPathKeys)
	assert(#keys > 0, `{label}.keys must not be empty`)
	local normalizedKeys: { TargetAccessKey } = {}
	for index = 1, #keys do
		table.insert(normalizedKeys, decodeTargetAccessKey(keys[index], `{label}.keys[{index}]`, true, allowLiteralAccessKeys))
	end
	return {
		root = decodeTargetValueOrigin(path.root, label .. ".root"),
		keys = normalizedKeys,
	}
end

local function decodeTargetReceiverOrigin(
	value: any,
	label: string,
	allowAccessPathOrigins: boolean,
	allowLiteralAccessKeys: boolean
): TargetReceiverOrigin
	if allowAccessPathOrigins and type(value) == "table" and value.access_path ~= nil then
		local receiver = value :: Record
		rejectUnknownKeys(receiver, { access_path = true }, label)
		return {
			access_path = decodeTargetAccessPath(receiver.access_path, label .. ".access_path", allowLiteralAccessKeys),
		}
	end
	return decodeTargetValueOrigin(value, label)
end

local function decodeTargetOrigin(
	value: any,
	label: string,
	capabilities: TargetRecoveryCapabilities
): TargetOrigin
	local allowedOriginFields = capabilities.resolutionOrigins
	assert(allowedOriginFields ~= nil)
	local origin = expectRecord(value, label)
	rejectUnknownKeys(origin, allowedOriginFields, label)
	local originFieldCount = 0
	for _ in origin do
		originFieldCount += 1
	end
	assert(originFieldCount == 1, `{label} must contain exactly one semantic origin`)
	if origin.intrinsic ~= nil then
		local intrinsicPath = expectString(origin.intrinsic, label .. ".intrinsic")
		assert(IntrinsicBindings.kindForPath(intrinsicPath) ~= nil, `{label}.intrinsic is not supported`)
		return { intrinsic = intrinsicPath }
	elseif origin.local_value ~= nil then
		return { local_value = expectString(origin.local_value, label .. ".local_value") }
	elseif origin.local_place ~= nil then
		return { local_place = expectString(origin.local_place, label .. ".local_place") }
	elseif origin.closure_value ~= nil then
		return { closure_value = expectString(origin.closure_value, label .. ".closure_value") }
	elseif origin.table_get ~= nil then
		local access = expectRecord(origin.table_get, label .. ".table_get")
		rejectUnknownKeys(access, { table = true, key = true }, label .. ".table_get")
		return {
			table_get = {
				table = decodeTargetValueOrigin(access.table, label .. ".table_get.table"),
				key = decodeTargetTableKey(access.key, label .. ".table_get.key", capabilities),
			},
		}
	elseif origin.access_path ~= nil then
		return {
			access_path = decodeTargetAccessPath(
				origin.access_path,
				label .. ".access_path",
				capabilities.allowLiteralAccessKeys
			),
		}
	elseif origin.namecall ~= nil then
		local namecall = expectRecord(origin.namecall, label .. ".namecall")
		rejectUnknownKeys(namecall, { receiver = true, method = true }, label .. ".namecall")
		return {
			namecall = {
				receiver = decodeTargetReceiverOrigin(
					namecall.receiver,
					label .. ".namecall.receiver",
					allowedOriginFields.access_path == true,
					capabilities.allowLiteralAccessKeys
				),
				method = expectString(namecall.method, label .. ".namecall.method"),
			},
		}
	end
	return { environment = expectString(origin.environment, label .. ".environment") }
end

local function decodeTargetResolutions(
	value: any,
	label: string,
	sourceSha256: string,
	capabilities: TargetRecoveryCapabilities,
	proofBundle: TargetProofBundle.Bundle?
): { TargetResolution }
	local items = RecoveryAdmission.expectDenseArray(value, label, RecoveryAdmission.maxCollectionItems)
	local resolutions: { TargetResolution } = {}
	local seenLocations = {}
	local seenProofDigests = {}
	for index = 1, #items do
		local item = items[index]
		local resolutionLabel = `{label}[{index}]`
		local resolution = expectRecord(item, resolutionLabel)
		local allowedResolutionFields = { call_location = true, origin = true, evidence = true }
		if capabilities.requireIndependentProof then
			allowedResolutionFields.proof = true
		end
		rejectUnknownKeys(resolution, allowedResolutionFields, resolutionLabel)
		local callLocation = expectString(resolution.call_location, resolutionLabel .. ".call_location")
		assert(seenLocations[callLocation] ~= true, `{resolutionLabel}.call_location is duplicated`)
		seenLocations[callLocation] = true
		local normalizedOrigin = decodeTargetOrigin(resolution.origin, resolutionLabel .. ".origin", capabilities)
		local evidence = normalizeEvidence(resolution.evidence, resolutionLabel .. ".evidence")
		assert(
			type(evidence.digest) == "string" and string.lower(evidence.digest) == sourceSha256,
			`{resolutionLabel}.evidence must authenticate the source digest`
		)
		if proofBundle ~= nil then
			assert(evidence.locator ~= proofBundle.evidence.locator, `{resolutionLabel}.evidence must differ from bundle attestation`)
		end
		local proof: TargetProof? = nil
		if capabilities.requireIndependentProof then
			local proofLabel = resolutionLabel .. ".proof"
			local envelope = expectRecord(resolution.proof, proofLabel)
			local content = ""
			local detachedEntryId: string? = nil
			if capabilities.useDetachedProofBundle then
				rejectUnknownKeys(envelope, { entry_id = true, evidence = true }, proofLabel)
				assert(proofBundle ~= nil, `{proofLabel} has no detached proof bundle`)
				detachedEntryId = string.lower(expectString(envelope.entry_id, proofLabel .. ".entry_id"))
			else
				rejectUnknownKeys(envelope, { content = true, evidence = true }, proofLabel)
				content = expectString(envelope.content, proofLabel .. ".content")
				assert(#content <= TargetRecovery.maxProofContentBytes, `{proofLabel}.content exceeds the proof-content limit`)
			end
			local proofEvidence = normalizeEvidence(envelope.evidence, proofLabel .. ".evidence")
			assert(proofEvidence.kind == "frontend_proof", `{proofLabel}.evidence.kind must be frontend_proof`)
			assert(proofEvidence.locator ~= evidence.locator, `{proofLabel}.evidence must use an independent locator`)
			if proofBundle ~= nil then
				assert(proofEvidence.locator ~= proofBundle.evidence.locator, `{proofLabel}.evidence must differ from bundle attestation`)
			end
			if detachedEntryId ~= nil then
				local bindingDigest = string.lower(expectString(proofEvidence.digest, proofLabel .. ".evidence.digest"))
				content = (proofBundle :: TargetProofBundle.Bundle):resolve(
					detachedEntryId,
					bindingDigest,
					proofLabel .. ".entry_id"
				).content
			end
			local expectedDigest = TargetRecovery.targetProofDigest(sourceSha256, callLocation, normalizedOrigin, content)
			assert(
				type(proofEvidence.digest) == "string" and string.lower(proofEvidence.digest) == expectedDigest,
				`{proofLabel}.evidence must authenticate the supplied content and semantic binding`
			)
			assert(seenProofDigests[expectedDigest] ~= true, `{proofLabel} duplicates another proof envelope`)
			seenProofDigests[expectedDigest] = true
			proof = { content = content, evidence = proofEvidence }
		end
		table.insert(resolutions, {
			call_location = callLocation,
			origin = normalizedOrigin,
			evidence = evidence,
			proof = proof,
		})
	end
	assert(#resolutions > 0, `{label} must not be empty`)
	return resolutions
end

local function decodeTargetResultContracts(
	value: any,
	label: string,
	sourceSha256: string,
	capabilities: TargetRecoveryCapabilities
): { TargetResultContract }
	local items = RecoveryAdmission.expectDenseArray(value, label, RecoveryAdmission.maxCollectionItems)
	local contracts: { TargetResultContract } = {}
	local seenResults: { [string]: boolean } = {}
	local seenProofDigests: { [string]: boolean } = {}
	for index = 1, #items do
		local contractLabel = `{label}[{index}]`
		local contract = expectRecord(items[index], contractLabel)
		rejectUnknownKeys(
			contract,
			{ producer_call_location = true, result_ordinal = true, origin = true, evidence = true, proof = true },
			contractLabel
		)
		local producerLocation = expectString(
			contract.producer_call_location,
			contractLabel .. ".producer_call_location"
		)
		local resultOrdinal = expectNatural(contract.result_ordinal, contractLabel .. ".result_ordinal")
		assert(
			resultOrdinal >= 1 and resultOrdinal <= TargetProofBundle.maxResultOrdinal,
			`{contractLabel}.result_ordinal must be between 1 and {TargetProofBundle.maxResultOrdinal}`
		)
		local resultKey = producerLocation .. "\0" .. tostring(resultOrdinal)
		assert(seenResults[resultKey] ~= true, `{contractLabel} duplicates a producer result ordinal`)
		seenResults[resultKey] = true
		local origin = decodeTargetOrigin(contract.origin, contractLabel .. ".origin", capabilities)
		local evidence = normalizeEvidence(contract.evidence, contractLabel .. ".evidence")
		assert(
			type(evidence.digest) == "string" and string.lower(evidence.digest) == sourceSha256,
			`{contractLabel}.evidence must authenticate the source digest`
		)
		local proofLabel = contractLabel .. ".proof"
		local proof = expectRecord(contract.proof, proofLabel)
		rejectUnknownKeys(proof, { content = true, evidence = true }, proofLabel)
		local content = expectString(proof.content, proofLabel .. ".content")
		assert(#content <= TargetProofBundle.maxProofContentBytes, `{proofLabel}.content exceeds the proof-content limit`)
		local proofEvidence = normalizeEvidence(proof.evidence, proofLabel .. ".evidence")
		assert(proofEvidence.kind == "frontend_proof", `{proofLabel}.evidence.kind must be frontend_proof`)
		assert(proofEvidence.locator ~= evidence.locator, `{proofLabel}.evidence must use an independent locator`)
		local expectedDigest = TargetProofBundle.resultContractProofDigest(
			sourceSha256,
			producerLocation,
			resultOrdinal,
			origin,
			content
		)
		assert(
			type(proofEvidence.digest) == "string" and string.lower(proofEvidence.digest) == expectedDigest,
			`{proofLabel}.evidence must authenticate the supplied content and semantic binding`
		)
		assert(seenProofDigests[expectedDigest] ~= true, `{proofLabel} duplicates another result proof envelope`)
		seenProofDigests[expectedDigest] = true
		table.insert(contracts, {
			producer_call_location = producerLocation,
			result_ordinal = resultOrdinal,
			origin = origin,
			evidence = evidence,
			proof = { content = content, evidence = proofEvidence },
		})
	end
	assert(#contracts > 0, `{label} must not be empty`)
	return contracts
end

local function decodeTargetRecovery(
	value: any,
	manifestName: string,
	capabilities: TargetRecoveryCapabilities,
	proofBundle: TargetProofBundle.Bundle?
): TargetRecovery
	local label = manifestName .. ".target_recovery"
	local recovery = expectRecord(value, label)
	local allowedFields = {
		source_sha256 = true,
		call_site_count = true,
		unresolved_call_count = true,
		lowered_unresolved_call_count = true,
		detail = true,
		evidence = true,
	}
	allowedFields[if capabilities.frontier == "selectors" then "unresolved_target_selectors" else "unresolved_targets"] = true
	if capabilities.resolutionOrigins ~= nil then
		allowedFields.target_resolutions = true
	end
	if capabilities.allowResultContracts then
		allowedFields.result_contracts = true
	end
	rejectUnknownKeys(recovery, allowedFields, label)
	local sourceSha256 = string.lower(expectString(recovery.source_sha256, label .. ".source_sha256"))
	assert(#sourceSha256 == 64 and string.match(sourceSha256, "^[0-9a-f]+$") ~= nil, `{label}.source_sha256 must be a SHA-256 digest`)
	local targets: { { kind: "local" | "global" | "expression", locator: string } }? = nil
	local selectors: { TargetSelector }? = nil
	local seen = {}
	if capabilities.frontier == "selectors" then
		local selectorItems = RecoveryAdmission.expectDenseArray(
			recovery.unresolved_target_selectors,
			label .. ".unresolved_target_selectors",
			RecoveryAdmission.maxCollectionItems
		)
		local decodedSelectors: { TargetSelector } = {}
		for index = 1, #selectorItems do
			local item = selectorItems[index]
			local selectorLabel = `{label}.unresolved_target_selectors[{index}]`
			local selector = expectRecord(item, selectorLabel)
			rejectUnknownKeys(selector, { kind = true, value = true }, selectorLabel)
			local kind = expectString(selector.kind, selectorLabel .. ".kind")
			assert(
				kind == "local_name"
					or kind == "local_name_prefix"
					or kind == "global_name"
					or kind == "global_name_prefix",
				`{selectorLabel}.kind is not a supported target selector`
			)
			local selectorValue = expectString(selector.value, selectorLabel .. ".value")
			local key = kind .. "\0" .. selectorValue
			assert(seen[key] ~= true, `{selectorLabel} is duplicated`)
			seen[key] = true
			table.insert(decodedSelectors, { kind = kind :: any, value = selectorValue })
		end
		assert(#decodedSelectors > 0, `{label}.unresolved_target_selectors must not be empty`)
		selectors = decodedSelectors
	else
		local targetItems = RecoveryAdmission.expectDenseArray(
			recovery.unresolved_targets,
			label .. ".unresolved_targets",
			RecoveryAdmission.maxCollectionItems
		)
		local decodedTargets: { { kind: "local" | "global" | "expression", locator: string } } = {}
		for index = 1, #targetItems do
			local item = targetItems[index]
			local targetLabel = `{label}.unresolved_targets[{index}]`
			local target = expectRecord(item, targetLabel)
			rejectUnknownKeys(target, { kind = true, locator = true }, targetLabel)
			local kind = expectString(target.kind, targetLabel .. ".kind")
			assert(kind == "local" or kind == "global" or kind == "expression", `{targetLabel}.kind is not a supported target identity`)
			local locator = expectString(target.locator, targetLabel .. ".locator")
			local key = kind .. "\0" .. locator
			assert(seen[key] ~= true, `{targetLabel} is duplicated`)
			seen[key] = true
			table.insert(decodedTargets, { kind = kind :: any, locator = locator })
		end
		assert(#decodedTargets > 0, `{label}.unresolved_targets must not be empty`)
		targets = decodedTargets
	end
	local unresolvedCallCount = expectNatural(recovery.unresolved_call_count, label .. ".unresolved_call_count")
	if targets ~= nil then
		assert(unresolvedCallCount >= #targets, `{label}.unresolved_call_count cannot be smaller than its target frontier`)
	end
	local loweredUnresolvedCallCount = expectNatural(
		recovery.lowered_unresolved_call_count,
		label .. ".lowered_unresolved_call_count"
	)
	assert(loweredUnresolvedCallCount <= unresolvedCallCount, `{label}.lowered_unresolved_call_count exceeds its source frontier`)
	local resolutions = if capabilities.resolutionOrigins ~= nil
		then decodeTargetResolutions(
			recovery.target_resolutions,
			label .. ".target_resolutions",
			sourceSha256,
			capabilities,
			proofBundle
		)
		else nil
	if resolutions ~= nil then
		assert(#resolutions <= unresolvedCallCount, `{label}.target_resolutions exceeds its unresolved call frontier`)
	end
	local resultContracts = if capabilities.allowResultContracts and recovery.result_contracts ~= nil
		then decodeTargetResultContracts(
			recovery.result_contracts,
			label .. ".result_contracts",
			sourceSha256,
			capabilities
		)
		else nil
	local recoveryEvidence = normalizeEvidence(recovery.evidence, label .. ".evidence")
	if proofBundle ~= nil then
		assert(recoveryEvidence.locator ~= proofBundle.evidence.locator, `{label}.evidence must differ from bundle attestation`)
	end
	return {
		source_sha256 = sourceSha256,
		call_site_count = expectNatural(recovery.call_site_count, label .. ".call_site_count"),
		unresolved_call_count = unresolvedCallCount,
		lowered_unresolved_call_count = loweredUnresolvedCallCount,
		allow_direct_target_expressions = capabilities.allowDirectTargetExpressions,
		require_independent_proof = capabilities.requireIndependentProof,
		proof_bundle_evidence = if proofBundle ~= nil then proofBundle.evidence else nil,
		unresolved_targets = targets,
		unresolved_target_selectors = selectors,
		target_resolutions = resolutions,
		result_contracts = resultContracts,
		detail = expectString(recovery.detail, label .. ".detail"),
		evidence = recoveryEvidence,
	}
end

function RecoveryManifest.fromDecoded(value: any, manifestName: string, proofBundleInput: ProofBundleInput?): Manifest
	local decoded = expectRecord(value, manifestName)
	local version = expectString(decoded.schema_version, manifestName .. ".schema_version")
	local capabilities = manifestCapabilities[version]
	if capabilities == nil then
		error(`{manifestName} has an unsupported schema version`, 0)
	end

	local allowedFields = { schema_version = true, program_obligations = true }
	if capabilities.allowIntrinsicBindings then
		allowedFields.intrinsic_bindings = true
	end
	if capabilities.targetRecovery ~= nil then
		allowedFields.target_recovery = true
		if capabilities.targetRecovery.useDetachedProofBundle then
			allowedFields.proof_bundle = true
		end
	end
	rejectUnknownKeys(decoded, allowedFields, manifestName)

	local proofBundle: TargetProofBundle.Bundle? = nil
	local targetCapabilities = capabilities.targetRecovery
	if targetCapabilities ~= nil and targetCapabilities.useDetachedProofBundle then
		assert(proofBundleInput ~= nil, `{manifestName} requires detached proof bundle bytes and a trusted verifier`)
		local attestationLabel = manifestName .. ".proof_bundle"
		local attestation = expectRecord(decoded.proof_bundle, attestationLabel)
		rejectUnknownKeys(attestation, { signature = true, evidence = true }, attestationLabel)
		proofBundle = TargetProofBundle.open(
			proofBundleInput :: ProofBundleInput,
			expectString(attestation.signature, attestationLabel .. ".signature"),
			normalizeEvidence(attestation.evidence, attestationLabel .. ".evidence"),
			attestationLabel
		)
	else
		assert(proofBundleInput == nil, `{manifestName} does not accept detached proof bundle input`)
	end

	local obligations = decodeObligations(
		if capabilities.contentRequirement == "program_obligations" then decoded.program_obligations else decoded.program_obligations or {},
		manifestName
	)
	local bindings: { IntrinsicBinding } = {}
	if capabilities.allowIntrinsicBindings then
		bindings = decodeIntrinsicBindings(decoded.intrinsic_bindings or {}, manifestName)
	end
	local targetRecovery: TargetRecovery? = nil
	if targetCapabilities ~= nil and decoded.target_recovery ~= nil then
		targetRecovery = decodeTargetRecovery(decoded.target_recovery, manifestName, targetCapabilities, proofBundle)
	end
	if proofBundle ~= nil then
		proofBundle:assertFullyUsed(manifestName .. ".proof_bundle")
	end

	if capabilities.contentRequirement == "program_obligations" then
		assert(#obligations > 0, `{manifestName}.program_obligations must not be empty`)
	elseif capabilities.contentRequirement == "target_recovery_resolutions" then
		assert(targetRecovery ~= nil, `{manifestName} must contain target recovery resolutions`)
	else
		assert(#obligations > 0 or #bindings > 0 or targetRecovery ~= nil, `{manifestName} must contain recovery facts`)
	end

	return {
		program_obligations = obligations,
		intrinsic_bindings = bindings,
		target_recovery = targetRecovery,
	}
end

function RecoveryManifest.fromBytes(
	bytes: string,
	manifestName: string,
	decode: Decoder,
	proofBundleInput: ProofBundleInput?
): Manifest
	local admittedBytes = RecoveryAdmission.expectManifestBytes(bytes, manifestName)
	return RecoveryManifest.fromDecoded(decode(admittedBytes), manifestName, proofBundleInput)
end

return table.freeze(RecoveryManifest)
