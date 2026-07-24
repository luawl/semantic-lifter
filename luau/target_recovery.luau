--!strict

-- Verifies a recovery-side target frontier against the exact source and
-- pinned luau-ast shape. The frontier remains frontend-private; only typed
-- obligations and their evidence cross into admitted IR.

local TemporalTargetIdentity = require("./temporal_target_identity")
local AstAdmission = require("./ast_admission")
local RecoveryAdmission = require("./recovery_admission")
local TargetProofBundle = require("./target_proof_bundle")
local TargetResultContracts = require("./target_result_contracts")
local AstExpressionSlots = require("./ast_expression_slots")

local TargetRecovery = {}
TargetRecovery.maxAccessPathKeys = TargetProofBundle.maxAccessPathKeys
TargetRecovery.maxProofContentBytes = TargetProofBundle.maxProofContentBytes
TargetRecovery.maxResultOrdinal = TargetResultContracts.maxResultOrdinal

type Record = { [string]: any }

export type Evidence = {
	kind: string,
	locator: string,
	digest: string?,
}

export type Target = {
	kind: "local" | "global" | "expression",
	locator: string,
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

export type TargetResultContract = TargetResultContracts.Contract

export type Spec = {
	source_sha256: string,
	call_site_count: number,
	unresolved_call_count: number,
	lowered_unresolved_call_count: number,
	allow_direct_target_expressions: boolean?,
	require_independent_proof: boolean?,
	proof_bundle_evidence: Evidence?,
	unresolved_targets: { Target }?,
	unresolved_target_selectors: { TargetSelector }?,
	target_resolutions: { TargetResolution }?,
	result_contracts: { TargetResultContract }?,
	detail: string,
	evidence: Evidence,
}

export type VerifiedValueOrigin =
	{ kind: "local_value", declaration: Record }
	| { kind: "local_place", declaration: Record }
	| { kind: "environment", name: string }

export type VerifiedAccessKey =
	{ kind: "constant_string", value: string }
	| { kind: "constant_boolean", value: boolean }
	| { kind: "constant_number", value: number }
	| VerifiedValueOrigin

export type VerifiedTableKey = VerifiedAccessKey | { kind: "source_expression", expression: Record }

export type VerifiedAccessPath = {
	kind: "access_path",
	root_origin: VerifiedValueOrigin,
	key_origins: { VerifiedAccessKey },
}

export type VerifiedReceiverOrigin = VerifiedValueOrigin | VerifiedAccessPath

export type VerifiedOrigin =
	{ kind: "intrinsic", path: string }
	| VerifiedValueOrigin
	| { kind: "closure_value", expression: Record }
	| { kind: "table_get", table_origin: VerifiedValueOrigin, key_origin: VerifiedTableKey }
	| VerifiedAccessPath
	| { kind: "namecall", receiver_origin: VerifiedReceiverOrigin, method: string }

export type VerifiedResolution = {
	origin: VerifiedOrigin,
	evidence: Evidence,
	proof_evidence: Evidence?,
	result_contract_evidence: { Evidence }?,
	temporal_identity: TemporalTargetIdentity.Proof?,
	preserve_source_target: boolean,
}

export type VerifiedSite = {
	detail: string,
	evidence: Evidence,
	resolution: VerifiedResolution?,
}

export type Verified = {
	by_call_location: { [string]: VerifiedSite },
	proof_bundle_evidence: Evidence?,
	call_site_count: number,
	unresolved_call_count: number,
	lowered_unresolved_call_count: number,
	resolved_call_count: number,
}

function TargetRecovery.sha256(input: string): string
	return TargetProofBundle.sha256(input)
end

function TargetRecovery.targetProofDigest(
	sourceSha256: string,
	callLocation: string,
	origin: TargetOrigin,
	content: string
): string
	return TargetProofBundle.targetProofDigest(sourceSha256, callLocation, origin, content)
end

function TargetRecovery.targetResultProofDigest(
	sourceSha256: string,
	producerCallLocation: string,
	resultOrdinal: number,
	origin: TargetOrigin,
	content: string
): string
	return TargetProofBundle.resultContractProofDigest(
		sourceSha256,
		producerCallLocation,
		resultOrdinal,
		origin,
		content
	)
end

local function expectRecord(value: any, label: string): Record
	assert(type(value) == "table", `{label} must be an object`)
	return value :: Record
end

local function expectString(value: any, label: string): string
	assert(type(value) == "string" and value ~= "", `{label} must be a non-empty string`)
	return value
end

local function targetKey(kind: string, locator: string): string
	return kind .. "\0" .. locator
end

local function describeCallTarget(call: Record): (string, string)
	local functionNode = expectRecord(call.func, "call target")
	local tag = expectString(functionNode.type, "call target.type")
	if tag == "AstExprLocal" then
		local localNode = expectRecord(functionNode["local"], "local call target declaration")
		return "local", expectString(localNode.location, "local call target declaration.location")
	elseif tag == "AstExprGlobal" then
		return "global", expectString(functionNode.global, "global call target name")
	end
	return "expression", expectString(functionNode.location, "call target.location")
end

local function transparentCallTargetReference(value: any): (string?, string?, Record?)
	if type(value) ~= "table" then
		return nil, nil, nil
	end
	local node = value :: Record
	local tag = expectString(node.type, "call target.type")
	while tag == "AstExprGroup" or tag == "AstExprTypeAssertion" or tag == "AstExprInstantiate" do
		node = expectRecord(node.expr, "transparent call target expression")
		tag = expectString(node.type, "call target.type")
	end
	if tag == "AstExprLocal" then
		local localNode = expectRecord(node["local"], "local call target declaration")
		return "local", expectString(localNode.location, "local call target declaration.location"), localNode
	elseif tag == "AstExprGlobal" then
		return "global", expectString(node.global, "global call target name"), nil
	end
	return nil, nil, nil
end

type SourceIdentities = {
	localDeclarations: { [string]: Record },
	closureExpressions: { [string]: Record },
	sourceExpressions: { [string]: Record | boolean },
}

local function indexSourceIdentities(document: Record): SourceIdentities
	local localDeclarations: { [string]: Record } = {}
	local closureExpressions: { [string]: Record } = {}
	local sourceExpressions: { [string]: Record | boolean } = {}
	local function visit(value: any)
		if type(value) ~= "table" then
			return
		end
		local record = value :: Record
		if record.type == "AstLocal" then
			local location = expectString(record.location, "local declaration.location")
			local name = expectString(record.name, "local declaration.name")
			local prior = localDeclarations[location]
			if prior ~= nil then
				assert(prior.name == name, `local declaration location {location} is ambiguous`)
			else
				localDeclarations[location] = record
			end
		elseif record.type == "AstExprFunction" then
			local location = expectString(record.location, "closure expression.location")
			local prior = closureExpressions[location]
			assert(prior == nil or prior == record, `closure expression location {location} is ambiguous`)
			closureExpressions[location] = record
		end
		local tag = record.type
		local location = record.location
		if type(tag) == "string" and string.sub(tag, 1, 7) == "AstExpr" and type(location) == "string" then
			local prior = sourceExpressions[location]
			if prior == nil then
				sourceExpressions[location] = record
			elseif prior ~= record then
				sourceExpressions[location] = false
			end
		end
		for _, child in record do
			visit(child)
		end
	end
	visit(document)
	return {
		localDeclarations = localDeclarations,
		closureExpressions = closureExpressions,
		sourceExpressions = sourceExpressions,
	}
end

local function verifyValueOrigin(
	originValue: any,
	localDeclarations: { [string]: Record },
	label: string
): VerifiedValueOrigin
	local origin = expectRecord(originValue, label)
	local selectedKind: string? = nil
	local selectedValue: string? = nil
	for key, value in origin do
		assert(
			key == "local_value" or key == "local_place" or key == "environment",
			`{label} has unknown value-origin field {key}`
		)
		assert(selectedKind == nil, `{label} has an ambiguous value origin`)
		selectedKind = key
		selectedValue = expectString(value, `{label}.{key}`)
	end
	assert(selectedKind ~= nil and selectedValue ~= nil, `{label} has an invalid value origin`)
	if selectedKind == "environment" then
		return { kind = "environment", name = selectedValue :: string }
	end
	local declaration = localDeclarations[selectedValue :: string]
	assert(declaration ~= nil, `{label} names an absent local declaration`)
	if selectedKind == "local_value" then
		return { kind = "local_value", declaration = declaration :: Record }
	end
	return { kind = "local_place", declaration = declaration :: Record }
end

local function verifyAccessKey(value: any, localDeclarations: { [string]: Record }, label: string): VerifiedAccessKey
	if type(value) == "string" then
		return { kind = "constant_string", value = value }
	end
	if type(value) == "table" and value.literal ~= nil then
		local literalKey = value :: Record
		for key in literalKey do
			assert(key == "literal", `{label} has unknown literal-key field {key}`)
		end
		local literal = expectRecord(literalKey.literal, label .. ".literal")
		local selectedKind: string? = nil
		local selectedValue: any = nil
		for key, literalValue in literal do
			assert(key == "boolean" or key == "number", `{label}.literal has unknown field {key}`)
			assert(selectedKind == nil, `{label}.literal is ambiguous`)
			selectedKind = key
			selectedValue = literalValue
		end
		assert(selectedKind ~= nil, `{label}.literal is empty`)
		if selectedKind == "boolean" then
			assert(type(selectedValue) == "boolean", `{label}.literal.boolean must be a Boolean`)
			return { kind = "constant_boolean", value = selectedValue }
		end
		assert(
			type(selectedValue) == "number"
				and selectedValue == selectedValue
				and selectedValue ~= math.huge
				and selectedValue ~= -math.huge,
			`{label}.literal.number must be finite`
		)
		return { kind = "constant_number", value = if selectedValue == 0 then 0 else selectedValue }
	end
	return verifyValueOrigin(value, localDeclarations, label)
end

local function verifyTableKey(value: any, identities: SourceIdentities, label: string): VerifiedTableKey
	if type(value) == "table" and value.source_expression ~= nil then
		local expressionKey = value :: Record
		for key in expressionKey do
			assert(key == "source_expression", `{label} has unknown source-expression field {key}`)
		end
		local location = expectString(expressionKey.source_expression, label .. ".source_expression")
		local expression = identities.sourceExpressions[location]
		assert(type(expression) == "table", `{label}.source_expression names an absent or ambiguous expression`)
		return { kind = "source_expression", expression = expression :: Record }
	end
	return verifyAccessKey(value, identities.localDeclarations, label)
end

local function verifyAccessPath(value: any, localDeclarations: { [string]: Record }, label: string): VerifiedAccessPath
	local path = expectRecord(value, label)
	for key in path do
		assert(key == "root" or key == "keys", `{label} has unknown field {key}`)
	end
	local keys = RecoveryAdmission.expectDenseArray(path.keys, label .. ".keys", TargetRecovery.maxAccessPathKeys)
	assert(#keys > 0, `{label}.keys must not be empty`)
	local keyOrigins: { VerifiedAccessKey } = {}
	for index = 1, #keys do
		table.insert(keyOrigins, verifyAccessKey(keys[index], localDeclarations, `{label}.keys[{index}]`))
	end
	return {
		kind = "access_path",
		root_origin = verifyValueOrigin(path.root, localDeclarations, label .. ".root"),
		key_origins = keyOrigins,
	}
end

local function verifyReceiverOrigin(
	value: any,
	localDeclarations: { [string]: Record },
	label: string
): VerifiedReceiverOrigin
	if type(value) == "table" and value.access_path ~= nil then
		local receiver = value :: Record
		for key in receiver do
			assert(key == "access_path", `{label} has unknown receiver-origin field {key}`)
		end
		return verifyAccessPath(receiver.access_path, localDeclarations, label .. ".access_path")
	end
	return verifyValueOrigin(value, localDeclarations, label)
end

local function verifyOrigin(originValue: any, identities: SourceIdentities, subject: string): VerifiedOrigin
	local label = subject .. ".origin"
	local localDeclarations = identities.localDeclarations
	local origin = expectRecord(originValue, label)
	local selectedKind: string? = nil
	for key in origin do
		assert(
			key == "intrinsic"
				or key == "local_value"
				or key == "local_place"
				or key == "environment"
				or key == "closure_value"
				or key == "table_get"
				or key == "access_path"
				or key == "namecall",
			`{subject} has unknown origin field {key}`
		)
		assert(selectedKind == nil, `{subject} has an ambiguous semantic origin`)
		selectedKind = key
	end
	assert(selectedKind ~= nil, `{subject} has an invalid semantic origin`)
	if selectedKind == "intrinsic" then
		return { kind = "intrinsic", path = expectString(origin.intrinsic, label .. ".intrinsic") }
	elseif selectedKind == "closure_value" then
		local location = expectString(origin.closure_value, label .. ".closure_value")
		local expression = identities.closureExpressions[location]
		assert(expression ~= nil, `{label}.closure_value names an absent function expression`)
		return { kind = "closure_value", expression = expression :: Record }
	elseif selectedKind == "table_get" then
		local access = expectRecord(origin.table_get, label .. ".table_get")
		for key in access do
			assert(key == "table" or key == "key", `{label}.table_get has unknown field {key}`)
		end
		assert(access.table ~= nil and access.key ~= nil, `{label}.table_get must contain table and key`)
		return {
			kind = "table_get",
			table_origin = verifyValueOrigin(access.table, localDeclarations, label .. ".table_get.table"),
			key_origin = verifyTableKey(access.key, identities, label .. ".table_get.key"),
		}
	elseif selectedKind == "access_path" then
		return verifyAccessPath(origin.access_path, localDeclarations, label .. ".access_path")
	elseif selectedKind == "namecall" then
		local namecall = expectRecord(origin.namecall, label .. ".namecall")
		for key in namecall do
			assert(key == "receiver" or key == "method", `{label}.namecall has unknown field {key}`)
		end
		assert(namecall.receiver ~= nil and namecall.method ~= nil, `{label}.namecall must contain receiver and method`)
		return {
			kind = "namecall",
			receiver_origin = verifyReceiverOrigin(namecall.receiver, localDeclarations, label .. ".namecall.receiver"),
			method = expectString(namecall.method, label .. ".namecall.method"),
		}
	end
	return verifyValueOrigin(origin, localDeclarations, label)
end

local function selectorMatches(selector: TargetSelector, referenceKind: string, name: string): boolean
	if selector.kind == referenceKind .. "_name" then
		return name == selector.value
	elseif selector.kind == referenceKind .. "_name_prefix" then
		return string.sub(name, 1, #selector.value) == selector.value
	end
	return false
end

local function targetContainsSelectedReference(
	value: any,
	selectors: { TargetSelector },
	matchedSelectors: { [number]: boolean }
): boolean
	if type(value) ~= "table" then
		return false
	end
	local selected = false
	local stack: { { value: Record, role: AstExpressionSlots.Role? } } = { {
		value = value :: Record,
		role = nil,
	} }
	while #stack > 0 do
		local frame = table.remove(stack) :: { value: Record, role: AstExpressionSlots.Role? }
		local record = frame.value
		if record.type == "AstExprFunction" then
			continue
		end
		local referenceKind: string? = nil
		local name: string? = nil
		if record.type == "AstExprLocal" then
			local localNode = expectRecord(record["local"], "local call target declaration")
			referenceKind = "local"
			name = expectString(localNode.name, "local call target declaration.name")
		elseif record.type == "AstExprGlobal" then
			referenceKind = "global"
			name = expectString(record.global, "global call target name")
		end
		if referenceKind ~= nil and name ~= nil then
			for index, selector in selectors do
				if selectorMatches(selector, referenceKind, name) then
					matchedSelectors[index] = true
					selected = true
				end
			end
		end
		for key, child in record do
			if type(child) == "table" then
				local role = AstExpressionSlots.childRole(frame.role, record, key, child)
				if role ~= nil then
					table.insert(stack, { value = child :: Record, role = role })
				end
			end
		end
	end
	return selected
end

local function verifyResultContracts(
	document: Record,
	spec: Spec,
	identities: SourceIdentities,
	proofBundleEvidence: Evidence?
): TargetResultContracts.Matcher?
	if spec.result_contracts == nil then
		return nil
	end
	local items = RecoveryAdmission.expectDenseArray(
		spec.result_contracts,
		"target result contract list",
		RecoveryAdmission.maxCollectionItems
	) :: { TargetResultContract }
	assert(#items > 0, "target result contract list must not be empty")
	local seenProofDigests: { [string]: boolean } = {}
	for index, contract in items do
		local subject = `target result contract {index}`
		assert(
			type(contract.producer_call_location) == "string" and contract.producer_call_location ~= "",
			`{subject} has an empty producer call location`
		)
		assert(
			type(contract.result_ordinal) == "number"
				and contract.result_ordinal >= 1
				and contract.result_ordinal <= TargetRecovery.maxResultOrdinal
				and contract.result_ordinal % 1 == 0,
			`{subject} has an invalid result ordinal`
		)
		verifyOrigin(contract.origin, identities, subject)
		local evidence = contract.evidence
		assert(
			type(evidence) == "table"
				and type(evidence.kind) == "string"
				and evidence.kind ~= ""
				and type(evidence.locator) == "string"
				and evidence.locator ~= ""
				and type(evidence.digest) == "string"
				and string.lower(evidence.digest) == string.lower(spec.source_sha256),
			`{subject} does not authenticate the source digest`
		)
		local proof = contract.proof
		assert(type(proof) == "table", `{subject} has no independent proof content`)
		assert(
			type(proof.content) == "string"
				and proof.content ~= ""
				and #proof.content <= TargetRecovery.maxProofContentBytes,
			`{subject} has invalid proof content`
		)
		local proofEvidence = proof.evidence
		assert(
			type(proofEvidence) == "table"
				and proofEvidence.kind == "frontend_proof"
				and type(proofEvidence.locator) == "string"
				and proofEvidence.locator ~= ""
				and proofEvidence.locator ~= evidence.locator
				and (proofBundleEvidence == nil or proofEvidence.locator ~= proofBundleEvidence.locator),
			`{subject} proof evidence is not independent`
		)
		local expectedDigest = TargetRecovery.targetResultProofDigest(
			spec.source_sha256,
			contract.producer_call_location,
			contract.result_ordinal,
			contract.origin,
			proof.content
		)
		assert(
			type(proofEvidence.digest) == "string" and string.lower(proofEvidence.digest) == expectedDigest,
			`{subject} proof digest does not authenticate its semantic binding`
		)
		assert(seenProofDigests[expectedDigest] ~= true, `{subject} duplicates a result proof envelope`)
		seenProofDigests[expectedDigest] = true
	end
	return TargetResultContracts.new(document, items)
end

function TargetRecovery.verify(document: Record, source: string, spec: Spec): Verified
	assert(string.lower(spec.source_sha256) == TargetRecovery.sha256(source), "target recovery source digest does not match")
	assert(spec.call_site_count >= 0 and spec.call_site_count % 1 == 0, "target recovery call count is invalid")
	assert(spec.unresolved_call_count >= 0 and spec.unresolved_call_count % 1 == 0, "target recovery unresolved call count is invalid")
	assert(
		spec.lowered_unresolved_call_count >= 0
			and spec.lowered_unresolved_call_count % 1 == 0
			and spec.lowered_unresolved_call_count <= spec.unresolved_call_count,
		"target recovery lowered unresolved call count is invalid"
	)
	assert(
		spec.allow_direct_target_expressions == nil or type(spec.allow_direct_target_expressions) == "boolean",
		"target recovery direct-target capability is invalid"
	)
	assert(
		spec.require_independent_proof == nil or type(spec.require_independent_proof) == "boolean",
		"target recovery proof capability is invalid"
	)
	local proofBundleEvidence = spec.proof_bundle_evidence
	if proofBundleEvidence ~= nil then
		assert(spec.require_independent_proof == true, "target recovery bundle evidence requires independent proofs")
		assert(
			proofBundleEvidence.kind == "frontend_proof"
				and proofBundleEvidence.locator ~= ""
				and type(proofBundleEvidence.digest) == "string"
				and proofBundleEvidence.digest ~= "",
			"target recovery bundle evidence is malformed"
		)
		assert(proofBundleEvidence.locator ~= spec.evidence.locator, "target recovery bundle evidence is not independent")
	end

	local explicitTargets = spec.unresolved_targets
	local selectors = spec.unresolved_target_selectors
	assert((explicitTargets ~= nil) ~= (selectors ~= nil), "target recovery must use exactly one frontier mode")
	if explicitTargets ~= nil then
		explicitTargets = RecoveryAdmission.expectDenseArray(
			explicitTargets,
			"target recovery target frontier",
			RecoveryAdmission.maxCollectionItems
		) :: { Target }
	else
		selectors = RecoveryAdmission.expectDenseArray(
			selectors,
			"target recovery selector frontier",
			RecoveryAdmission.maxCollectionItems
		) :: { TargetSelector }
	end
	if selectors ~= nil then
		assert(
			type(spec.evidence.digest) == "string"
				and string.lower(spec.evidence.digest) == string.lower(spec.source_sha256),
			"target recovery selector evidence must authenticate the source digest"
		)
	end
	local resolutions = spec.target_resolutions
	local resolutionItems: { any }? = nil
	if resolutions ~= nil then
		resolutionItems = RecoveryAdmission.expectDenseArray(
			resolutions,
			"target recovery resolution list",
			RecoveryAdmission.maxCollectionItems
		)
	end
	local sourceIdentities = indexSourceIdentities(document)
	local resultContractMatcher = verifyResultContracts(document, spec, sourceIdentities, proofBundleEvidence)
	local temporalAnalysis: TemporalTargetIdentity.Analysis? = nil
	local resolutionByLocation: { [string]: VerifiedResolution } = {}
	local resultSessionByLocation: { [string]: TargetResultContracts.Session } = {}
	local seenProofDigests: { [string]: boolean } = {}
	if resolutionItems ~= nil then
		temporalAnalysis = TemporalTargetIdentity.analyze(document)
		assert(#resolutionItems > 0, "target recovery resolution list must not be empty")
		assert(#resolutionItems <= spec.unresolved_call_count, "target recovery has more resolutions than unresolved calls")
		for index = 1, #resolutionItems do
			local resolution = resolutionItems[index]
			assert(resolution.call_location ~= "", `target recovery resolution {index} has an empty call location`)
			assert(
				type(resolution.evidence) == "table"
					and type(resolution.evidence.digest) == "string"
					and string.lower(resolution.evidence.digest) == string.lower(spec.source_sha256),
				`target recovery resolution {index} does not authenticate the source digest`
			)
			assert(
				proofBundleEvidence == nil or resolution.evidence.locator ~= proofBundleEvidence.locator,
				`target recovery resolution {index} source evidence is not independent of its proof bundle`
			)
			assert(
				resolutionByLocation[resolution.call_location] == nil,
				`target recovery resolution {index} duplicates a call location`
			)
			local verifiedOrigin = verifyOrigin(
				resolution.origin,
				sourceIdentities,
				`target recovery resolution {index}`
			)
			local proofEvidence: Evidence? = nil
			if spec.require_independent_proof == true then
				local proof = resolution.proof
				assert(type(proof) == "table", `target recovery resolution {index} has no independent proof content`)
				assert(
					type(proof.content) == "string"
						and proof.content ~= ""
						and #proof.content <= TargetRecovery.maxProofContentBytes,
					`target recovery resolution {index} has invalid proof content`
				)
				assert(type(proof.evidence) == "table", `target recovery resolution {index} has no proof evidence`)
				local evidence = proof.evidence
				assert(
					evidence.kind == "frontend_proof"
						and type(evidence.locator) == "string"
						and evidence.locator ~= ""
						and evidence.locator ~= resolution.evidence.locator
						and (proofBundleEvidence == nil or evidence.locator ~= proofBundleEvidence.locator),
					`target recovery resolution {index} proof evidence is not independent`
				)
				local expectedDigest = TargetRecovery.targetProofDigest(
					spec.source_sha256,
					resolution.call_location,
					resolution.origin,
					proof.content
				)
				assert(
					type(evidence.digest) == "string" and string.lower(evidence.digest) == expectedDigest,
					`target recovery resolution {index} proof digest does not authenticate its content and semantic binding`
				)
				assert(seenProofDigests[expectedDigest] ~= true, `target recovery resolution {index} duplicates a proof envelope`)
				seenProofDigests[expectedDigest] = true
				proofEvidence = evidence
			else
				assert(resolution.proof == nil, `target recovery resolution {index} uses an unsupported proof envelope`)
			end
			resolutionByLocation[resolution.call_location] = {
				origin = verifiedOrigin,
				evidence = resolution.evidence,
				proof_evidence = proofEvidence,
				result_contract_evidence = nil,
				temporal_identity = nil,
				preserve_source_target = false,
			}
			if resultContractMatcher ~= nil then
				resultSessionByLocation[resolution.call_location] = (resultContractMatcher :: TargetResultContracts.Matcher):begin(
					resolution.origin
				)
			end
		end
	end
	local targets: { [string]: Target } = {}
	local matchedTargets: { [string]: boolean } = {}
	if explicitTargets ~= nil then
		local targetItems = explicitTargets
		assert(#targetItems > 0, "target recovery target frontier must not be empty")
		for index = 1, #targetItems do
			local target = targetItems[index]
			assert(target.kind == "local" or target.kind == "global" or target.kind == "expression", `target recovery target {index} has an invalid kind`)
			assert(target.locator ~= "", `target recovery target {index} has an empty locator`)
			local key = targetKey(target.kind, target.locator)
			assert(targets[key] == nil, `target recovery target {index} is duplicated`)
			targets[key] = target
		end
	else
		local selectorItems = selectors :: { TargetSelector }
		assert(#selectorItems > 0, "target recovery selector frontier must not be empty")
		local seenSelectors: { [string]: boolean } = {}
		for index = 1, #selectorItems do
			local selector = selectorItems[index] :: TargetSelector
			assert(
				selector.kind == "local_name"
					or selector.kind == "local_name_prefix"
					or selector.kind == "global_name"
					or selector.kind == "global_name_prefix",
				`target recovery selector {index} has an invalid kind`
			)
			assert(selector.value ~= "", `target recovery selector {index} has an empty value`)
			local key = selector.kind .. "\0" .. selector.value
			assert(seenSelectors[key] == nil, `target recovery selector {index} is duplicated`)
			seenSelectors[key] = true
		end
	end

	local callCount = 0
	local unresolvedCallCount = 0
	local byCallLocation: { [string]: VerifiedSite } = {}
	local seenCalls: { [string]: boolean } = {}
	local matchedResolutions: { [string]: boolean } = {}
	local matchedSelectors: { [number]: boolean } = {}
	AstAdmission.visitRuntime(expectRecord(document.root, "target recovery document root"), function(record: Record)
		if record.type == "AstExprCall" then
			callCount += 1
			local location = expectString(record.location, "call.location")
			assert(seenCalls[location] == nil, `target recovery found duplicate call location {location}`)
			seenCalls[location] = true
			local unresolved = false
			if explicitTargets ~= nil then
				local kind, locator = describeCallTarget(record)
				local key = targetKey(kind, locator)
				if targets[key] ~= nil then
					matchedTargets[key] = true
					unresolved = true
				end
			else
				unresolved = targetContainsSelectedReference(
					expectRecord(record.func, "call target"),
					selectors :: { TargetSelector },
					matchedSelectors
				)
			end
			if unresolved then
				unresolvedCallCount += 1
				local resolution = resolutionByLocation[location]
				if resolution ~= nil then
					local resultSession = resultSessionByLocation[location]
					local matchesResult: TemporalTargetIdentity.ResultMatcher? = nil
					if resultSession ~= nil then
						matchesResult = function(value: Record, resultOrdinal: number, origin: Record): boolean
							return (resultSession :: TargetResultContracts.Session):matches(value, resultOrdinal, origin)
						end
					end
					local resultEvidenceCommitted = false
					local function commitResultEvidence(): number
						assert(not resultEvidenceCommitted, `target recovery result evidence was committed twice at {location}`)
						resultEvidenceCommitted = true
						if resultSession == nil then
							return 0
						end
						local evidence = (resultSession :: TargetResultContracts.Session):commit()
						for _, item in evidence do
							assert(
								item.locator ~= resolution.evidence.locator,
								`target recovery result evidence is not independent at {location}`
							)
						end
						resolution.result_contract_evidence = if #evidence > 0 then evidence else nil
						return #evidence
					end
					local referenceKind: string?
					local referenceLocator: string?
					local referenceDeclaration: Record?
					local sourceTarget: Record
					local authenticatedOrigin: Record
					if resolution.origin.kind == "namecall" then
						assert(record.self == true, `target recovery namecall origin requires a method call at {location}`)
						local functionNode = expectRecord(record.func, "method call target")
						assert(functionNode.type == "AstExprIndexName", `target recovery method call has no static name at {location}`)
						assert(
							type(functionNode.index) == "string" and functionNode.index == resolution.origin.method,
							`target recovery method name does not match the source at {location}`
						)
						sourceTarget = expectRecord(functionNode.expr, "method call receiver")
						referenceKind, referenceLocator, referenceDeclaration = transparentCallTargetReference(sourceTarget)
						authenticatedOrigin = resolution.origin.receiver_origin
					else
						assert(record.self ~= true, `target recovery cannot replace method call {location}`)
						sourceTarget = expectRecord(record.func, "call target")
						referenceKind, referenceLocator, referenceDeclaration = transparentCallTargetReference(sourceTarget)
						authenticatedOrigin = resolution.origin
					end
					if referenceKind == nil then
						assert(
							spec.allow_direct_target_expressions == true,
							`target recovery cannot authenticate a direct target expression at {location}`
						)
						assert(
							TemporalTargetIdentity.matchesExpression(
								temporalAnalysis :: TemporalTargetIdentity.Analysis,
								sourceTarget,
								authenticatedOrigin,
								matchesResult
							),
							`target recovery origin does not match the direct source expression at {location}`
						)
						local resultEvidenceCount = commitResultEvidence()
						assert(
							authenticatedOrigin.kind == "table_get"
								or authenticatedOrigin.kind == "access_path"
								or authenticatedOrigin.kind == "closure_value"
								or resultEvidenceCount > 0,
							`target recovery direct target has no authenticated source identity at {location}`
						)
						resolution.preserve_source_target = true
					elseif referenceKind == "local" then
						assert(referenceDeclaration ~= nil and referenceLocator ~= nil)
						resolution.temporal_identity = TemporalTargetIdentity.verify(
							temporalAnalysis :: TemporalTargetIdentity.Analysis,
							record,
							referenceDeclaration :: Record,
							authenticatedOrigin,
							matchesResult
						)
					else
						assert(referenceKind == "global" and referenceLocator ~= nil)
						assert(
							not (authenticatedOrigin.kind == "environment" and authenticatedOrigin.name == referenceLocator),
							`target recovery environment origin does not change target identity at {location}`
						)
						assert(
							TemporalTargetIdentity.matchesExpression(
								temporalAnalysis :: TemporalTargetIdentity.Analysis,
								sourceTarget,
								authenticatedOrigin,
								matchesResult
							),
							`target recovery origin does not match the direct source target at {location}`
						)
					end
					if not resultEvidenceCommitted then
						commitResultEvidence()
					end
					matchedResolutions[location] = true
				end
				byCallLocation[location] = {
					detail = spec.detail,
					evidence = spec.evidence,
					resolution = resolution,
				}
			end
		end
	end)

	assert(callCount == spec.call_site_count, `target recovery expected {spec.call_site_count} calls but found {callCount}`)
	assert(
		unresolvedCallCount == spec.unresolved_call_count,
		`target recovery expected {spec.unresolved_call_count} unresolved calls but found {unresolvedCallCount}`
	)
	if explicitTargets ~= nil then
		for key in targets do
			assert(matchedTargets[key] == true, "target recovery contains a target that is not called")
		end
	else
		for index in selectors :: { TargetSelector } do
			assert(matchedSelectors[index] == true, `target recovery selector {index} did not match a call target`)
		end
	end
	for location in resolutionByLocation do
		assert(matchedResolutions[location] == true, `target recovery resolution does not identify a selected call at {location}`)
	end
	if resultContractMatcher ~= nil then
		(resultContractMatcher :: TargetResultContracts.Matcher):assertFullyUsed("target recovery")
	end
	return {
		by_call_location = byCallLocation,
		proof_bundle_evidence = proofBundleEvidence,
		call_site_count = callCount,
		unresolved_call_count = unresolvedCallCount,
		lowered_unresolved_call_count = spec.lowered_unresolved_call_count,
		resolved_call_count = if resolutions ~= nil then #resolutions else 0,
	}
end

return table.freeze(TargetRecovery)
