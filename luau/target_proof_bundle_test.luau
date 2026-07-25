--!strict

local RecoveryManifest = require("./recovery_manifest")
local TargetProofBundle = require("./target_proof_bundle")
local TargetRecovery = require("./target_recovery")

local sourceDigest = TargetProofBundle.sha256("abc")
local proofContent = "one detached derivation supports repeated target identities"
local proofEntryId = "sha256:" .. TargetProofBundle.sha256(proofContent)
local signature = string.rep("ab", 64)
local trustedPublicKey = string.rep("cd", 32)
local signedBundleBytes = "exact detached bundle bytes"
local firstOrigin = { intrinsic = "pcall" }
local firstCallLocation = "0,13 - 0,15"
local secondCallLocation = "1,0 - 1,8"
local firstBinding = TargetProofBundle.targetProofDigest(sourceDigest, firstCallLocation, firstOrigin, proofContent)
local secondBinding = TargetProofBundle.targetProofDigest(sourceDigest, secondCallLocation, firstOrigin, proofContent)

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

local function bundleRecord(): any
	return {
		schema_version = "lifter_target_proof_bundle_v1",
		entries = {
			{ id = proofEntryId, content = proofContent, bindings = { firstBinding, secondBinding } },
		},
	}
end

local function bundleInput(decoded: any, bytes: string?, acceptedBytes: string?): RecoveryManifest.ProofBundleInput
	local exactBytes = bytes or signedBundleBytes
	local expectedBytes = acceptedBytes or exactBytes
	return {
		bytes = exactBytes,
		decode = function(message: string): any
			assert(message == exactBytes, "bundle parser did not receive the authenticated bytes")
			return deepClone(decoded)
		end,
		trusted_public_key = trustedPublicKey,
		verify_signature = function(message: string, suppliedSignature: string, publicKey: string): boolean
			return message == expectedBytes and suppliedSignature == signature and publicKey == trustedPublicKey
		end,
	}
end

local function manifestRecord(bundleBytes: string?): any
	local exactBytes = bundleBytes or signedBundleBytes
	local origin = firstOrigin
	return {
		schema_version = "lifter_recovery_manifest_v14",
		proof_bundle = {
			signature = signature,
			evidence = {
				kind = "frontend_proof",
				locator = "fixture:detached-bundle-attestation",
				digest = TargetProofBundle.sha256(exactBytes),
			},
		},
		target_recovery = {
			source_sha256 = sourceDigest,
			call_site_count = 2,
			unresolved_call_count = 2,
			lowered_unresolved_call_count = 2,
			unresolved_target_selectors = {
				{ kind = "local_name", value = "unresolved_callee" },
				{ kind = "global_name", value = "pcall" },
			},
			target_resolutions = {
				{
					call_location = firstCallLocation,
					origin = origin,
					evidence = {
						kind = "dynamic_fixture",
						locator = "fixture:detached-source:local",
						digest = sourceDigest,
					},
					proof = {
						entry_id = proofEntryId,
						evidence = {
							kind = "frontend_proof",
							locator = "fixture:detached-site:local",
							digest = firstBinding,
						},
					},
				},
				{
					call_location = secondCallLocation,
					origin = origin,
					evidence = {
						kind = "dynamic_fixture",
						locator = "fixture:detached-source:global",
						digest = sourceDigest,
					},
					proof = {
						entry_id = proofEntryId,
						evidence = {
							kind = "frontend_proof",
							locator = "fixture:detached-site:global",
							digest = secondBinding,
						},
					},
				},
			},
			detail = "target identities require one independently attested derivation",
			evidence = {
				kind = "structural_derivation",
				locator = "fixture:detached-frontier",
				digest = sourceDigest,
			},
		},
	}
end

local function expectReject(label: string, action: () -> (), needle: string)
	local outcome = table.pack(pcall(action))
	local accepted = outcome[1]
	local failure = outcome[2]
	assert(not accepted, `{label} was accepted`)
	assert(string.find(tostring(failure), needle, 1, true) ~= nil, `{label} rejected for an unexpected reason: {failure}`)
end

local validAccessPath = { root = { environment = "namespace" }, keys = { "method" } }
local invalidCanonicalOrigins: { { label: string, origin: any, needle: string } } = {
	{
		label = "ambiguous target origin",
		origin = { intrinsic = "pcall", environment = "pcall" },
		needle = "exactly one semantic variant",
	},
	{
		label = "shadow target-origin field",
		origin = { intrinsic = "pcall", shadow = true },
		needle = "shadow is not supported",
	},
	{
		label = "ambiguous table root",
		origin = {
			table_get = {
				table = { local_value = "0,0 - 0,1", environment = "namespace" },
				key = "method",
			},
		},
		needle = "exactly one semantic variant",
	},
	{
		label = "ambiguous literal key",
		origin = {
			table_get = {
				table = { environment = "namespace" },
				key = { literal = { boolean = false, number = 0 } },
			},
		},
		needle = "exactly one semantic variant",
	},
	{
		label = "ambiguous namecall receiver",
		origin = {
			namecall = {
				receiver = { access_path = validAccessPath, environment = "namespace" },
				method = "run",
			},
		},
		needle = "exactly one semantic variant",
	},
	{
		label = "shadow access-path field",
		origin = { access_path = { root = { environment = "namespace" }, keys = { "method" }, shadow = true } },
		needle = "shadow is not supported",
	},
	{
		label = "shadow namecall field",
		origin = { namecall = { receiver = { environment = "namespace" }, method = "run", shadow = true } },
		needle = "shadow is not supported",
	},
	{
		label = "empty access path",
		origin = { access_path = { root = { environment = "namespace" }, keys = {} } },
		needle = "keys count is invalid",
	},
}
for _, row in invalidCanonicalOrigins do
	expectReject(row.label, function()
		TargetProofBundle.targetProofDigest(sourceDigest, firstCallLocation, row.origin, proofContent)
	end, row.needle)
end

local function openBundleRecord(record: any, bytes: string): TargetProofBundle.Bundle
	return TargetProofBundle.open(bundleInput(record, bytes), signature, {
		kind = "frontend_proof",
		locator = "fixture:direct-bundle-open",
		digest = TargetProofBundle.sha256(bytes),
	}, "direct-bundle")
end

local nonArrayEntries = bundleRecord()
local extraContent = "entry stored outside the declared bundle array"
nonArrayEntries.entries.shadow = {
	id = "sha256:" .. TargetProofBundle.sha256(extraContent),
	content = extraContent,
	bindings = { string.rep("5", 64) },
}
expectReject("non-array bundle entry", function()
	openBundleRecord(nonArrayEntries, "non-array entry bundle bytes")
end, "entries must be a dense array")

local nonArrayBindings = bundleRecord()
nonArrayBindings.entries[1].bindings.shadow = string.rep("6", 64)
expectReject("non-array proof binding", function()
	openBundleRecord(nonArrayBindings, "non-array binding bundle bytes")
end, "bindings must be a dense array")

local nonBooleanVerifier: any = bundleInput(bundleRecord(), "non-Boolean verifier bundle bytes")
nonBooleanVerifier.verify_signature = function(): any
	return "trusted"
end
expectReject("non-Boolean signature result", function()
	TargetProofBundle.open(nonBooleanVerifier, signature, {
		kind = "frontend_proof",
		locator = "fixture:non-Boolean-verifier",
		digest = TargetProofBundle.sha256(nonBooleanVerifier.bytes),
	}, "non-Boolean-verifier")
end, "signature is not trusted")

local decoded = RecoveryManifest.fromDecoded(manifestRecord(), "detached-proof", bundleInput(bundleRecord()))
local recovery = decoded.target_recovery
assert(recovery ~= nil and recovery.proof_bundle_evidence ~= nil, "V14 lost detached bundle attestation evidence")
assert(recovery.target_resolutions ~= nil and #recovery.target_resolutions == 2, "V14 lost repeated proof references")
local firstProof = recovery.target_resolutions[1].proof
local secondProof = recovery.target_resolutions[2].proof
assert(
	firstProof ~= nil
		and secondProof ~= nil
		and firstProof.content == proofContent
		and secondProof.content == proofContent,
	"V14 did not resolve one content-addressed entry at both sites"
)

local targetLocal = { type = "AstLocal", name = "unresolved_callee", location = "0,6 - 0,12" }
local targetDocument: any = {
	root = {
		type = "AstStatBlock",
		location = "0,0 - 2,0",
		body = ({
			{
				type = "AstStatLocal",
				location = "0,0 - 0,12",
				vars = { targetLocal },
				values = { { type = "AstExprGlobal", location = "0,15 - 0,20", global = "pcall" } },
			},
			{
				type = "AstExprCall",
				location = "0,13 - 0,15",
				func = { type = "AstExprLocal", location = "0,13 - 0,14", ["local"] = targetLocal },
			},
			{
				type = "AstExprCall",
				location = "1,0 - 1,8",
				func = { type = "AstExprGlobal", location = "1,0 - 1,5", global = "pcall" },
			},
		} :: { any }),
	},
}
local verified = TargetRecovery.verify(targetDocument, "abc", recovery :: any)
assert(verified.resolved_call_count == 2, "detached proof recovery did not resolve both selected sites")
assert(verified.proof_bundle_evidence ~= nil, "verified recovery lost shared bundle evidence")

local nonArrayRecovery = deepClone(recovery)
nonArrayRecovery.target_resolutions.shadow = deepClone(nonArrayRecovery.target_resolutions[1])
expectReject("non-array direct recovery resolution", function()
	TargetRecovery.verify(targetDocument, "abc", nonArrayRecovery)
end, "resolution list must be a dense array")

local mutatedRecovery = deepClone(recovery)
mutatedRecovery.target_resolutions[1].proof.content ..= " tampered"
expectReject("post-decode detached content mutation", function()
	TargetRecovery.verify(targetDocument, "abc", mutatedRecovery)
end, "proof digest does not authenticate")

expectReject("missing detached input", function()
	RecoveryManifest.fromDecoded(manifestRecord(), "missing-detached-input")
end, "requires detached proof bundle bytes")

local legacyWithBundle = manifestRecord()
legacyWithBundle.schema_version = "lifter_recovery_manifest_v13"
expectReject("legacy detached bundle", function()
	RecoveryManifest.fromDecoded(legacyWithBundle, "legacy-detached-input", bundleInput(bundleRecord()))
end, "unknown field proof_bundle")

local wrongDigest = manifestRecord()
wrongDigest.proof_bundle.evidence.digest = string.rep("0", 64)
expectReject("wrong bundle digest", function()
	RecoveryManifest.fromDecoded(wrongDigest, "wrong-bundle-digest", bundleInput(bundleRecord()))
end, "exact detached bundle bytes")

local wrongSignature = manifestRecord()
wrongSignature.proof_bundle.signature = string.rep("ef", 64)
expectReject("wrong bundle signature", function()
	RecoveryManifest.fromDecoded(wrongSignature, "wrong-bundle-signature", bundleInput(bundleRecord()))
end, "signature is not trusted")

local reorderedBytes = "reordered detached bundle bytes"
local reorderedManifest = manifestRecord(reorderedBytes)
expectReject("reordered signed bytes", function()
	RecoveryManifest.fromDecoded(
		reorderedManifest,
		"reordered-bundle",
		bundleInput(bundleRecord(), reorderedBytes, signedBundleBytes)
	)
end, "signature is not trusted")

local unrelatedContent = "different authenticated proof content"
local unrelatedBundle = {
	schema_version = "lifter_target_proof_bundle_v1",
	entries = {
		{
			id = "sha256:" .. TargetProofBundle.sha256(unrelatedContent),
			content = unrelatedContent,
			bindings = { string.rep("1", 64) },
		},
	},
}
local unrelatedBytes = "different authenticated bundle bytes"
local unrelatedManifest = manifestRecord(unrelatedBytes)
expectReject("authenticated bytes are parsing authority", function()
	RecoveryManifest.fromDecoded(unrelatedManifest, "unrelated-authenticated-bundle", bundleInput(unrelatedBundle, unrelatedBytes))
end, "does not identify an entry")

local reboundManifest = manifestRecord()
local reboundOrigin = { intrinsic = "xpcall" }
reboundManifest.target_recovery.target_resolutions[1].origin = reboundOrigin
reboundManifest.target_recovery.target_resolutions[1].proof.evidence.digest = TargetProofBundle.targetProofDigest(
	sourceDigest,
	firstCallLocation,
	reboundOrigin,
	proofContent
)
expectReject("unsigned semantic rebinding", function()
	RecoveryManifest.fromDecoded(reboundManifest, "unsigned-rebinding", bundleInput(bundleRecord()))
end, "is not authorized by the detached proof bundle")

local missingBindingBundle = bundleRecord()
table.remove(missingBindingBundle.entries[1].bindings, 1)
expectReject("missing signed site binding", function()
	RecoveryManifest.fromDecoded(manifestRecord("missing-binding bundle bytes"), "missing-binding", bundleInput(missingBindingBundle, "missing-binding bundle bytes"))
end, "is not authorized by the detached proof bundle")

local unusedBindingBundle = bundleRecord()
table.insert(unusedBindingBundle.entries[1].bindings, string.rep("2", 64))
expectReject("unused signed site binding", function()
	RecoveryManifest.fromDecoded(manifestRecord("unused-binding bundle bytes"), "unused-binding", bundleInput(unusedBindingBundle, "unused-binding bundle bytes"))
end, "contains unused proof binding")

local duplicateBindingBundle = bundleRecord()
table.insert(duplicateBindingBundle.entries[1].bindings, firstBinding)
expectReject("duplicate signed site binding", function()
	RecoveryManifest.fromDecoded(manifestRecord("duplicate-binding bundle bytes"), "duplicate-binding", bundleInput(duplicateBindingBundle, "duplicate-binding bundle bytes"))
end, "duplicates a proof binding")

local missingEntry = manifestRecord()
missingEntry.target_recovery.target_resolutions[1].proof.entry_id = "sha256:" .. string.rep("0", 64)
expectReject("missing bundle entry", function()
	RecoveryManifest.fromDecoded(missingEntry, "missing-entry", bundleInput(bundleRecord()))
end, "does not identify an entry")

local unusedBundle = bundleRecord()
local unusedContent = "unused detached derivation"
table.insert(unusedBundle.entries, {
	id = "sha256:" .. TargetProofBundle.sha256(unusedContent),
	content = unusedContent,
	bindings = { string.rep("3", 64) },
})
local unusedBundleBytes = "unused-entry bundle bytes"
expectReject("unused bundle entry", function()
	RecoveryManifest.fromDecoded(manifestRecord(unusedBundleBytes), "unused-entry", bundleInput(unusedBundle, unusedBundleBytes))
end, "contains unused proof entry")

local duplicateBundle = bundleRecord()
table.insert(duplicateBundle.entries, deepClone(duplicateBundle.entries[1]))
local duplicateBundleBytes = "duplicate-entry bundle bytes"
expectReject("duplicate bundle content", function()
	RecoveryManifest.fromDecoded(manifestRecord(duplicateBundleBytes), "duplicate-entry", bundleInput(duplicateBundle, duplicateBundleBytes))
end, "duplicates proof content")

local collisionBundle = bundleRecord()
table.insert(collisionBundle.entries, { id = proofEntryId, content = "different proof bytes", bindings = { string.rep("4", 64) } })
local collisionBundleBytes = "collision-entry bundle bytes"
expectReject("bundle digest collision", function()
	RecoveryManifest.fromDecoded(manifestRecord(collisionBundleBytes), "colliding-entry", bundleInput(collisionBundle, collisionBundleBytes))
end, "collides with different proof content")

local wrongAddressBundle = bundleRecord()
wrongAddressBundle.entries[1].id = "sha256:" .. string.rep("1", 64)
local wrongAddressBundleBytes = "wrong-address bundle bytes"
expectReject("wrong content address", function()
	RecoveryManifest.fromDecoded(manifestRecord(wrongAddressBundleBytes), "wrong-content-address", bundleInput(wrongAddressBundle, wrongAddressBundleBytes))
end, "does not content-address")

local oversizedInput = bundleInput(bundleRecord(), string.rep("x", TargetProofBundle.maxBundleBytes + 1))
expectReject("oversized detached bundle", function()
	RecoveryManifest.fromDecoded(manifestRecord(), "oversized-bundle", oversizedInput)
end, "byte size is invalid")
