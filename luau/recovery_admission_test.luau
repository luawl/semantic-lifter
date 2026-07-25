--!strict

local AstFrontend = require("./ast_frontend")
local RecoveryAdmission = require("./recovery_admission")
local RecoveryManifest = require("./recovery_manifest")
local TargetRecovery = require("./target_recovery")

local sourceText = "abc"
local sourceDigest = TargetRecovery.sha256(sourceText)

local function denseArray(count: number, makeItem: (number) -> any): { any }
	local items = {}
	for index = 1, count do
		table.insert(items, makeItem(index))
	end
	return items
end

local function rejectsWith(action: any, fragment: string)
	local accepted, failure = pcall(action)
	assert(not accepted, `expected rejection containing {fragment}`)
	assert(
		string.find(tostring(failure), fragment, 1, true) ~= nil,
		`rejection did not contain {fragment}: {tostring(failure)}`
	)
end

local function evidence(locator: string, digest: string?): any
	return {
		kind = "decoded_record",
		locator = locator,
		digest = digest,
	}
end

local obligation = {
	kind = "missing_semantics",
	blocks_profile = "readable_luau",
	detail = "bounded recovery admission fixture",
	evidence = evidence("fixture:recovery-admission-obligation", nil),
}

local decodeCount = 0
local boundedBytes = string.rep(" ", RecoveryAdmission.maxManifestBytes)
local boundedByteManifest = RecoveryManifest.fromBytes(
	boundedBytes,
	"bounded-byte-manifest",
	function(bytes: string): any
		decodeCount += 1
		assert(#bytes == RecoveryAdmission.maxManifestBytes, "manifest byte admission changed its exact limit")
		return {
			schema_version = "lifter_recovery_manifest_v1",
			program_obligations = { obligation },
		}
	end
)
assert(#boundedByteManifest.program_obligations == 1 and decodeCount == 1, "exact-limit manifest bytes were rejected")
rejectsWith(function()
	RecoveryManifest.fromBytes(
		boundedBytes .. " ",
		"oversized-byte-manifest",
		function(_bytes: string): any
			decodeCount += 1
			return {}
		end
	)
end, "manifest byte limit")
assert(decodeCount == 1, "oversized manifest bytes reached the JSON decoder")

local boundedObligations = denseArray(RecoveryAdmission.maxCollectionItems, function(_index)
	return obligation
end)
local boundedObligationManifest = RecoveryManifest.fromDecoded({
	schema_version = "lifter_recovery_manifest_v1",
	program_obligations = boundedObligations,
}, "bounded-obligation-manifest")
assert(
	#boundedObligationManifest.program_obligations == RecoveryAdmission.maxCollectionItems,
	"exact-limit obligation collection was rejected"
)
table.insert(boundedObligations, obligation)
rejectsWith(function()
	RecoveryManifest.fromDecoded({
		schema_version = "lifter_recovery_manifest_v1",
		program_obligations = boundedObligations,
	}, "oversized-obligation-manifest")
end, "admission item limit")

local supportedIntrinsics = {
	"error",
	"pcall",
	"xpcall",
	"coroutine.create",
	"coroutine.resume",
	"coroutine.yield",
}
local boundedIntrinsicManifest = RecoveryManifest.fromDecoded({
	schema_version = "lifter_recovery_manifest_v2",
	intrinsic_bindings = denseArray(#supportedIntrinsics, function(index)
		return {
			path = supportedIntrinsics[index],
			evidence = evidence(`fixture:recovery-admission-intrinsic-{index}`, nil),
		}
	end),
}, "bounded-intrinsic-manifest")
assert(#boundedIntrinsicManifest.intrinsic_bindings == #supportedIntrinsics, "valid intrinsic bindings were rejected")
local oversizedIntrinsics = denseArray(RecoveryAdmission.maxIntrinsicBindings + 1, function(index)
	return {
		path = "pcall",
		evidence = evidence(`fixture:oversized-intrinsic-{index}`, nil),
	}
end)
rejectsWith(function()
	RecoveryManifest.fromDecoded({
		schema_version = "lifter_recovery_manifest_v2",
		intrinsic_bindings = oversizedIntrinsics,
	}, "oversized-intrinsic-manifest")
end, "admission item limit")

local boundedTargets = denseArray(RecoveryAdmission.maxCollectionItems, function(index)
	return { kind = "expression", locator = `fixture-target-{index}` }
end)
local boundedTargetManifest = RecoveryManifest.fromDecoded({
	schema_version = "lifter_recovery_manifest_v3",
	target_recovery = {
		source_sha256 = sourceDigest,
		call_site_count = RecoveryAdmission.maxCollectionItems,
		unresolved_call_count = RecoveryAdmission.maxCollectionItems,
		lowered_unresolved_call_count = 0,
		unresolved_targets = boundedTargets,
		detail = "bounded target frontier",
		evidence = evidence("fixture:bounded-target-frontier", sourceDigest),
	},
}, "bounded-target-manifest")
assert(
	boundedTargetManifest.target_recovery ~= nil
		and #(boundedTargetManifest.target_recovery :: any).unresolved_targets == RecoveryAdmission.maxCollectionItems,
	"exact-limit target frontier was rejected"
)
table.insert(boundedTargets, { kind = "expression", locator = "fixture-target-over-limit" })
rejectsWith(function()
	RecoveryManifest.fromDecoded({
		schema_version = "lifter_recovery_manifest_v3",
		target_recovery = {
			source_sha256 = sourceDigest,
			call_site_count = #boundedTargets,
			unresolved_call_count = #boundedTargets,
			lowered_unresolved_call_count = 0,
			unresolved_targets = boundedTargets,
			detail = "oversized target frontier",
			evidence = evidence("fixture:oversized-target-frontier", sourceDigest),
		},
	}, "oversized-target-manifest")
end, "admission item limit")

local boundedResolutions = denseArray(RecoveryAdmission.maxCollectionItems, function(index)
	return {
		call_location = `fixture-call-{index}`,
		origin = { intrinsic = "pcall" },
		evidence = evidence(`fixture:bounded-resolution-{index}`, sourceDigest),
	}
end)
local function resolutionManifest(resolutions: { any }): any
	return {
		schema_version = "lifter_recovery_manifest_v5",
		target_recovery = {
			source_sha256 = sourceDigest,
			call_site_count = #resolutions,
			unresolved_call_count = #resolutions,
			lowered_unresolved_call_count = 0,
			unresolved_target_selectors = { { kind = "local_name", value = "unresolved" } },
			target_resolutions = resolutions,
			detail = "bounded target resolutions",
			evidence = evidence("fixture:bounded-resolution-frontier", sourceDigest),
		},
	}
end
local boundedResolutionManifest = RecoveryManifest.fromDecoded(
	resolutionManifest(boundedResolutions),
	"bounded-resolution-manifest"
)
assert(
	boundedResolutionManifest.target_recovery ~= nil
		and #((boundedResolutionManifest.target_recovery :: any).target_resolutions) == RecoveryAdmission.maxCollectionItems,
	"exact-limit target resolutions were rejected"
)
table.insert(boundedResolutions, {
	call_location = "fixture-call-over-limit",
	origin = { intrinsic = "pcall" },
	evidence = evidence("fixture:resolution-over-limit", sourceDigest),
})
rejectsWith(function()
	RecoveryManifest.fromDecoded(resolutionManifest(boundedResolutions), "oversized-resolution-manifest")
end, "admission item limit")

local function directRecovery(frontierField: string, frontier: { any }, resolutions: { any }?): any
	local spec = {
		source_sha256 = sourceDigest,
		call_site_count = #frontier,
		unresolved_call_count = math.max(#frontier, if resolutions ~= nil then #resolutions else 0),
		lowered_unresolved_call_count = 0,
		detail = "direct recovery admission fixture",
		evidence = evidence("fixture:direct-recovery-admission", sourceDigest),
		target_resolutions = resolutions,
	}
	spec[frontierField] = frontier
	return spec
end

rejectsWith(function()
	TargetRecovery.verify({}, sourceText, directRecovery("unresolved_targets", boundedTargets, nil))
end, "admission item limit")
local oversizedSelectors = denseArray(RecoveryAdmission.maxCollectionItems + 1, function(index)
	return { kind = "local_name", value = `unresolved_{index}` }
end)
rejectsWith(function()
	TargetRecovery.verify({}, sourceText, directRecovery("unresolved_target_selectors", oversizedSelectors, nil))
end, "admission item limit")
rejectsWith(function()
	TargetRecovery.verify(
		{},
		sourceText,
		directRecovery("unresolved_target_selectors", { { kind = "local_name", value = "unresolved" } }, boundedResolutions)
	)
end, "admission item limit")

local oversizedObligationOptions = AstFrontend.tryLift({}, {
	program_id = "oversized-direct-obligations",
	source_name = "oversized-direct-obligations",
	program_obligations = boundedObligations,
})
assert(
	oversizedObligationOptions.program == nil
		and oversizedObligationOptions.diagnostics[1].code == "invalid_options"
		and string.find(oversizedObligationOptions.diagnostics[1].detail, "admission item limit", 1, true) ~= nil,
	"direct frontend options bypassed the obligation budget"
)
local oversizedIntrinsicOptions = AstFrontend.tryLift({}, {
	program_id = "oversized-direct-intrinsics",
	source_name = "oversized-direct-intrinsics",
	intrinsic_bindings = oversizedIntrinsics,
})
assert(
	oversizedIntrinsicOptions.program == nil
		and oversizedIntrinsicOptions.diagnostics[1].code == "invalid_options"
		and string.find(oversizedIntrinsicOptions.diagnostics[1].detail, "admission item limit", 1, true) ~= nil,
	"direct frontend options bypassed the intrinsic budget"
)

return true
