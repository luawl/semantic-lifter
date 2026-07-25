--!strict

local serde = require("@lune/serde")
local RecoveryManifestCore = require("./recovery_manifest")
local TargetRecovery = require("./target_recovery")
local AstFrontend = require("./ast_frontend")
local LifterIR = require("./lifter_ir")
local JsonCodec = require("./json_codec")

local RecoveryManifest = {
	decode = function(text: string, manifestName: string)
		return RecoveryManifestCore.fromBytes(text, manifestName, function(bytes: string): any
			return serde.decode("json", bytes)
		end)
	end,
}

assert(TargetRecovery.sha256("") == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", "empty SHA-256 vector changed")
assert(TargetRecovery.sha256("abc") == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad", "SHA-256 abc vector changed")

local manifest = RecoveryManifest.decode([[
{
  "schema_version": "lifter_recovery_manifest_v1",
  "program_obligations": [
    {
      "kind": "missing_semantics",
      "blocks_profile": "readable_luau",
      "detail": "target semantics remain unresolved",
      "evidence": {
        "kind": "decoded_record",
        "locator": "fixture:recovery-manifest"
      }
    }
  ]
}
]], "valid-manifest")

local obligations = manifest.program_obligations
assert(#obligations == 1, "valid manifest did not retain its obligation")
assert(#manifest.intrinsic_bindings == 0, "v1 manifest gained intrinsic bindings")
assert(obligations[1].kind == "missing_semantics", "valid manifest changed its obligation kind")
assert(obligations[1].evidence.locator == "fixture:recovery-manifest", "valid manifest changed its provenance")
assert(manifest.target_recovery == nil, "v1 manifest gained target recovery")

local obligationRecord = {
	kind = "missing_semantics",
	blocks_profile = "readable_luau",
	detail = "target semantics remain unresolved",
	evidence = {
		kind = "decoded_record",
		locator = "fixture:non-array-obligation",
	},
}
local nonArrayObligations: any = { obligationRecord }
nonArrayObligations.shadow = obligationRecord
local acceptedNonArrayObligation = pcall(function()
	RecoveryManifestCore.fromDecoded({
		schema_version = "lifter_recovery_manifest_v1",
		program_obligations = nonArrayObligations,
	}, "non-array-obligations")
end)
assert(not acceptedNonArrayObligation, "manifest accepted a non-array obligation entry")

local intrinsicManifest = RecoveryManifest.decode([[
{
  "schema_version": "lifter_recovery_manifest_v2",
  "intrinsic_bindings": [
    {
      "path": "pcall",
      "evidence": {
        "kind": "frontend_proof",
        "locator": "fixture:stable-pcall-binding"
      }
    },
    {
      "path": "coroutine.resume",
      "evidence": {
        "kind": "frontend_proof",
        "locator": "fixture:stable-coroutine-resume-binding"
      }
    },
    {
      "path": "error",
      "evidence": {
        "kind": "frontend_proof",
        "locator": "fixture:stable-error-binding"
      }
    }
  ]
}
]], "intrinsic-manifest")
assert(#intrinsicManifest.program_obligations == 0, "intrinsic manifest gained an obligation")
assert(#intrinsicManifest.intrinsic_bindings == 3, "intrinsic manifest lost a binding")
assert(intrinsicManifest.intrinsic_bindings[2].path == "coroutine.resume", "intrinsic path changed")
assert(intrinsicManifest.intrinsic_bindings[3].path == "error", "error intrinsic path changed")
assert(intrinsicManifest.target_recovery == nil, "v2 manifest gained target recovery")

local targetManifest = RecoveryManifest.decode([[
{
  "schema_version": "lifter_recovery_manifest_v3",
  "target_recovery": {
    "source_sha256": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    "call_site_count": 2,
    "unresolved_call_count": 1,
    "lowered_unresolved_call_count": 1,
    "unresolved_targets": [
      { "kind": "local", "locator": "0,6 - 0,12" }
    ],
    "detail": "callee identity remains unresolved",
    "evidence": {
      "kind": "structural_derivation",
      "locator": "fixture:target-frontier",
      "digest": "0123456789abcdef"
    }
  }
}
]], "target-manifest")
local targetRecovery = targetManifest.target_recovery
assert(targetRecovery ~= nil, "v3 manifest lost target recovery")
local targetDocumentLocal = { type = "AstLocal", name = "unresolved_callee", location = "0,6 - 0,12" }
local targetDocument = {
	root = {
		type = "AstStatBlock",
		location = "0,0 - 2,0",
		body = {
			{
				type = "AstStatLocal",
				location = "0,0 - 0,12",
				vars = { targetDocumentLocal },
				values = { { type = "AstExprGlobal", location = "0,15 - 0,20", global = "pcall" } },
			},
			{
				type = "AstExprCall",
				location = "0,13 - 0,15",
				func = {
					type = "AstExprLocal",
					location = "0,13 - 0,14",
					["local"] = targetDocumentLocal,
				},
			},
			{
				type = "AstExprCall",
				location = "1,0 - 1,7",
				func = { type = "AstExprGlobal", location = "1,0 - 1,5", global = "print" },
			},
		},
	},
}

local verified = TargetRecovery.verify(targetDocument, "abc", targetRecovery :: any)
assert(verified.call_site_count == 2, "target recovery changed its call census")
assert(verified.unresolved_call_count == 1, "target recovery changed its unresolved census")
assert(verified.lowered_unresolved_call_count == 1, "target recovery changed its lowered census")
assert(verified.by_call_location["0,13 - 0,15"] ~= nil, "target recovery lost the unresolved call site")
assert(verified.by_call_location["1,0 - 1,7"] == nil, "target recovery marked an unlisted global target")
local acceptedWrongSource = pcall(TargetRecovery.verify, targetDocument, "abd", targetRecovery :: any)
assert(not acceptedWrongSource, "target recovery accepted a different source digest")
local staleTargetRecovery = table.clone(targetRecovery :: any)
staleTargetRecovery.unresolved_targets = { { kind = "global", locator = "missing" } }
local acceptedStaleTarget = pcall(TargetRecovery.verify, targetDocument, "abc", staleTargetRecovery)
assert(not acceptedStaleTarget, "target recovery accepted a target absent from the AST")

local selectorManifest = RecoveryManifest.decode([[
{
  "schema_version": "lifter_recovery_manifest_v4",
  "target_recovery": {
    "source_sha256": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    "call_site_count": 2,
    "unresolved_call_count": 1,
    "lowered_unresolved_call_count": 1,
    "unresolved_target_selectors": [
      { "kind": "local_name_prefix", "value": "unresolved_" }
    ],
		"detail": "explicitly marked callee identity remains unresolved",
		"evidence": {
		  "kind": "structural_derivation",
		  "locator": "fixture:target-selector",
		  "digest": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
		}
  }
}
]], "target-selector-manifest")
local selectorRecovery = selectorManifest.target_recovery
assert(selectorRecovery ~= nil, "v4 manifest lost target recovery")
assert(selectorRecovery.unresolved_targets == nil, "v4 manifest gained an explicit target list")
assert(
	selectorRecovery.unresolved_target_selectors ~= nil and #selectorRecovery.unresolved_target_selectors == 1,
	"v4 manifest lost its target selector"
)
local selectorVerified = TargetRecovery.verify(targetDocument, "abc", selectorRecovery :: any)
assert(selectorVerified.call_site_count == 2, "target selector changed its call census")
assert(selectorVerified.unresolved_call_count == 1, "target selector changed its unresolved census")
assert(selectorVerified.by_call_location["0,13 - 0,15"] ~= nil, "target selector lost its marked local call")
assert(selectorVerified.by_call_location["1,0 - 1,7"] == nil, "target selector marked an unrelated global call")

local runtimeTraversalDocument: any = {
	root = {
		type = "AstStatBlock",
		body = ({
			{
				type = "AstStatLocal",
				vars = { targetDocumentLocal },
				values = { { type = "AstExprGlobal", global = "pcall" } },
			},
			{
				type = "AstStatTypeAlias",
				value = { type = "AstTypeTypeof", expr = {
					type = "AstExprCall",
					location = "type-only-call",
					func = { type = "AstExprGlobal", global = "type_noise" },
					args = {},
				} },
			},
			{ type = "AstStatExpr", expr = {
				type = "AstExprCall",
				location = "runtime-selected-call",
				func = { type = "AstExprLocal", ["local"] = targetDocumentLocal },
				args = {},
			} },
			{ type = "AstStatExpr", expr = {
				type = "AstExprCall",
				location = "runtime-unrelated-call",
				func = {
					type = "AstExprTypeAssertion",
					expr = { type = "AstExprGlobal", global = "print" },
					annotation = {
						type = "AstTypeTypeof",
						expr = { type = "AstExprLocal", ["local"] = targetDocumentLocal },
					},
				},
				args = {},
			} },
		} :: { any }),
	},
}
local runtimeTraversalVerified = TargetRecovery.verify(runtimeTraversalDocument, "abc", selectorRecovery :: any)
assert(runtimeTraversalVerified.call_site_count == 2, "target recovery counted a type-only call")
assert(runtimeTraversalVerified.unresolved_call_count == 1, "target selector matched a type-only reference")
assert(runtimeTraversalVerified.by_call_location["runtime-selected-call"] ~= nil, "runtime target was not selected")
assert(runtimeTraversalVerified.by_call_location["runtime-unrelated-call"] == nil, "annotation reference selected a runtime call")

local staleSelectorRecovery = table.clone(selectorRecovery :: any)
staleSelectorRecovery.unresolved_target_selectors = { { kind = "local_name_prefix", value = "absent_" } }
local acceptedStaleSelector = pcall(TargetRecovery.verify, targetDocument, "abc", staleSelectorRecovery)
assert(not acceptedStaleSelector, "target recovery accepted a selector absent from call targets")
local unauthenticatedSelectorRecovery = table.clone(selectorRecovery :: any)
unauthenticatedSelectorRecovery.evidence = table.clone((selectorRecovery :: any).evidence)
unauthenticatedSelectorRecovery.evidence.digest = "unrelated-proof"
local acceptedUnauthenticatedSelector = pcall(
	TargetRecovery.verify,
	targetDocument,
	"abc",
	unauthenticatedSelectorRecovery
)
assert(not acceptedUnauthenticatedSelector, "target recovery accepted selector evidence for another artifact")

local resolutionManifest = RecoveryManifest.decode([[
{
  "schema_version": "lifter_recovery_manifest_v5",
  "target_recovery": {
    "source_sha256": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    "call_site_count": 2,
    "unresolved_call_count": 1,
    "lowered_unresolved_call_count": 1,
    "unresolved_target_selectors": [
      { "kind": "local_name", "value": "unresolved_callee" }
    ],
    "target_resolutions": [
      {
        "call_location": "0,13 - 0,15",
        "origin": { "intrinsic": "pcall" },
        "evidence": {
          "kind": "dynamic_fixture",
          "locator": "fixture:resolved-pcall",
          "digest": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        }
      }
    ],
    "detail": "callee identity requires authenticated recovery",
    "evidence": {
      "kind": "structural_derivation",
      "locator": "fixture:resolution-frontier",
      "digest": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    }
  }
}
]], "target-resolution-manifest")
local resolutionRecovery = resolutionManifest.target_recovery
assert(resolutionRecovery ~= nil, "v5 manifest lost target recovery")
assert(resolutionRecovery.target_resolutions ~= nil and #resolutionRecovery.target_resolutions == 1, "v5 manifest lost its resolution")
local resolutionVerified = TargetRecovery.verify(targetDocument, "abc", resolutionRecovery :: any)
assert(resolutionVerified.resolved_call_count == 1, "target recovery changed its resolved call count")
local resolvedSite = resolutionVerified.by_call_location["0,13 - 0,15"]
assert(
	resolvedSite ~= nil
		and resolvedSite.resolution ~= nil
		and resolvedSite.resolution.origin.kind == "intrinsic"
		and resolvedSite.resolution.origin.path == "pcall",
	"target recovery lost the selected call's semantic origin"
)
local duplicateResolutionRecovery = table.clone(resolutionRecovery :: any)
local originalResolution = ((resolutionRecovery :: any).target_resolutions :: { any })[1]
duplicateResolutionRecovery.target_resolutions = { originalResolution, table.clone(originalResolution) }
local acceptedDuplicateResolution = pcall(TargetRecovery.verify, targetDocument, "abc", duplicateResolutionRecovery)
assert(not acceptedDuplicateResolution, "target recovery accepted ambiguous resolutions for one call")

local unauthenticatedResolutionRecovery = table.clone(resolutionRecovery :: any)
unauthenticatedResolutionRecovery.target_resolutions = table.clone((resolutionRecovery :: any).target_resolutions)
unauthenticatedResolutionRecovery.target_resolutions[1] = table.clone(unauthenticatedResolutionRecovery.target_resolutions[1])
unauthenticatedResolutionRecovery.target_resolutions[1].evidence = table.clone(unauthenticatedResolutionRecovery.target_resolutions[1].evidence)
unauthenticatedResolutionRecovery.target_resolutions[1].evidence.digest = "unrelated-proof"
local acceptedUnauthenticatedResolution = pcall(
	TargetRecovery.verify,
	targetDocument,
	"abc",
	unauthenticatedResolutionRecovery
)
assert(not acceptedUnauthenticatedResolution, "target recovery accepted resolution evidence for another artifact")

local staleResolutionRecovery = table.clone(resolutionRecovery :: any)
staleResolutionRecovery.target_resolutions = table.clone((resolutionRecovery :: any).target_resolutions)
staleResolutionRecovery.target_resolutions[1] = table.clone(staleResolutionRecovery.target_resolutions[1])
staleResolutionRecovery.target_resolutions[1].call_location = "1,0 - 1,7"
local acceptedUnselectedResolution = pcall(TargetRecovery.verify, targetDocument, "abc", staleResolutionRecovery)
assert(not acceptedUnselectedResolution, "target recovery accepted a resolution for an unselected call")

local proofSourceDigest = TargetRecovery.sha256("abc")
local proofLocation = "0,13 - 0,15"
local proofOrigin = { intrinsic = "pcall" }
local proofContent = "immutable local initializer establishes intrinsic identity"
local proofDigest = TargetRecovery.targetProofDigest(proofSourceDigest, proofLocation, proofOrigin, proofContent)
assert(#proofDigest == 64 and string.match(proofDigest, "^[0-9a-f]+$") ~= nil, "target proof digest is not SHA-256")
assert(proofDigest == "86902438481ca0571095a29ee44f16122fadbbc904720a3a1314dd473d42af43", "target proof digest vector changed")
assert(
	proofDigest ~= TargetRecovery.targetProofDigest(proofSourceDigest, "0,14 - 0,16", proofOrigin, proofContent)
		and proofDigest ~= TargetRecovery.targetProofDigest(proofSourceDigest, proofLocation, { intrinsic = "error" }, proofContent)
		and proofDigest ~= TargetRecovery.targetProofDigest(TargetRecovery.sha256("abd"), proofLocation, proofOrigin, proofContent)
		and proofDigest ~= TargetRecovery.targetProofDigest(proofSourceDigest, proofLocation, proofOrigin, proofContent .. "!"),
	"target proof digest is not bound to content, source, location, and semantic origin"
)
local compositionalProofOrigin: any = {
	namecall = {
		receiver = {
			access_path = {
				root = { environment = "namespace" },
				keys = { "dispatch", { literal = { number = 7 } }, { literal = { boolean = false } } },
			},
		},
		method = "run",
	},
}
local compositionalProofDigest = TargetRecovery.targetProofDigest(
	proofSourceDigest,
	proofLocation,
	compositionalProofOrigin,
	proofContent
)
compositionalProofOrigin.namecall.method = "stop"
assert(
	compositionalProofDigest
		~= TargetRecovery.targetProofDigest(proofSourceDigest, proofLocation, compositionalProofOrigin, proofContent),
	"target proof digest did not bind a compositional namecall origin"
)
compositionalProofOrigin.namecall.method = "run"

local function proofBoundManifestRecord(): any
	return {
		schema_version = "lifter_recovery_manifest_v13",
		target_recovery = {
			source_sha256 = proofSourceDigest,
			call_site_count = 2,
			unresolved_call_count = 1,
			lowered_unresolved_call_count = 1,
			unresolved_target_selectors = {
				{ kind = "local_name", value = "unresolved_callee" },
			},
			target_resolutions = {
				{
					call_location = proofLocation,
					origin = { intrinsic = "pcall" },
					evidence = {
						kind = "dynamic_fixture",
						locator = "fixture:proof-bound-source",
						digest = proofSourceDigest,
					},
					proof = {
						content = proofContent,
						evidence = {
							kind = "frontend_proof",
							locator = "fixture:proof-bound-derivation",
							digest = proofDigest,
						},
					},
				},
			},
			detail = "callee identity requires source-bound derivation evidence",
			evidence = {
				kind = "structural_derivation",
				locator = "fixture:proof-bound-frontier",
				digest = proofSourceDigest,
			},
		},
	}
end

local proofBoundManifest = RecoveryManifestCore.fromDecoded(proofBoundManifestRecord(), "proof-bound-manifest")
local proofBoundRecovery = proofBoundManifest.target_recovery
assert(proofBoundRecovery ~= nil and proofBoundRecovery.require_independent_proof, "v13 manifest lost its proof capability")
local proofBoundResolution = if proofBoundRecovery ~= nil and proofBoundRecovery.target_resolutions ~= nil
	then proofBoundRecovery.target_resolutions[1]
	else nil
assert(
	proofBoundResolution ~= nil
		and proofBoundResolution.proof ~= nil
		and proofBoundResolution.proof.content == proofContent
		and proofBoundResolution.proof.evidence.digest == proofDigest,
	"v13 manifest lost its supplied proof content or authenticated digest"
)
local proofBoundVerified = TargetRecovery.verify(targetDocument, "abc", proofBoundRecovery :: any)
local proofBoundSite = proofBoundVerified.by_call_location[proofLocation]
assert(
	proofBoundSite ~= nil
		and proofBoundSite.resolution ~= nil
		and proofBoundSite.resolution.proof_evidence ~= nil
		and proofBoundSite.resolution.proof_evidence.digest == proofDigest,
	"v13 verification lost independent proof evidence"
)

local missingProof = proofBoundManifestRecord()
missingProof.target_recovery.target_resolutions[1].proof = nil
assert(not pcall(RecoveryManifestCore.fromDecoded, missingProof, "missing-proof"), "v13 accepted a missing proof envelope")

local staleProof = proofBoundManifestRecord()
staleProof.target_recovery.target_resolutions[1].proof.content ..= " tampered"
assert(not pcall(RecoveryManifestCore.fromDecoded, staleProof, "stale-proof"), "v13 accepted stale proof content")

local wrongProofSource = proofBoundManifestRecord()
local wrongSourceDigest = TargetRecovery.sha256("abd")
wrongProofSource.target_recovery.source_sha256 = wrongSourceDigest
wrongProofSource.target_recovery.evidence.digest = wrongSourceDigest
wrongProofSource.target_recovery.target_resolutions[1].evidence.digest = wrongSourceDigest
assert(not pcall(RecoveryManifestCore.fromDecoded, wrongProofSource, "wrong-proof-source"), "v13 accepted a proof bound to another source")

local wrongProofLocation = proofBoundManifestRecord()
wrongProofLocation.target_recovery.target_resolutions[1].call_location = "0,14 - 0,16"
assert(not pcall(RecoveryManifestCore.fromDecoded, wrongProofLocation, "wrong-proof-location"), "v13 accepted a proof bound to another call")

local wrongProofOrigin = proofBoundManifestRecord()
wrongProofOrigin.target_recovery.target_resolutions[1].origin = { intrinsic = "error" }
assert(not pcall(RecoveryManifestCore.fromDecoded, wrongProofOrigin, "wrong-proof-origin"), "v13 accepted a proof bound to another origin")

local digestOnlyProof = proofBoundManifestRecord()
digestOnlyProof.target_recovery.target_resolutions[1].proof.content = nil
assert(not pcall(RecoveryManifestCore.fromDecoded, digestOnlyProof, "digest-only-proof"), "v13 trusted a claimed digest without proof content")

local wrongProofKind = proofBoundManifestRecord()
wrongProofKind.target_recovery.target_resolutions[1].proof.evidence.kind = "dynamic_fixture"
assert(not pcall(RecoveryManifestCore.fromDecoded, wrongProofKind, "wrong-proof-kind"), "v13 accepted non-proof evidence as an independent proof")

local sharedProofLocator = proofBoundManifestRecord()
sharedProofLocator.target_recovery.target_resolutions[1].proof.evidence.locator = "fixture:proof-bound-source"
assert(not pcall(RecoveryManifestCore.fromDecoded, sharedProofLocator, "shared-proof-locator"), "v13 accepted source evidence as its independent proof")

local duplicateProof = proofBoundManifestRecord()
local duplicatedResolution = table.clone(duplicateProof.target_recovery.target_resolutions[1])
table.insert(duplicateProof.target_recovery.target_resolutions, duplicatedResolution)
assert(not pcall(RecoveryManifestCore.fromDecoded, duplicateProof, "duplicate-proof"), "v13 accepted a duplicate proof envelope")

local oldVersionProof = proofBoundManifestRecord()
oldVersionProof.schema_version = "lifter_recovery_manifest_v12"
assert(not pcall(RecoveryManifestCore.fromDecoded, oldVersionProof, "v12-proof"), "v12 accepted a V13 proof envelope")

local mutatedProofRecovery: any = table.clone(proofBoundRecovery :: any)
mutatedProofRecovery.target_resolutions = table.clone((proofBoundRecovery :: any).target_resolutions)
mutatedProofRecovery.target_resolutions[1] = table.clone(mutatedProofRecovery.target_resolutions[1])
mutatedProofRecovery.target_resolutions[1].proof = table.clone(mutatedProofRecovery.target_resolutions[1].proof)
mutatedProofRecovery.target_resolutions[1].proof.content ..= " mutated"
assert(
	not pcall(TargetRecovery.verify, targetDocument, "abc", mutatedProofRecovery),
	"target recovery trusted proof content mutated after manifest decoding"
)

local acceptedUnknownResolutionOrigin = pcall(function()
	RecoveryManifest.decode([[
{
  "schema_version": "lifter_recovery_manifest_v5",
  "target_recovery": {
    "source_sha256": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    "call_site_count": 1,
    "unresolved_call_count": 1,
    "lowered_unresolved_call_count": 1,
    "unresolved_target_selectors": [
      { "kind": "global_name", "value": "unknown" }
    ],
    "target_resolutions": [
      {
        "call_location": "0,0 - 0,2",
        "origin": { "intrinsic": "coroutine.wrap" },
        "evidence": {
          "kind": "dynamic_fixture",
          "locator": "fixture:unsupported-origin",
          "digest": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        }
      }
    ],
    "detail": "invalid origin",
    "evidence": {
      "kind": "structural_derivation",
      "locator": "fixture:unsupported-origin-frontier",
      "digest": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    }
  }
}
]], "unknown-resolution-origin")
end)
assert(not acceptedUnknownResolutionOrigin, "manifest accepted an unsupported recovery origin")

local acceptedUnknownSelector = pcall(function()
	RecoveryManifest.decode([[
{
  "schema_version": "lifter_recovery_manifest_v4",
  "target_recovery": {
    "source_sha256": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    "call_site_count": 1,
    "unresolved_call_count": 1,
    "lowered_unresolved_call_count": 1,
    "unresolved_target_selectors": [
      { "kind": "sample_rule", "value": "unresolved_" }
    ],
    "detail": "invalid selector",
    "evidence": { "kind": "structural_derivation", "locator": "fixture:invalid-selector" }
  }
}
]], "unknown-target-selector")
end)
assert(not acceptedUnknownSelector, "manifest accepted a source-specific target selector kind")

local acceptedDuplicateIntrinsic = pcall(function()
	RecoveryManifest.decode([[
{
  "schema_version": "lifter_recovery_manifest_v2",
  "intrinsic_bindings": [
    { "path": "pcall", "evidence": { "kind": "frontend_proof", "locator": "fixture:first" } },
    { "path": "pcall", "evidence": { "kind": "frontend_proof", "locator": "fixture:second" } }
  ]
}
]], "duplicate-intrinsic-manifest")
end)
assert(not acceptedDuplicateIntrinsic, "manifest accepted a duplicate intrinsic binding")

local acceptedUnknownIntrinsic = pcall(function()
	RecoveryManifest.decode([[
{
  "schema_version": "lifter_recovery_manifest_v2",
  "intrinsic_bindings": [
    { "path": "coroutine.wrap", "evidence": { "kind": "frontend_proof", "locator": "fixture:unknown" } }
  ]
}
]], "unknown-intrinsic-manifest")
end)
assert(not acceptedUnknownIntrinsic, "manifest accepted an unknown intrinsic path")

local acceptedEmptyV2 = pcall(function()
	RecoveryManifest.decode([[
{
  "schema_version": "lifter_recovery_manifest_v2"
}
]], "empty-v2-manifest")
end)
assert(not acceptedEmptyV2, "manifest accepted a V2 document without recovery facts")

local acceptedUnknownField = pcall(function()
	RecoveryManifest.decode([[
{
  "schema_version": "lifter_recovery_manifest_v1",
  "program_obligations": [],
  "sample_name": "forbidden"
}
]], "unknown-field-manifest")
end)
assert(not acceptedUnknownField, "manifest accepted a source-specific unknown field")

local acceptedUnknownKind = pcall(function()
	RecoveryManifest.decode([[
{
  "schema_version": "lifter_recovery_manifest_v1",
  "program_obligations": [
    {
      "kind": "sample_placeholder",
      "blocks_profile": "readable_luau",
      "detail": "invalid",
      "evidence": {
        "kind": "decoded_record",
        "locator": "fixture:invalid-kind"
      }
    }
  ]
}
]], "unknown-kind-manifest")
end)
assert(not acceptedUnknownKind, "manifest accepted a non-contract obligation kind")

local recoveryLocal = { type = "AstLocal", name = "unresolved_callee", location = "0,6 - 0,12" }
local recoveryDocument = {
	root = {
		type = "AstStatBlock",
		location = "0,0 - 3,8",
		body = {
			{
				type = "AstStatLocal",
				location = "0,0 - 0,18",
				vars = { recoveryLocal },
				values = { { type = "AstExprGlobal", location = "0,15 - 0,20", global = "error" } },
			},
			{
				type = "AstStatExpr",
				location = "1,0 - 1,8",
				expr = {
					type = "AstExprCall",
					location = "1,0 - 1,8",
					func = {
						type = "AstExprLocal",
						location = "1,0 - 1,6",
						["local"] = recoveryLocal,
					},
					args = {},
					self = false,
				},
			},
			{ type = "AstStatReturn", location = "2,0 - 2,6", list = {} },
			{
				type = "AstStatExpr",
				location = "3,0 - 3,8",
				expr = {
					type = "AstExprCall",
					location = "3,0 - 3,8",
					func = {
						type = "AstExprLocal",
						location = "3,0 - 3,6",
						["local"] = recoveryLocal,
					},
					args = {},
					self = false,
				},
			},
		},
	},
}
local recoveryOptions = {
	program_id = "frontend-target-recovery",
	source_name = "frontend-target-recovery",
	source_text = "abc",
	target_recovery = {
		source_sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
		call_site_count = 2,
		unresolved_call_count = 2,
		lowered_unresolved_call_count = 1,
		unresolved_target_selectors = { { kind = "local_name_prefix", value = "unresolved_" } },
		detail = "callee identity remains unresolved",
		evidence = {
			kind = "structural_derivation",
			locator = "fixture:target-recovery",
			digest = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
		},
	},
}
local recoveredTarget = AstFrontend.tryLift(recoveryDocument, recoveryOptions)
assert(
	recoveredTarget.program ~= nil and #recoveredTarget.diagnostics == 0,
	`verified target recovery did not lift: {if recoveredTarget.diagnostics[1] ~= nil then recoveredTarget.diagnostics[1].code .. ": " .. recoveredTarget.diagnostics[1].detail else "no diagnostic"}`
)
local targetObligations = (recoveredTarget.program :: any).obligations
assert(#targetObligations == 1, "verified unresolved target did not produce exactly one obligation")
assert(targetObligations[1].kind == "unresolved_identity", "target recovery obligation lost its typed kind")
assert(targetObligations[1].subject.instruction ~= nil, "target recovery obligation was not attached to its call instruction")
assert(#targetObligations[1].evidence == 2, "target recovery obligation lost source or frontier evidence")
assert(
	type(targetObligations[1].evidence[1]) == "number" and type(targetObligations[1].evidence[2]) == "number",
	"target recovery obligation evidence is not a flat ID array"
)
assert(
	string.find(LifterIR.encodeJson(recoveredTarget.program), '"kind":"unresolved_identity"', 1, true) ~= nil,
	"target recovery obligation did not cross the JSON boundary"
)
local resolvedRecoveryOptions = table.clone(recoveryOptions)
resolvedRecoveryOptions.program_id = "frontend-target-resolution"
resolvedRecoveryOptions.source_name = "frontend-target-resolution"
resolvedRecoveryOptions.target_recovery = table.clone(recoveryOptions.target_recovery)
resolvedRecoveryOptions.target_recovery.target_resolutions = {
	{
		call_location = "1,0 - 1,8",
		origin = { intrinsic = "error" },
		evidence = {
			kind = "dynamic_fixture",
			locator = "fixture:resolved-error",
			digest = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
		},
	},
}
local resolvedTarget = AstFrontend.tryLift(recoveryDocument, resolvedRecoveryOptions)
assert(
	resolvedTarget.program ~= nil and #resolvedTarget.diagnostics == 0,
	`verified target resolution did not lift: {if resolvedTarget.diagnostics[1] ~= nil then resolvedTarget.diagnostics[1].code .. ": " .. resolvedTarget.diagnostics[1].detail else "no diagnostic"}`
)
assert(#(resolvedTarget.program :: any).obligations == 0, "resolved target retained an identity obligation")
assert(
	string.find(LifterIR.encodeJson(resolvedTarget.program), "target_resolutions", 1, true) == nil,
	"frontend-private target resolution leaked into admitted IR"
)
local proofResolvedOptions: any = table.clone(resolvedRecoveryOptions)
proofResolvedOptions.program_id = "frontend-proof-bound-resolution"
proofResolvedOptions.source_name = "frontend-proof-bound-resolution"
proofResolvedOptions.target_recovery = table.clone(resolvedRecoveryOptions.target_recovery)
proofResolvedOptions.target_recovery.require_independent_proof = true
proofResolvedOptions.target_recovery.target_resolutions = table.clone(resolvedRecoveryOptions.target_recovery.target_resolutions)
proofResolvedOptions.target_recovery.target_resolutions[1] = table.clone(proofResolvedOptions.target_recovery.target_resolutions[1])
local terminatingProofContent = "callee initializer establishes terminating intrinsic identity"
proofResolvedOptions.target_recovery.target_resolutions[1].proof = {
	content = terminatingProofContent,
	evidence = {
		kind = "frontend_proof",
		locator = "fixture:resolved-error-derivation",
		digest = TargetRecovery.targetProofDigest(
			proofResolvedOptions.target_recovery.source_sha256,
			"1,0 - 1,8",
			{ intrinsic = "error" },
			terminatingProofContent
		),
	},
}
local proofResolvedTarget = AstFrontend.tryLift(recoveryDocument, proofResolvedOptions)
assert(
	proofResolvedTarget.program ~= nil and #proofResolvedTarget.diagnostics == 0,
	`proof-bound target resolution did not lift: {if proofResolvedTarget.diagnostics[1] ~= nil then proofResolvedTarget.diagnostics[1].code .. ": " .. proofResolvedTarget.diagnostics[1].detail else "no diagnostic"}`
)
local proofResolvedProgram = proofResolvedTarget.program :: any
local sourceBindingEvidence: number? = nil
local derivationEvidence: number? = nil
for _, item in proofResolvedProgram.evidence do
	if item.locator == "fixture:resolved-error" then
		sourceBindingEvidence = item.id
	elseif item.locator == "fixture:resolved-error-derivation" then
		derivationEvidence = item.id
	end
end
assert(
	sourceBindingEvidence ~= nil and derivationEvidence ~= nil and sourceBindingEvidence ~= derivationEvidence,
	"proof-bound lowering did not admit separate source and derivation evidence records"
)
local foundProofBoundTerminator = false
for _, block in proofResolvedProgram.blocks do
	if table.find(block.evidence, sourceBindingEvidence) and table.find(block.evidence, derivationEvidence) then
		foundProofBoundTerminator = true
	end
end
assert(foundProofBoundTerminator, "terminating recovery did not attach both provenance records to its block")
local encodedProofResolved = LifterIR.encodeJson(proofResolvedProgram)
assert(
	string.find(encodedProofResolved, terminatingProofContent, 1, true) == nil
		and string.find(encodedProofResolved, "require_independent_proof", 1, true) == nil
		and string.find(encodedProofResolved, "proof_evidence", 1, true) == nil,
	"frontend-private proof envelope leaked into admitted IR"
)
local deadResolutionOptions = table.clone(recoveryOptions)
deadResolutionOptions.program_id = "frontend-dead-target-resolution"
deadResolutionOptions.source_name = "frontend-dead-target-resolution"
deadResolutionOptions.target_recovery = table.clone(recoveryOptions.target_recovery)
deadResolutionOptions.target_recovery.target_resolutions = {
	{
		call_location = "3,0 - 3,8",
		origin = { intrinsic = "error" },
		evidence = {
			kind = "dynamic_fixture",
			locator = "fixture:dead-resolved-error",
			digest = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
		},
	},
}
local deadResolution = AstFrontend.tryLift(recoveryDocument, deadResolutionOptions)
assert(
	deadResolution.program == nil and deadResolution.diagnostics[1].code == "target_recovery_dead_resolution",
	"frontend accepted a semantic resolution for a structurally dead call"
)
local unsupportedResolutionOptions = table.clone(resolvedRecoveryOptions)
unsupportedResolutionOptions.program_id = "frontend-unsupported-target-resolution"
unsupportedResolutionOptions.source_name = "frontend-unsupported-target-resolution"
unsupportedResolutionOptions.target_recovery = table.clone(resolvedRecoveryOptions.target_recovery)
unsupportedResolutionOptions.target_recovery.target_resolutions = table.clone(resolvedRecoveryOptions.target_recovery.target_resolutions)
unsupportedResolutionOptions.target_recovery.target_resolutions[1] = table.clone(unsupportedResolutionOptions.target_recovery.target_resolutions[1])
unsupportedResolutionOptions.target_recovery.target_resolutions[1].origin = { intrinsic = "pcall" }
recoveryDocument.root.body[1].values[1].global = "pcall"
local unsupportedResolution = AstFrontend.tryLift(recoveryDocument, unsupportedResolutionOptions)
recoveryDocument.root.body[1].values[1].global = "error"
assert(
	unsupportedResolution.program == nil
		and unsupportedResolution.diagnostics[1].code == "target_recovery_unsupported_intrinsic_shape",
	"frontend accepted a recovered intrinsic that cannot preserve the call shape"
)
local mismatchedRecoveryOptions = table.clone(recoveryOptions)
mismatchedRecoveryOptions.source_text = "abd"
local mismatchedRecovery = AstFrontend.tryLift(recoveryDocument, mismatchedRecoveryOptions)
assert(
	mismatchedRecovery.program == nil and mismatchedRecovery.diagnostics[1].code == "target_recovery_mismatch",
	"frontend admitted target recovery for a different source digest"
)
local wrongLoweredCountOptions = table.clone(recoveryOptions)
wrongLoweredCountOptions.target_recovery = table.clone(recoveryOptions.target_recovery)
wrongLoweredCountOptions.target_recovery.lowered_unresolved_call_count = 2
local wrongLoweredCount = AstFrontend.tryLift(recoveryDocument, wrongLoweredCountOptions)
assert(
	wrongLoweredCount.program == nil and wrongLoweredCount.diagnostics[1].code == "target_recovery_unrepresented",
	"frontend accepted a lowered target count that included a structurally dead call"
)

require("./recovery_admission_test")

local runTargetOriginContractTests = require("./target_origin_contract_test")
runTargetOriginContractTests(targetDocument)

require("./closure_target_recovery_test")

require("./target_result_contract_test")


require("./namecall_target_recovery_test")
require("./access_path_target_recovery_test")
