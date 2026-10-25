--!strict

local serde = require("@lune/serde")
local RecoveryManifestCore = require("./recovery_manifest")
local TargetRecovery = require("./target_recovery")
local AstAdmission = require("./ast_admission")
local AstFrontend = require("./ast_frontend")
local LifterIR = require("./lifter_ir")
local JsonCodec = require("./json_codec")

local RecoveryManifest = {
	decode = function(text: string, manifestName: string)
		return RecoveryManifestCore.fromBytes(text, manifestName, function(bytes: string): any
			return AstAdmission.decodeManifestBytes(bytes, function(marked: string): any
				return serde.decode("json", marked)
			end)
		end)
	end,
}

local function runTargetOriginContractTests(targetDocument: any)
	local recoveryLocal = targetDocument.root.body[1].vars[1]

	local function targetDocumentWithInitializer(expression: any): any
		local linked = table.clone(targetDocument)
		linked.root = table.clone(targetDocument.root)
		linked.root.body = table.clone(targetDocument.root.body)
		linked.root.body[1] = table.clone(targetDocument.root.body[1])
		linked.root.body[1].values = { expression }
		return linked
	end

	local sourceDigest = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
	
	local function recoveryEvidence(locator: string): any
		return {
			kind = "dynamic_fixture",
			locator = locator,
			digest = sourceDigest,
		}
	end
	
	local function recoveryWithOrigin(
		selectorKind: string,
		selectorValue: string,
		callSiteCount: number,
		callLocation: string,
		origin: any
	): any
		local selectors = JsonCodec.newArray()
		table.insert(selectors, { kind = selectorKind, value = selectorValue })
		local resolutions = JsonCodec.newArray()
		table.insert(resolutions, {
			call_location = callLocation,
			origin = origin,
			evidence = recoveryEvidence("fixture:nonintrinsic-origin"),
		})
		return {
			source_sha256 = sourceDigest,
			call_site_count = callSiteCount,
			unresolved_call_count = 1,
			lowered_unresolved_call_count = 1,
			unresolved_target_selectors = selectors,
			target_resolutions = resolutions,
			detail = "callee identity requires an authenticated semantic origin",
			evidence = {
				kind = "structural_derivation",
				locator = "fixture:nonintrinsic-origin-frontier",
				digest = sourceDigest,
			},
		}
	end
	
	local function encodedOriginManifest(schemaVersion: string, origin: any): string
		return LifterIR.encodeJson({
			schema_version = schemaVersion,
			target_recovery = recoveryWithOrigin("global_name", "unresolved", 1, "0,0 - 0,12", origin),
		})
	end
	
	local acceptedV5NonIntrinsicOrigin = pcall(function()
		RecoveryManifest.decode(
			encodedOriginManifest("lifter_recovery_manifest_v5", { environment = "recovered_target" }),
			"v5-nonintrinsic-origin"
		)
	end)
	assert(not acceptedV5NonIntrinsicOrigin, "v5 manifest accepted a non-intrinsic target origin")
	
	local acceptedEmptyV6Origin = pcall(function()
		RecoveryManifest.decode(encodedOriginManifest("lifter_recovery_manifest_v6", {}), "v6-empty-origin")
	end)
	assert(not acceptedEmptyV6Origin, "v6 manifest accepted a resolution without a semantic origin")
	
	local acceptedAmbiguousV6Origin = pcall(function()
		RecoveryManifest.decode(
			encodedOriginManifest("lifter_recovery_manifest_v6", {
				local_value = "0,6 - 0,12",
				environment = "recovered_target",
			}),
			"v6-ambiguous-origin"
		)
	end)
	assert(not acceptedAmbiguousV6Origin, "v6 manifest accepted more than one semantic origin")
	
	local acceptedAbsentLocalOrigin = pcall(
		TargetRecovery.verify,
		targetDocument,
		"abc",
		recoveryWithOrigin("local_name", "unresolved_callee", 2, "0,13 - 0,15", { local_value = "9,0 - 9,6" })
	)
	assert(not acceptedAbsentLocalOrigin, "target recovery accepted an absent local origin")
	
	local acceptedUnlinkedLocalOrigin = pcall(
		TargetRecovery.verify,
		{
			root = {
				type = targetDocument.root.type,
				location = targetDocument.root.location,
				body = { targetDocument.root.body[2], targetDocument.root.body[3] },
			},
		},
		"abc",
		recoveryWithOrigin("local_name", "unresolved_callee", 2, "0,13 - 0,15", { local_value = recoveryLocal.location })
	)
	assert(not acceptedUnlinkedLocalOrigin, "target recovery accepted a same-local origin without a declaration/write proof")
	
	local acceptedNoOpEnvironmentOrigin = pcall(
		TargetRecovery.verify,
		targetDocument,
		"abc",
		recoveryWithOrigin("global_name", "print", 2, "1,0 - 1,7", { environment = "print" })
	)
	assert(not acceptedNoOpEnvironmentOrigin, "target recovery accepted an environment origin that did not change target identity")
	
	local effectfulTargetLocation = "0,0 - 0,24"
	local effectfulTargetDocument = {
		root = {
			type = "AstStatBlock",
			location = effectfulTargetLocation,
			body = {
				{
					type = "AstExprCall",
					location = effectfulTargetLocation,
					func = {
						type = "AstExprIndexName",
						location = "0,0 - 0,18",
						expr = {
							type = "AstExprLocal",
							location = "0,0 - 0,16",
							["local"] = recoveryLocal,
						},
						index = "target",
					},
					args = {},
					self = false,
				},
			},
		},
	}
	local acceptedEffectfulTargetResolution = pcall(
		TargetRecovery.verify,
		effectfulTargetDocument,
		"abc",
		recoveryWithOrigin("local_name", "unresolved_callee", 1, effectfulTargetLocation, { environment = "recovered_target" })
	)
	assert(not acceptedEffectfulTargetResolution, "target recovery erased an effectful callee expression")
	
	local immutableOriginLocal = { type = "AstLocal", name = "immutable_origin", location = "0,6 - 0,22" }
	local mutableOriginLocal = { type = "AstLocal", name = "mutable_origin", location = "1,6 - 1,20" }
	local nestedOriginLocal = { type = "AstLocal", name = "nested_origin", location = "3,24 - 3,37" }
	local holderLocal = { type = "AstLocal", name = "holder", location = "3,6 - 3,12" }
	local unresolvedOriginLocal = { type = "AstLocal", name = "unresolved_origin", location = "4,6 - 4,23" }
	local lateOriginLocal = { type = "AstLocal", name = "late_origin", location = "6,6 - 6,17" }
	local originCallLocation = "5,0 - 5,19"
	
	local function localExpression(localNode: any, location: string): any
		return { type = "AstExprLocal", location = location, ["local"] = localNode }
	end
	
	local function nilDeclaration(localNode: any, location: string): any
		return {
			type = "AstStatLocal",
			location = location,
			vars = { localNode },
			values = { { type = "AstExprConstantNil", location = location } },
		}
	end
	
	local originDocument = {
		root = {
			type = "AstStatBlock",
			location = "0,0 - 7,6",
			body = {
				nilDeclaration(immutableOriginLocal, "0,0 - 0,28"),
				nilDeclaration(mutableOriginLocal, "1,0 - 1,26"),
				{
					type = "AstStatAssign",
					location = "2,0 - 2,20",
					vars = { localExpression(mutableOriginLocal, "2,0 - 2,14") },
					values = { { type = "AstExprConstantNil", location = "2,17 - 2,20" } },
				},
				{
					type = "AstStatLocal",
					location = "3,0 - 3,45",
					vars = { holderLocal },
					values = {
						{
							type = "AstExprFunction",
							location = "3,15 - 3,45",
							args = { nestedOriginLocal },
							vararg = false,
							body = { type = "AstStatBlock", location = "3,39 - 3,45", body = {} },
						},
					},
				},
				nilDeclaration(unresolvedOriginLocal, "4,0 - 4,29"),
				{
					type = "AstStatExpr",
					location = originCallLocation,
					expr = {
						type = "AstExprCall",
						location = originCallLocation,
						func = localExpression(unresolvedOriginLocal, "5,0 - 5,17"),
						args = {},
						self = false,
					},
				},
				nilDeclaration(lateOriginLocal, "6,0 - 6,23"),
				{ type = "AstStatReturn", location = "7,0 - 7,6", list = {} },
			},
		},
	}
	
	local originLocalsByLocation = {
		[immutableOriginLocal.location] = immutableOriginLocal,
		[mutableOriginLocal.location] = mutableOriginLocal,
		[nestedOriginLocal.location] = nestedOriginLocal,
		[lateOriginLocal.location] = lateOriginLocal,
	}
	
	local function rawValueOriginExpression(origin: any, location: string): any
		if origin.local_value ~= nil or origin.local_place ~= nil then
			local declarationLocation = origin.local_value or origin.local_place
			local localNode = originLocalsByLocation[declarationLocation]
			assert(localNode ~= nil, "test origin has no local declaration")
			return localExpression(localNode, location)
		end
		return { type = "AstExprGlobal", location = location, global = origin.environment }
	end
	
	local function rawOriginExpression(origin: any): any
		if origin.table_get == nil then
			return rawValueOriginExpression(origin, "4,26 - 4,42")
		end
		local access = origin.table_get
		local tableExpression = rawValueOriginExpression(access.table, "4,26 - 4,34")
		if type(access.key) == "string" then
			return {
				type = "AstExprIndexName",
				location = "4,26 - 4,45",
				expr = tableExpression,
				index = access.key,
			}
		end
		return {
			type = "AstExprIndexExpr",
			location = "4,26 - 4,45",
			expr = tableExpression,
			index = rawValueOriginExpression(access.key, "4,36 - 4,44"),
		}
	end
	
	local function liftOrigin(origin: any, suffix: string): any
		originDocument.root.body[5].values = { rawOriginExpression(origin) }
		return AstFrontend.tryLift(originDocument, {
			program_id = "frontend-origin-" .. suffix,
			source_name = "frontend-origin-" .. suffix,
			source_text = "abc",
			target_recovery = recoveryWithOrigin("local_name", "unresolved_origin", 1, originCallLocation, origin),
		})
	end
	
	local valueKindMismatch = liftOrigin({ local_value = mutableOriginLocal.location }, "value-kind-mismatch")
	assert(
		valueKindMismatch.program == nil and valueKindMismatch.diagnostics[1].code == "target_recovery_mismatch",
		"frontend accepted a local-value origin backed by a mutable place"
	)
	
	local placeKindMismatch = liftOrigin({ local_place = immutableOriginLocal.location }, "place-kind-mismatch")
	assert(
		placeKindMismatch.program == nil and placeKindMismatch.diagnostics[1].code == "target_recovery_mismatch",
		"frontend accepted a local-place origin backed by an immutable value"
	)
	
	local lateOrigin = liftOrigin({ local_value = lateOriginLocal.location }, "late-origin")
	assert(
		lateOrigin.program == nil and lateOrigin.diagnostics[1].code == "invalid_local_scope",
		"frontend accepted a local origin declared after its recovered call"
	)
	
	local outOfScopeOrigin = liftOrigin({ local_value = nestedOriginLocal.location }, "out-of-scope-origin")
	assert(
		outOfScopeOrigin.program == nil and outOfScopeOrigin.diagnostics[1].code == "invalid_local_owner",
		"frontend accepted a local origin owned by another lexical function"
	)

	local environmentTableOrigin = {
		table_get = {
			table = { environment = "recovered_namespace" },
			key = "dispatch",
		},
	}
	local acceptedV6TableOrigin = pcall(function()
		RecoveryManifest.decode(
			encodedOriginManifest("lifter_recovery_manifest_v6", environmentTableOrigin),
			"v6-table-origin"
		)
	end)
	assert(not acceptedV6TableOrigin, "v6 manifest accepted a v7 table access origin")
	
	local tableOriginManifest = RecoveryManifest.decode(
		encodedOriginManifest("lifter_recovery_manifest_v7", environmentTableOrigin),
		"v7-table-origin"
	)
	local tableOriginRecovery = tableOriginManifest.target_recovery
	local tableOriginResolution = if tableOriginRecovery ~= nil and tableOriginRecovery.target_resolutions ~= nil
		then tableOriginRecovery.target_resolutions[1]
		else nil
	assert(
		tableOriginResolution ~= nil
			and tableOriginResolution.origin.table_get ~= nil
			and tableOriginResolution.origin.table_get.table.environment == "recovered_namespace"
			and tableOriginResolution.origin.table_get.key == "dispatch",
		"v7 manifest lost the normalized table access origin"
	)
	
	local emptyTableKeyManifest = RecoveryManifest.decode(
		encodedOriginManifest("lifter_recovery_manifest_v7", {
			table_get = { table = { environment = "recovered_namespace" }, key = "" },
		}),
		"v7-empty-table-key"
	)
	assert(emptyTableKeyManifest.target_recovery ~= nil, "v7 manifest rejected a valid empty-string table key")
	
	local acceptedNonStringTableKey = pcall(function()
		RecoveryManifest.decode(
			encodedOriginManifest("lifter_recovery_manifest_v7", {
				table_get = { table = { environment = "recovered_namespace" }, key = 7 },
			}),
			"v7-non-string-table-key"
		)
	end)
	assert(not acceptedNonStringTableKey, "v7 manifest accepted a non-string table access key")
	
	local dynamicEnvironmentTableOrigin = {
		table_get = {
			table = { environment = "recovered_namespace" },
			key = { environment = "recovered_key" },
		},
	}
	local acceptedV7DynamicTableKey = pcall(function()
		RecoveryManifest.decode(
			encodedOriginManifest("lifter_recovery_manifest_v7", dynamicEnvironmentTableOrigin),
			"v7-dynamic-table-key"
		)
	end)
	assert(not acceptedV7DynamicTableKey, "v7 manifest accepted a v8 dynamic table key origin")
	
	local dynamicTableOriginManifest = RecoveryManifest.decode(
		encodedOriginManifest("lifter_recovery_manifest_v8", dynamicEnvironmentTableOrigin),
		"v8-dynamic-table-key"
	)
	local dynamicTableRecovery = dynamicTableOriginManifest.target_recovery
	local dynamicTableResolution = if dynamicTableRecovery ~= nil and dynamicTableRecovery.target_resolutions ~= nil
		then dynamicTableRecovery.target_resolutions[1]
		else nil
	assert(
		dynamicTableResolution ~= nil
			and dynamicTableResolution.origin.table_get ~= nil
			and type(dynamicTableResolution.origin.table_get.key) == "table"
			and dynamicTableResolution.origin.table_get.key.environment == "recovered_key",
		"v8 manifest lost the normalized dynamic table key origin"
	)
	
	local dynamicVerified = TargetRecovery.verify(
		targetDocumentWithInitializer({
			type = "AstExprIndexExpr",
			location = "0,15 - 0,48",
			expr = {
				type = "AstExprGlobal",
				location = "0,15 - 0,34",
				global = "recovered_namespace",
			},
			index = {
				type = "AstExprGlobal",
				location = "0,36 - 0,48",
				global = "recovered_key",
			},
		}),
		"abc",
		recoveryWithOrigin("local_name", "unresolved_callee", 2, "0,13 - 0,15", dynamicEnvironmentTableOrigin)
	)
	local dynamicVerifiedSite = dynamicVerified.by_call_location["0,13 - 0,15"]
	assert(
		dynamicVerifiedSite ~= nil
			and dynamicVerifiedSite.resolution ~= nil
			and dynamicVerifiedSite.resolution.origin.kind == "table_get"
			and dynamicVerifiedSite.resolution.origin.key_origin.kind == "environment"
			and dynamicVerifiedSite.resolution.origin.key_origin.name == "recovered_key",
		"target recovery lost the verified dynamic key identity"
	)

	local sourceExpressionLocation = "0,36 - 0,48"
	local sourceExpressionTableOrigin = {
		table_get = {
			table = { environment = "recovered_namespace" },
			key = { source_expression = sourceExpressionLocation },
		},
	}
	local acceptedV15SourceExpressionKey = pcall(function()
		RecoveryManifest.decode(
			encodedOriginManifest("lifter_recovery_manifest_v15", sourceExpressionTableOrigin),
			"v15-source-expression-table-key"
		)
	end)
	assert(not acceptedV15SourceExpressionKey, "v15 manifest accepted a v16 source-expression table key")

	local sourceExpressionManifest = RecoveryManifest.decode(
		encodedOriginManifest("lifter_recovery_manifest_v16", sourceExpressionTableOrigin),
		"v16-source-expression-table-key"
	)
	local sourceExpressionRecovery = sourceExpressionManifest.target_recovery
	assert(
		sourceExpressionRecovery ~= nil
			and sourceExpressionRecovery.target_resolutions ~= nil
			and sourceExpressionRecovery.target_resolutions[1].origin.table_get.key.source_expression
				== sourceExpressionLocation,
		"v16 manifest lost the source-expression table key identity"
	)

	local sourceExpression = {
		type = "AstExprBinary",
		location = sourceExpressionLocation,
		op = "Sub",
		left = { type = "AstExprGlobal", location = "0,36 - 0,44", global = "key_base" },
		right = { type = "AstExprConstantInteger", location = "0,47 - 0,48", value = 1 },
	}
	local sourceExpressionVerified = TargetRecovery.verify(
		targetDocumentWithInitializer({
			type = "AstExprIndexExpr",
			location = "0,15 - 0,49",
			expr = {
				type = "AstExprGlobal",
				location = "0,15 - 0,34",
				global = "recovered_namespace",
			},
			index = sourceExpression,
		}),
		"abc",
		recoveryWithOrigin("local_name", "unresolved_callee", 2, "0,13 - 0,15", sourceExpressionTableOrigin)
	)
	local sourceExpressionSite = sourceExpressionVerified.by_call_location["0,13 - 0,15"]
	assert(
		sourceExpressionSite ~= nil
			and sourceExpressionSite.resolution ~= nil
			and sourceExpressionSite.resolution.origin.kind == "table_get"
			and sourceExpressionSite.resolution.origin.key_origin.kind == "source_expression"
			and sourceExpressionSite.resolution.origin.key_origin.expression == sourceExpression,
		"target recovery did not bind the exact source key expression"
	)

	local acceptedAbsentSourceExpression = pcall(
		TargetRecovery.verify,
		targetDocumentWithInitializer({
			type = "AstExprIndexExpr",
			location = "0,15 - 0,49",
			expr = { type = "AstExprGlobal", location = "0,15 - 0,34", global = "recovered_namespace" },
			index = sourceExpression,
		}),
		"abc",
		recoveryWithOrigin("local_name", "unresolved_callee", 2, "0,13 - 0,15", {
			table_get = {
				table = { environment = "recovered_namespace" },
				key = { source_expression = "9,0 - 9,8" },
			},
		})
	)
	assert(not acceptedAbsentSourceExpression, "target recovery accepted an absent source key expression")

	local ambiguousSourceExpression = table.clone(sourceExpression)
	ambiguousSourceExpression.left = {
		type = "AstExprGlobal",
		location = sourceExpressionLocation,
		global = "ambiguous_key_base",
	}
	local acceptedAmbiguousSourceExpression = pcall(
		TargetRecovery.verify,
		targetDocumentWithInitializer({
			type = "AstExprIndexExpr",
			location = "0,15 - 0,49",
			expr = { type = "AstExprGlobal", location = "0,15 - 0,34", global = "recovered_namespace" },
			index = ambiguousSourceExpression,
		}),
		"abc",
		recoveryWithOrigin("local_name", "unresolved_callee", 2, "0,13 - 0,15", sourceExpressionTableOrigin)
	)
	assert(not acceptedAmbiguousSourceExpression, "target recovery accepted an ambiguous source key expression")

	local firstSourceExpressionDigest = TargetRecovery.targetProofDigest(
		sourceDigest,
		"0,13 - 0,15",
		sourceExpressionTableOrigin,
		"source expression proof"
	)
	local secondSourceExpressionDigest = TargetRecovery.targetProofDigest(
		sourceDigest,
		"0,13 - 0,15",
		{
			table_get = {
				table = { environment = "recovered_namespace" },
				key = { source_expression = "0,36 - 0,49" },
			},
		},
		"source expression proof"
	)
	assert(firstSourceExpressionDigest ~= secondSourceExpressionDigest, "target proof omitted the source key expression")
	
	local acceptedV8NumericTableKey = pcall(function()
		RecoveryManifest.decode(
			encodedOriginManifest("lifter_recovery_manifest_v8", {
				table_get = { table = { environment = "recovered_namespace" }, key = 7 },
			}),
			"v8-numeric-table-key"
		)
	end)
	assert(not acceptedV8NumericTableKey, "v8 manifest accepted an unauthenticated numeric table key")
	
	local acceptedAmbiguousDynamicTableKey = pcall(function()
		RecoveryManifest.decode(
			encodedOriginManifest("lifter_recovery_manifest_v8", {
				table_get = {
					table = { environment = "recovered_namespace" },
					key = { local_value = "0,6 - 0,12", environment = "recovered_key" },
				},
			}),
			"v8-ambiguous-table-key"
		)
	end)
	assert(not acceptedAmbiguousDynamicTableKey, "v8 manifest accepted an ambiguous dynamic table key origin")
	
	local acceptedIntrinsicDynamicTableKey = pcall(function()
		RecoveryManifest.decode(
			encodedOriginManifest("lifter_recovery_manifest_v8", {
				table_get = { table = { environment = "recovered_namespace" }, key = { intrinsic = "pcall" } },
			}),
			"v8-intrinsic-table-key"
		)
	end)
	assert(not acceptedIntrinsicDynamicTableKey, "v8 manifest accepted an intrinsic as a dynamic table key")
	
	local acceptedMissingTableRoot = pcall(function()
		RecoveryManifest.decode(
			encodedOriginManifest("lifter_recovery_manifest_v7", {
				table_get = { key = "dispatch" },
			}),
			"v7-missing-table-root"
		)
	end)
	assert(not acceptedMissingTableRoot, "v7 manifest accepted a table access without a root")
	
	local acceptedIntrinsicTableRoot = pcall(function()
		RecoveryManifest.decode(
			encodedOriginManifest("lifter_recovery_manifest_v7", {
				table_get = { table = { intrinsic = "pcall" }, key = "dispatch" },
			}),
			"v7-intrinsic-table-root"
		)
	end)
	assert(not acceptedIntrinsicTableRoot, "v7 manifest accepted an intrinsic as a table root")
	
	local acceptedAbsentTableRoot = pcall(
		TargetRecovery.verify,
		targetDocument,
		"abc",
		recoveryWithOrigin("local_name", "unresolved_callee", 2, "0,13 - 0,15", {
			table_get = { table = { local_value = "9,0 - 9,6" }, key = "dispatch" },
		})
	)
	assert(not acceptedAbsentTableRoot, "target recovery accepted an absent local table root")
	
	local acceptedAbsentTableKey = pcall(
		TargetRecovery.verify,
		targetDocument,
		"abc",
		recoveryWithOrigin("local_name", "unresolved_callee", 2, "0,13 - 0,15", {
			table_get = {
				table = { environment = "recovered_namespace" },
				key = { local_value = "9,0 - 9,6" },
			},
		})
	)
	assert(not acceptedAbsentTableKey, "target recovery accepted an absent local dynamic table key")
	
	local acceptedEffectfulTableTarget = pcall(
		TargetRecovery.verify,
		effectfulTargetDocument,
		"abc",
		recoveryWithOrigin("local_name", "unresolved_callee", 1, effectfulTargetLocation, environmentTableOrigin)
	)
	assert(not acceptedEffectfulTableTarget, "table-origin recovery erased an effectful callee expression")
	
	local methodTargetDocument = table.clone(targetDocument)
	methodTargetDocument.root = table.clone(targetDocument.root)
	methodTargetDocument.root.body = table.clone(targetDocument.root.body)
	methodTargetDocument.root.body[2] = table.clone(targetDocument.root.body[2])
	methodTargetDocument.root.body[2].self = true
	local acceptedTableMethodTarget = pcall(
		TargetRecovery.verify,
		methodTargetDocument,
		"abc",
		recoveryWithOrigin("local_name", "unresolved_callee", 2, "0,13 - 0,15", environmentTableOrigin)
	)
	assert(not acceptedTableMethodTarget, "table-origin recovery accepted a method call without receiver semantics")
	
	local tableValueKindMismatch = liftOrigin({
		table_get = { table = { local_value = mutableOriginLocal.location }, key = "dispatch" },
	}, "table-value-kind-mismatch")
	assert(
		tableValueKindMismatch.program == nil
			and tableValueKindMismatch.diagnostics[1].code == "target_recovery_mismatch",
		"frontend accepted a table local-value root backed by a mutable place"
	)
	
	local tablePlaceKindMismatch = liftOrigin({
		table_get = { table = { local_place = immutableOriginLocal.location }, key = "dispatch" },
	}, "table-place-kind-mismatch")
	assert(
		tablePlaceKindMismatch.program == nil
			and tablePlaceKindMismatch.diagnostics[1].code == "target_recovery_mismatch",
		"frontend accepted a table local-place root backed by an immutable value"
	)
	
	local lateTableRoot = liftOrigin({
		table_get = { table = { local_value = lateOriginLocal.location }, key = "dispatch" },
	}, "late-table-root")
	assert(
		lateTableRoot.program == nil and lateTableRoot.diagnostics[1].code == "invalid_local_scope",
		"frontend accepted a table root declared after its recovered call"
	)
	
	local tableKeyValueKindMismatch = liftOrigin({
		table_get = {
			table = { environment = "recovered_namespace" },
			key = { local_value = mutableOriginLocal.location },
		},
	}, "table-key-value-kind-mismatch")
	assert(
		tableKeyValueKindMismatch.program == nil
			and tableKeyValueKindMismatch.diagnostics[1].code == "target_recovery_mismatch",
		"frontend accepted a dynamic local-value key backed by a mutable place"
	)
	
	local tableKeyPlaceKindMismatch = liftOrigin({
		table_get = {
			table = { environment = "recovered_namespace" },
			key = { local_place = immutableOriginLocal.location },
		},
	}, "table-key-place-kind-mismatch")
	assert(
		tableKeyPlaceKindMismatch.program == nil
			and tableKeyPlaceKindMismatch.diagnostics[1].code == "target_recovery_mismatch",
		"frontend accepted a dynamic local-place key backed by an immutable value"
	)
	
	local lateTableKey = liftOrigin({
		table_get = {
			table = { environment = "recovered_namespace" },
			key = { local_value = lateOriginLocal.location },
		},
	}, "late-table-key")
	assert(
		lateTableKey.program == nil and lateTableKey.diagnostics[1].code == "invalid_local_scope",
		"frontend accepted a dynamic table key declared after its recovered call"
	)
	
	local outOfScopeTableKey = liftOrigin({
		table_get = {
			table = { environment = "recovered_namespace" },
			key = { local_value = nestedOriginLocal.location },
		},
	}, "out-of-scope-table-key")
	assert(
		outOfScopeTableKey.program == nil and outOfScopeTableKey.diagnostics[1].code == "invalid_local_owner",
		"frontend accepted a dynamic table key owned by another lexical function"
	)
end

return runTargetOriginContractTests
