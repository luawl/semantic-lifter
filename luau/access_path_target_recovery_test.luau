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

local sourceText = "abc"
local sourceDigest = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
local ordinaryCallLocation = "7,0 - 7,18"
local methodCallLocation = "7,0 - 7,27"

local immutableRoot = { type = "AstLocal", name = "immutable_root", location = "0,6 - 0,20" }
local mutableRoot = { type = "AstLocal", name = "mutable_root", location = "1,6 - 1,18" }
local immutableKey = { type = "AstLocal", name = "immutable_key", location = "3,6 - 3,19" }
local mutableKey = { type = "AstLocal", name = "mutable_key", location = "4,6 - 4,17" }
local unresolvedTarget = { type = "AstLocal", name = "unresolved_target", location = "6,6 - 6,23" }
local lateKey = { type = "AstLocal", name = "late_key", location = "8,6 - 8,14" }

local function localExpression(localNode: any, location: string): any
	return { type = "AstExprLocal", location = location, ["local"] = localNode }
end

local function localDeclaration(localNode: any, location: string, value: any?): any
	return {
		type = "AstStatLocal",
		location = location,
		vars = { localNode },
		values = { value or { type = "AstExprConstantNil", location = location } },
	}
end

local function makeCall(selfCall: boolean): any
	local targetExpression = localExpression(unresolvedTarget, "7,0 - 7,17")
	return {
		type = "AstExprCall",
		location = if selfCall then methodCallLocation else ordinaryCallLocation,
		func = if selfCall
			then {
				type = "AstExprIndexName",
				location = "7,0 - 7,25",
				expr = targetExpression,
				index = "dispatch",
			}
			else targetExpression,
		args = {},
		self = selfCall,
	}
end

local function makeDocument(selfCall: boolean, callOverride: any?, targetValue: any?): any
	local call = callOverride or makeCall(selfCall)
	return {
		root = {
			type = "AstStatBlock",
			location = "0,0 - 9,6",
			body = {
				localDeclaration(immutableRoot, "0,0 - 0,26", nil),
				localDeclaration(mutableRoot, "1,0 - 1,24", nil),
				{
					type = "AstStatAssign",
					location = "2,0 - 2,18",
					vars = { localExpression(mutableRoot, "2,0 - 2,12") },
					values = { { type = "AstExprConstantNil", location = "2,15 - 2,18" } },
				},
				localDeclaration(immutableKey, "3,0 - 3,25", nil),
				localDeclaration(mutableKey, "4,0 - 4,23", nil),
				{
					type = "AstStatAssign",
					location = "5,0 - 5,17",
					vars = { localExpression(mutableKey, "5,0 - 5,11") },
					values = { { type = "AstExprConstantNil", location = "5,14 - 5,17" } },
				},
				localDeclaration(unresolvedTarget, "6,0 - 6,29", targetValue),
				{ type = "AstStatExpr", location = call.location, expr = call },
				localDeclaration(lateKey, "8,0 - 8,20", nil),
				{ type = "AstStatReturn", location = "9,0 - 9,6", list = {} },
			},
		},
	}
end

local function keys(...: any): { any }
	local result = JsonCodec.newArray()
	for index = 1, select("#", ...) do
		table.insert(result, (select(index, ...)))
	end
	return result
end

local function path(root: any, pathKeys: { any }): any
	return { access_path = { root = root, keys = pathKeys } }
end

local declarationsByLocation = {
	[immutableRoot.location] = immutableRoot,
	[mutableRoot.location] = mutableRoot,
	[immutableKey.location] = immutableKey,
	[mutableKey.location] = mutableKey,
	[unresolvedTarget.location] = unresolvedTarget,
	[lateKey.location] = lateKey,
}

local function valueOriginExpression(origin: any, location: string): any
	if origin.local_value ~= nil or origin.local_place ~= nil then
		local declarationLocation = origin.local_value or origin.local_place
		local localNode = declarationsByLocation[declarationLocation]
		assert(localNode ~= nil, "test origin has no local declaration")
		return localExpression(localNode, location)
	end
	return { type = "AstExprGlobal", location = location, global = origin.environment }
end

local function accessPathExpression(origin: any): any
	local pathValue = origin.access_path
	local expression = valueOriginExpression(pathValue.root, "6,32 - 6,40")
	for index, key in pathValue.keys do
		if type(key) == "string" then
			expression = {
				type = "AstExprIndexName",
				location = `6,32 - 6,{40 + index}`,
				expr = expression,
				index = key,
			}
		else
			local keyExpression
			if key.literal ~= nil and key.literal.boolean ~= nil then
				keyExpression = {
					type = "AstExprConstantBool",
					location = `6,{40 + index} - 6,{41 + index}`,
					value = key.literal.boolean,
				}
			elseif key.literal ~= nil and key.literal.number ~= nil then
				keyExpression = {
					type = "AstExprConstantNumber",
					location = `6,{40 + index} - 6,{41 + index}`,
					value = key.literal.number,
				}
			else
				keyExpression = valueOriginExpression(key, `6,{40 + index} - 6,{41 + index}`)
			end
			expression = {
				type = "AstExprIndexExpr",
				location = `6,32 - 6,{40 + index}`,
				expr = expression,
				index = keyExpression,
			}
		end
	end
	return expression
end

local function targetExpression(origin: any): any
	if origin.namecall ~= nil then
		return accessPathExpression(origin.namecall.receiver)
	end
	return accessPathExpression(origin)
end

local function recoveryWithOrigin(callLocation: string, origin: any): any
	local selectors = JsonCodec.newArray()
	table.insert(selectors, { kind = "local_name", value = "unresolved_target" })
	local resolutions = JsonCodec.newArray()
	table.insert(resolutions, {
		call_location = callLocation,
		origin = origin,
		evidence = { kind = "dynamic_fixture", locator = "fixture:access-path", digest = sourceDigest },
	})
	return {
		source_sha256 = sourceDigest,
		call_site_count = 1,
		unresolved_call_count = 1,
		lowered_unresolved_call_count = 1,
		unresolved_target_selectors = selectors,
		target_resolutions = resolutions,
		detail = "callee identity requires an authenticated access path",
		evidence = {
			kind = "structural_derivation",
			locator = "fixture:access-path-frontier",
			digest = sourceDigest,
		},
	}
end

local function encodedManifest(version: string, callLocation: string, origin: any): string
	return LifterIR.encodeJson({ schema_version = version, target_recovery = recoveryWithOrigin(callLocation, origin) })
end

local immutablePath = path(
	{ local_value = immutableRoot.location },
	keys("namespace", { local_value = immutableKey.location })
)
local acceptedV9Path = pcall(function()
	RecoveryManifest.decode(encodedManifest("lifter_recovery_manifest_v9", ordinaryCallLocation, immutablePath), "v9-access-path")
end)
assert(not acceptedV9Path, "v9 manifest accepted a v10 access path")

local manifest = RecoveryManifest.decode(
	encodedManifest("lifter_recovery_manifest_v10", ordinaryCallLocation, immutablePath),
	"v10-access-path"
)
local manifestRecovery = manifest.target_recovery
local manifestResolution = if manifestRecovery ~= nil and manifestRecovery.target_resolutions ~= nil
	then manifestRecovery.target_resolutions[1]
	else nil
assert(
	manifestResolution ~= nil
		and manifestResolution.origin.access_path ~= nil
		and #manifestResolution.origin.access_path.keys == 2,
	"v10 manifest lost the normalized access path"
)

local function rejectsManifest(origin: any, label: string): boolean
	return not pcall(function()
		RecoveryManifest.decode(encodedManifest("lifter_recovery_manifest_v10", ordinaryCallLocation, origin), label)
	end)
end

local function rejectsManifestVersion(version: string, origin: any, label: string): boolean
	return not pcall(function()
		RecoveryManifest.decode(encodedManifest(version, ordinaryCallLocation, origin), label)
	end)
end

assert(rejectsManifest(path({ environment = "root" }, keys()), "v10-empty-path"), "v10 accepted an empty access path")
assert(rejectsManifest({ access_path = { keys = keys("field") } }, "v10-missing-root"), "v10 accepted an access path without a root")
assert(rejectsManifest({ access_path = { root = { environment = "root" } } }, "v10-missing-keys"), "v10 accepted an access path without keys")
assert(rejectsManifest(path({ intrinsic = "pcall" }, keys("field")), "v10-intrinsic-root"), "v10 accepted an intrinsic path root")
assert(rejectsManifest(path({ environment = "root" }, keys(7)), "v10-numeric-key"), "v10 accepted an unauthenticated numeric path key")
local literalPath = path(
	{ environment = "root" },
	keys({ literal = { number = 7 } }, { literal = { boolean = false } })
)
assert(
	rejectsManifestVersion("lifter_recovery_manifest_v10", literalPath, "v10-literal-path"),
	"v10 manifest accepted a v11 literal path key"
)
local literalManifest = RecoveryManifest.decode(
	encodedManifest("lifter_recovery_manifest_v11", ordinaryCallLocation, literalPath),
	"v11-literal-path"
)
local literalManifestRecovery = literalManifest.target_recovery
local literalManifestResolution = if literalManifestRecovery ~= nil and literalManifestRecovery.target_resolutions ~= nil
	then literalManifestRecovery.target_resolutions[1]
	else nil
local literalManifestPath = if literalManifestResolution ~= nil then literalManifestResolution.origin.access_path else nil
assert(
	literalManifestPath ~= nil
		and type(literalManifestPath.keys[1]) == "table"
		and (literalManifestPath.keys[1] :: any).literal.number == 7
		and type(literalManifestPath.keys[2]) == "table"
		and (literalManifestPath.keys[2] :: any).literal.boolean == false,
	"v11 manifest lost a normalized number or Boolean literal path key"
)
assert(
	rejectsManifestVersion("lifter_recovery_manifest_v11", path({ environment = "root" }, keys(7)), "v11-raw-number"),
	"v11 manifest accepted an untagged numeric path key"
)
assert(
	rejectsManifestVersion(
		"lifter_recovery_manifest_v11",
		path({ environment = "root" }, keys({ literal = { number = 7, boolean = true } })),
		"v11-ambiguous-literal"
	),
	"v11 manifest accepted an ambiguous literal path key"
)
assert(
	rejectsManifestVersion(
		"lifter_recovery_manifest_v11",
		path({ environment = "root" }, keys({ literal = { boolean = "false" } })),
		"v11-malformed-boolean"
	),
	"v11 manifest accepted a malformed Boolean literal path key"
)
local excessiveKeys = JsonCodec.newArray()
for index = 1, TargetRecovery.maxAccessPathKeys + 1 do
	table.insert(excessiveKeys, `field_{index}`)
end
assert(rejectsManifest(path({ environment = "root" }, excessiveKeys), "v10-excessive-path"), "v10 accepted an excessive access path")

local document = makeDocument(false, nil, targetExpression(immutablePath))
local verified = TargetRecovery.verify(document, sourceText, manifestRecovery :: any)
local verifiedSite = verified.by_call_location[ordinaryCallLocation]
assert(
	verifiedSite ~= nil
		and verifiedSite.resolution ~= nil
		and verifiedSite.resolution.origin.kind == "access_path"
		and #verifiedSite.resolution.origin.key_origins == 2,
	"target recovery lost the verified access path"
)

local function lift(selfCall: boolean, callLocation: string, origin: any, suffix: string): any
	return AstFrontend.tryLift(makeDocument(selfCall, nil, targetExpression(origin)), {
		program_id = "frontend-access-path-" .. suffix,
		source_name = "frontend-access-path-" .. suffix,
		source_text = sourceText,
		target_recovery = recoveryWithOrigin(callLocation, origin),
	})
end

local ordinaryLift = lift(false, ordinaryCallLocation, immutablePath, "ordinary")
assert(ordinaryLift.program ~= nil and #ordinaryLift.diagnostics == 0, "frontend rejected a verified access-path callee")
local tableGetCount = 0
local callCount = 0
for _, instruction in (ordinaryLift.program :: any).instructions do
	if instruction.operation.table_get ~= nil then
		tableGetCount += 1
	elseif instruction.operation.call ~= nil then
		callCount += 1
	end
end
assert(tableGetCount == 2 and callCount == 1, "frontend did not lower each path lookup exactly once before the call")

local literalDocument = makeDocument(false, nil, targetExpression(literalPath))
local literalVerified = TargetRecovery.verify(literalDocument, sourceText, literalManifestRecovery :: any)
local literalVerifiedSite = literalVerified.by_call_location[ordinaryCallLocation]
local literalVerifiedPath = if literalVerifiedSite ~= nil and literalVerifiedSite.resolution ~= nil
	then literalVerifiedSite.resolution.origin
	else nil
assert(
	literalVerifiedPath ~= nil
		and literalVerifiedPath.kind == "access_path"
		and literalVerifiedPath.key_origins[1].kind == "constant_number"
		and literalVerifiedPath.key_origins[2].kind == "constant_boolean",
	"target recovery lost the verified literal-key identities"
)
local literalLift = lift(false, ordinaryCallLocation, literalPath, "literal")
assert(literalLift.program ~= nil and #literalLift.diagnostics == 0, "frontend rejected a verified literal access path")
local literalKinds = {}
for _, instruction in (literalLift.program :: any).instructions do
	if instruction.operation.constant ~= nil then
		if instruction.operation.constant.number ~= nil then
			table.insert(literalKinds, "number")
		elseif instruction.operation.constant.integer ~= nil then
			table.insert(literalKinds, "integer")
		elseif instruction.operation.constant.boolean ~= nil then
			table.insert(literalKinds, "boolean")
		end
	end
end
assert(table.concat(literalKinds, ",") == "integer,boolean", "frontend did not preserve literal path key domains")

local literalMismatch = AstFrontend.tryLift(literalDocument, {
	program_id = "frontend-access-path-literal-mismatch",
	source_name = "frontend-access-path-literal-mismatch",
	source_text = sourceText,
	target_recovery = recoveryWithOrigin(
		ordinaryCallLocation,
		path({ environment = "root" }, keys({ literal = { number = 8 } }, { literal = { boolean = false } }))
	),
})
assert(
	literalMismatch.program == nil and literalMismatch.diagnostics[1].code == "target_recovery_mismatch",
	"frontend accepted a mismatched numeric literal path key"
)

local mutablePath = path(
	{ local_place = mutableRoot.location },
	keys("namespace", { local_place = mutableKey.location })
)
local mutableLift = lift(false, ordinaryCallLocation, mutablePath, "mutable")
assert(mutableLift.program ~= nil and #mutableLift.diagnostics == 0, "frontend rejected a mutable access path")
local recoveryOperations = {}
local placeReadCount = 0
for _, instruction in (mutableLift.program :: any).instructions do
	if instruction.operation.place_read ~= nil then
		placeReadCount += 1
	end
	for _, evidenceId in instruction.evidence do
		local item = (mutableLift.program :: any).evidence[evidenceId + 1]
		if item.locator == "fixture:access-path" then
			table.insert(recoveryOperations, (instruction.operation :: any).place_read and "place_read"
				or (instruction.operation :: any).constant and "constant"
				or (instruction.operation :: any).table_get and "table_get"
				or (instruction.operation :: any).call and "call"
				or "other")
			break
		end
	end
end
assert(
	table.concat(recoveryOperations, ",") == "call" and placeReadCount == 2,
	"frontend replayed the mutable root/key path instead of using its selected snapshot"
)

local namecallPath = {
	namecall = {
		receiver = immutablePath,
		method = "dispatch",
	},
}
local acceptedV9NamecallPath = pcall(function()
	RecoveryManifest.decode(
		encodedManifest("lifter_recovery_manifest_v9", methodCallLocation, namecallPath),
		"v9-namecall-access-path"
	)
end)
assert(not acceptedV9NamecallPath, "v9 manifest accepted a v10 namecall receiver path")
local namecallLift = lift(true, methodCallLocation, namecallPath, "namecall")
assert(namecallLift.program ~= nil and #namecallLift.diagnostics == 0, "frontend rejected a namecall receiver path")
local namecallCount = 0
for _, instruction in (namecallLift.program :: any).instructions do
	if instruction.operation.namecall ~= nil then
		namecallCount += 1
	end
end
assert(namecallCount == 1, "frontend did not lower a path receiver into one namecall")

local rootKindMismatch = lift(
	false,
	ordinaryCallLocation,
	path({ local_value = mutableRoot.location }, keys("field")),
	"root-kind-mismatch"
)
assert(
	rootKindMismatch.program == nil and rootKindMismatch.diagnostics[1].code == "target_recovery_mismatch",
	"frontend accepted an access-path value root backed by a mutable place"
)
local keyKindMismatch = lift(
	false,
	ordinaryCallLocation,
	path({ environment = "root" }, keys({ local_place = immutableKey.location })),
	"key-kind-mismatch"
)
assert(
	keyKindMismatch.program == nil and keyKindMismatch.diagnostics[1].code == "target_recovery_mismatch",
	"frontend accepted an access-path place key backed by an immutable value"
)
local latePath = lift(
	false,
	ordinaryCallLocation,
	path({ environment = "root" }, keys({ local_value = lateKey.location })),
	"late-key"
)
assert(
	latePath.program == nil and latePath.diagnostics[1].code == "invalid_local_scope",
	"frontend accepted an access-path key declared after its call"
)

local directPath = path(
	{ local_value = unresolvedTarget.location },
	keys({ literal = { number = 7 } }, { literal = { boolean = false } })
)
local directCall = {
	type = "AstExprCall",
	location = "7,0 - 7,38",
	func = targetExpression(directPath),
	args = {},
	self = false,
}
local directDocument = makeDocument(false, directCall, nil)
local v11DirectManifest = RecoveryManifest.decode(
	encodedManifest("lifter_recovery_manifest_v11", directCall.location, directPath),
	"v11-direct-access-path"
)
local v11DirectRecovery = v11DirectManifest.target_recovery
assert(v11DirectRecovery ~= nil and not v11DirectRecovery.allow_direct_target_expressions, "v11 gained direct-target capability")
assert(
	not pcall(TargetRecovery.verify, directDocument, sourceText, v11DirectRecovery :: any),
	"v11 authenticated a direct access-path callee"
)

local directManifest = RecoveryManifest.decode(
	encodedManifest("lifter_recovery_manifest_v12", directCall.location, directPath),
	"v12-direct-access-path"
)
local directRecovery = directManifest.target_recovery
assert(directRecovery ~= nil and directRecovery.allow_direct_target_expressions, "v12 lost direct-target capability")
local directVerified = TargetRecovery.verify(directDocument, sourceText, directRecovery :: any)
local directSite = directVerified.by_call_location[directCall.location]
assert(
	directSite ~= nil and directSite.resolution ~= nil and directSite.resolution.preserve_source_target,
	"v12 did not preserve an authenticated direct access-path callee"
)

local function recoveryOperationKinds(program: any): string
	local kinds = {}
	for _, instruction in program.instructions do
		for _, evidenceId in instruction.evidence do
			local evidence = program.evidence[evidenceId + 1]
			if evidence.locator == "fixture:access-path" then
				local operation = instruction.operation
				table.insert(kinds, operation.call and "call" or operation.namecall and "namecall" or "other")
				break
			end
		end
	end
	return table.concat(kinds, ",")
end

local directLift = AstFrontend.tryLift(directDocument, {
	program_id = "frontend-access-path-direct",
	source_name = "frontend-access-path-direct",
	source_text = sourceText,
	target_recovery = directRecovery,
})
assert(directLift.program ~= nil and #directLift.diagnostics == 0, "frontend rejected a direct access-path callee")
local directTableGetCount = 0
for _, instruction in (directLift.program :: any).instructions do
	if instruction.operation.table_get ~= nil then
		directTableGetCount += 1
	end
end
assert(
	directTableGetCount == 2 and recoveryOperationKinds(directLift.program) == "call",
	"frontend replayed a direct callee path or misplaced its recovery evidence"
)

local directTableOrigin = {
	table_get = {
		table = { local_value = unresolvedTarget.location },
		key = { literal = { number = 7 } },
	},
}
local directTableCall = {
	type = "AstExprCall",
	location = "7,0 - 7,29",
	func = {
		type = "AstExprIndexExpr",
		location = "7,0 - 7,20",
		expr = localExpression(unresolvedTarget, "7,0 - 7,17"),
		index = { type = "AstExprConstantNumber", location = "7,18 - 7,19", value = 7 },
	},
	args = {},
	self = false,
}
local directTableDocument = makeDocument(false, directTableCall, nil)
local directTableRecovery = RecoveryManifest.decode(
	encodedManifest("lifter_recovery_manifest_v12", directTableCall.location, directTableOrigin),
	"v12-direct-table-get"
).target_recovery
local directTableVerified = TargetRecovery.verify(directTableDocument, sourceText, directTableRecovery :: any)
local directTableSite = directTableVerified.by_call_location[directTableCall.location]
assert(
	directTableSite ~= nil and directTableSite.resolution ~= nil and directTableSite.resolution.preserve_source_target,
	"v12 rejected an authenticated direct table-get callee"
)

local directNamecallOrigin = {
	namecall = {
		receiver = directPath,
		method = "dispatch",
	},
}
local directNamecall = {
	type = "AstExprCall",
	location = "7,0 - 7,47",
	func = {
		type = "AstExprIndexName",
		location = "7,0 - 7,38",
		expr = targetExpression(directNamecallOrigin),
		index = "dispatch",
	},
	args = {},
	self = true,
}
local directNamecallDocument = makeDocument(true, directNamecall, nil)
local directNamecallRecovery = RecoveryManifest.decode(
	encodedManifest("lifter_recovery_manifest_v12", directNamecall.location, directNamecallOrigin),
	"v12-direct-namecall"
).target_recovery
local directNamecallVerified = TargetRecovery.verify(directNamecallDocument, sourceText, directNamecallRecovery :: any)
local directNamecallSite = directNamecallVerified.by_call_location[directNamecall.location]
assert(
	directNamecallSite ~= nil and directNamecallSite.resolution ~= nil and directNamecallSite.resolution.preserve_source_target,
	"v12 did not preserve an authenticated direct namecall receiver"
)
local directNamecallLift = AstFrontend.tryLift(directNamecallDocument, {
	program_id = "frontend-access-path-direct-namecall",
	source_name = "frontend-access-path-direct-namecall",
	source_text = sourceText,
	target_recovery = directNamecallRecovery,
})
assert(
	directNamecallLift.program ~= nil and #directNamecallLift.diagnostics == 0,
	"frontend rejected a direct access-path namecall receiver"
)
assert(
	recoveryOperationKinds(directNamecallLift.program) == "namecall",
	"frontend replayed a direct namecall receiver or misplaced its recovery evidence"
)

local mismatchedDirectPath = path(
	{ local_value = unresolvedTarget.location },
	keys({ literal = { number = 8 } }, { literal = { boolean = false } })
)
local mismatchedDirectRecovery = RecoveryManifest.decode(
	encodedManifest("lifter_recovery_manifest_v12", directCall.location, mismatchedDirectPath),
	"v12-mismatched-direct-access-path"
).target_recovery
assert(
	not pcall(TargetRecovery.verify, directDocument, sourceText, mismatchedDirectRecovery :: any),
	"v12 authenticated a mismatched direct access-path callee"
)
local mismatchedDirectLift = AstFrontend.tryLift(directDocument, {
	program_id = "frontend-access-path-direct-mismatch",
	source_name = "frontend-access-path-direct-mismatch",
	source_text = sourceText,
	target_recovery = mismatchedDirectRecovery,
})
assert(
	mismatchedDirectLift.program == nil and mismatchedDirectLift.diagnostics[1].code == "target_recovery_mismatch",
	"frontend did not report a typed direct access-path mismatch"
)

local malformedCapability = table.clone(directRecovery :: any)
malformedCapability.allow_direct_target_expressions = "yes"
assert(
	not pcall(TargetRecovery.verify, directDocument, sourceText, malformedCapability),
	"target recovery accepted malformed direct-target capability metadata"
)

local effectfulKeyCall = {
	type = "AstExprCall",
	location = "7,18 - 7,30",
	func = { type = "AstExprGlobal", location = "7,18 - 7,28", global = "read_key" },
	args = {},
	self = false,
}
local effectfulDirectCall = {
	type = "AstExprCall",
	location = "7,0 - 7,33",
	func = {
		type = "AstExprIndexExpr",
		location = "7,0 - 7,30",
		expr = localExpression(unresolvedTarget, "7,0 - 7,17"),
		index = effectfulKeyCall,
	},
	args = {},
	self = false,
}
local effectfulDirectDocument = makeDocument(false, effectfulDirectCall, nil)
local effectfulDirectRecovery = RecoveryManifest.decode(
	encodedManifest("lifter_recovery_manifest_v12", effectfulDirectCall.location, {
		table_get = {
			table = { local_value = unresolvedTarget.location },
			key = { environment = "read_key" },
		},
	}),
	"v12-effectful-direct-key"
).target_recovery :: any
effectfulDirectRecovery.call_site_count = 2
assert(
	not pcall(TargetRecovery.verify, effectfulDirectDocument, sourceText, effectfulDirectRecovery),
	"v12 authenticated a direct table access with an effectful key"
)

return true
