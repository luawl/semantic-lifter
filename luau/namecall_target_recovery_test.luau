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

local sourceText = "abc"
local sourceDigest = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
local callLocation = "4,0 - 4,30"

local immutableReceiver = { type = "AstLocal", name = "immutable_receiver", location = "0,6 - 0,24" }
local mutableReceiver = { type = "AstLocal", name = "mutable_receiver", location = "1,6 - 1,22" }
local unresolvedReceiver = { type = "AstLocal", name = "unresolved_receiver", location = "3,6 - 3,25" }
local lateReceiver = { type = "AstLocal", name = "late_receiver", location = "5,6 - 5,19" }

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

local function makeCall(receiverExpression: any, method: string, selfCall: boolean): any
	return {
		type = "AstExprCall",
		location = callLocation,
		func = {
			type = "AstExprIndexName",
			location = "4,0 - 4,28",
			expr = receiverExpression,
			index = method,
		},
		args = {},
		self = selfCall,
	}
end

local function makeDocument(call: any, targetValue: any?): any
	return {
		root = {
			type = "AstStatBlock",
			location = "0,0 - 6,6",
			body = {
				localDeclaration(immutableReceiver, "0,0 - 0,30", nil),
				localDeclaration(mutableReceiver, "1,0 - 1,28", nil),
				{
					type = "AstStatAssign",
					location = "2,0 - 2,22",
					vars = { localExpression(mutableReceiver, "2,0 - 2,16") },
					values = { { type = "AstExprConstantNil", location = "2,19 - 2,22" } },
				},
				localDeclaration(unresolvedReceiver, "3,0 - 3,31", targetValue),
				{ type = "AstStatExpr", location = callLocation, expr = call },
				localDeclaration(lateReceiver, "5,0 - 5,25", nil),
				{ type = "AstStatReturn", location = "6,0 - 6,6", list = {} },
			},
		},
	}
end

local function evidence(locator: string): any
	return { kind = "dynamic_fixture", locator = locator, digest = sourceDigest }
end

local function recoveryWithOrigin(origin: any): any
	local selectors = JsonCodec.newArray()
	table.insert(selectors, { kind = "local_name", value = "unresolved_receiver" })
	local resolutions = JsonCodec.newArray()
	table.insert(resolutions, {
		call_location = callLocation,
		origin = origin,
		evidence = evidence("fixture:namecall-origin"),
	})
	return {
		source_sha256 = sourceDigest,
		call_site_count = 1,
		unresolved_call_count = 1,
		lowered_unresolved_call_count = 1,
		unresolved_target_selectors = selectors,
		target_resolutions = resolutions,
		detail = "method receiver identity requires authenticated recovery",
		evidence = {
			kind = "structural_derivation",
			locator = "fixture:namecall-origin-frontier",
			digest = sourceDigest,
		},
	}
end

local function namecallOrigin(receiver: any, method: string): any
	return { namecall = { receiver = receiver, method = method } }
end

local function encodedManifest(version: string, origin: any): string
	return LifterIR.encodeJson({
		schema_version = version,
		target_recovery = recoveryWithOrigin(origin),
	})
end

local immutableOrigin = namecallOrigin({ local_value = immutableReceiver.location }, "dispatch")
local acceptedV8Namecall = pcall(function()
	RecoveryManifest.decode(encodedManifest("lifter_recovery_manifest_v8", immutableOrigin), "v8-namecall-origin")
end)
assert(not acceptedV8Namecall, "v8 manifest accepted a v9 namecall origin")

local manifest = RecoveryManifest.decode(
	encodedManifest("lifter_recovery_manifest_v9", immutableOrigin),
	"v9-namecall-origin"
)
local manifestRecovery = manifest.target_recovery
local manifestResolution = if manifestRecovery ~= nil and manifestRecovery.target_resolutions ~= nil
	then manifestRecovery.target_resolutions[1]
	else nil
assert(
	manifestResolution ~= nil
		and manifestResolution.origin.namecall ~= nil
		and manifestResolution.origin.namecall.receiver.local_value == immutableReceiver.location
		and manifestResolution.origin.namecall.method == "dispatch",
	"v9 manifest lost the normalized namecall origin"
)

local function rejectsManifest(origin: any, label: string): boolean
	return not pcall(function()
		RecoveryManifest.decode(encodedManifest("lifter_recovery_manifest_v9", origin), label)
	end)
end

assert(rejectsManifest({ namecall = { method = "dispatch" } }, "v9-missing-receiver"), "v9 accepted a namecall without a receiver")
assert(rejectsManifest({ namecall = { receiver = { environment = "receiver" } } }, "v9-missing-method"), "v9 accepted a namecall without a method")
assert(rejectsManifest(namecallOrigin({ intrinsic = "pcall" }, "dispatch"), "v9-intrinsic-receiver"), "v9 accepted an intrinsic receiver")
assert(rejectsManifest(namecallOrigin({ environment = "receiver" }, ""), "v9-empty-method"), "v9 accepted an empty method name")

local sourceReceiverExpression = localExpression(unresolvedReceiver, "4,0 - 4,19")
local methodCall = makeCall(sourceReceiverExpression, "dispatch", true)
local immutableReceiverExpression = localExpression(immutableReceiver, "3,28 - 3,46")
local mutableReceiverExpression = localExpression(mutableReceiver, "3,28 - 3,44")
local lateReceiverExpression = localExpression(lateReceiver, "3,28 - 3,41")
local document = makeDocument(methodCall, immutableReceiverExpression)
local verified = TargetRecovery.verify(document, sourceText, manifestRecovery :: any)
local verifiedSite = verified.by_call_location[callLocation]
assert(
	verifiedSite ~= nil
		and verifiedSite.resolution ~= nil
		and verifiedSite.resolution.origin.kind == "namecall"
		and verifiedSite.resolution.origin.method == "dispatch"
		and verifiedSite.resolution.origin.receiver_origin.kind == "local_value",
	"target recovery lost the verified namecall receiver"
)

local unresolvedLift = AstFrontend.tryLift(document, {
	program_id = "frontend-namecall-origin-unresolved",
	source_name = "frontend-namecall-origin-unresolved",
	source_text = sourceText,
	target_recovery = {
		source_sha256 = sourceDigest,
		call_site_count = 1,
		unresolved_call_count = 1,
		lowered_unresolved_call_count = 1,
		unresolved_target_selectors = { { kind = "local_name", value = "unresolved_receiver" } },
		detail = "method receiver identity requires authenticated recovery",
		evidence = {
			kind = "structural_derivation",
			locator = "fixture:namecall-unresolved-frontier",
			digest = sourceDigest,
		},
	},
})
assert(unresolvedLift.program ~= nil and #unresolvedLift.diagnostics == 0, "frontend rejected an unresolved namecall receiver")
local unresolvedProgram = unresolvedLift.program :: any
assert(#unresolvedProgram.obligations == 1, "unresolved namecall did not produce exactly one obligation")
local unresolvedObligation = unresolvedProgram.obligations[1]
assert(unresolvedObligation.kind == "dispatch_proof", "unresolved namecall collapsed into a generic identity blocker")
local unresolvedInstructionId = unresolvedObligation.subject.instruction
assert(type(unresolvedInstructionId) == "number", "unresolved namecall blocker lost its instruction subject")
assert(
	unresolvedProgram.instructions[unresolvedInstructionId + 1].operation.namecall ~= nil,
	"unresolved namecall blocker does not identify the namecall operation"
)
local unresolvedJson = LifterIR.encodeJson(unresolvedProgram)
assert(
	string.find(unresolvedJson, '"kind":"dispatch_proof"', 1, true) ~= nil
		and string.find(unresolvedJson, '"kind":"unresolved_identity"', 1, true) == nil,
	"unresolved namecall taxonomy did not cross the JSON boundary"
)

local function acceptedByVerifier(call: any, origin: any, targetValue: any?): boolean
	return pcall(TargetRecovery.verify, makeDocument(call, targetValue), sourceText, recoveryWithOrigin(origin))
end

assert(
	not acceptedByVerifier(makeCall(sourceReceiverExpression, "dispatch", false), immutableOrigin, immutableReceiverExpression),
	"target recovery applied a namecall origin to an ordinary call"
)
assert(
	acceptedByVerifier(methodCall, namecallOrigin({ local_value = unresolvedReceiver.location }, "dispatch"), nil),
	"target recovery rejected an authenticated temporal namecall receiver"
)
assert(
	not acceptedByVerifier(methodCall, namecallOrigin({ local_value = immutableReceiver.location }, "other"), immutableReceiverExpression),
	"target recovery accepted a mismatched method name"
)
assert(
	not acceptedByVerifier(methodCall, { environment = "replacement_receiver" }, nil),
	"target recovery applied an ordinary value origin to a method call"
)
local computedReceiver = {
	type = "AstExprIndexName",
	location = "4,0 - 4,25",
	expr = sourceReceiverExpression,
	index = "child",
}
assert(
	not acceptedByVerifier(makeCall(computedReceiver, "dispatch", true), immutableOrigin, immutableReceiverExpression),
	"target recovery erased an effectful method receiver"
)
assert(
	not acceptedByVerifier(methodCall, namecallOrigin({ local_value = "9,0 - 9,8" }, "dispatch"), immutableReceiverExpression),
	"target recovery accepted an absent namecall receiver origin"
)

local function lift(origin: any, suffix: string, targetValue: any?): any
	return AstFrontend.tryLift(makeDocument(methodCall, targetValue), {
		program_id = "frontend-namecall-origin-" .. suffix,
		source_name = "frontend-namecall-origin-" .. suffix,
		source_text = sourceText,
		target_recovery = recoveryWithOrigin(origin),
	})
end

local immutableLift = lift(immutableOrigin, "immutable", immutableReceiverExpression)
assert(immutableLift.program ~= nil and #immutableLift.diagnostics == 0, "frontend rejected an immutable namecall receiver")
local namecallInstruction = nil
local namecallCount = 0
local tableGetCount = 0
for _, instruction in (immutableLift.program :: any).instructions do
	if instruction.operation.namecall ~= nil then
		namecallCount += 1
		namecallInstruction = instruction
	elseif instruction.operation.table_get ~= nil then
		tableGetCount += 1
	end
end
assert(namecallCount == 1 and tableGetCount == 0, "frontend did not lower namecall recovery as one namecall")
assert(
	namecallInstruction.operation.namecall.method == "dispatch",
	"frontend changed the authenticated namecall method"
)

local mutableLift = lift(
	namecallOrigin({ local_place = mutableReceiver.location }, "dispatch"),
	"mutable",
	mutableReceiverExpression
)
assert(mutableLift.program ~= nil and #mutableLift.diagnostics == 0, "frontend rejected a mutable namecall receiver")
local mutableNamecall = nil
local placeReadCount = 0
for _, instruction in (mutableLift.program :: any).instructions do
	if instruction.operation.place_read ~= nil then
		placeReadCount += 1
	elseif instruction.operation.namecall ~= nil then
		mutableNamecall = instruction
	end
end
assert(
	placeReadCount == 1 and mutableNamecall ~= nil,
	"frontend replayed the mutable receiver read instead of using its selected snapshot"
)

local valueKindMismatch = lift(
	namecallOrigin({ local_value = mutableReceiver.location }, "dispatch"),
	"value-kind-mismatch",
	mutableReceiverExpression
)
assert(
	valueKindMismatch.program == nil
		and valueKindMismatch.diagnostics[1].code == "target_recovery_mismatch",
	"frontend accepted a namecall local-value receiver backed by a mutable place"
)
local placeKindMismatch = lift(
	namecallOrigin({ local_place = immutableReceiver.location }, "dispatch"),
	"place-kind-mismatch",
	immutableReceiverExpression
)
assert(
	placeKindMismatch.program == nil
		and placeKindMismatch.diagnostics[1].code == "target_recovery_mismatch",
	"frontend accepted a namecall local-place receiver backed by an immutable value"
)
local lateOrigin = lift(namecallOrigin({ local_value = lateReceiver.location }, "dispatch"), "late", lateReceiverExpression)
assert(
	lateOrigin.program == nil and lateOrigin.diagnostics[1].code == "invalid_local_scope",
	"frontend accepted a namecall receiver declared after its call"
)

return true
