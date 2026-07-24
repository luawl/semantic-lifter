--!strict

local AstFrontend = require("./ast_frontend")
local RecoveryManifest = require("./recovery_manifest")
local TargetProofBundle = require("./target_proof_bundle")

local sourceText = "abc"
local sourceDigest = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
local target = { type = "AstLocal", name = "versioned_target", location = "0,6 - 0,22" }
local firstClosureLocation = "1,19 - 3,3"
local secondClosureLocation = "5,19 - 7,3"
local firstCallLocation = "4,0 - 4,18"
local secondCallLocation = "8,0 - 8,18"

local function localExpression(location: string): any
	return { type = "AstExprLocal", location = location, ["local"] = target }
end

local function closureExpression(location: string, bodyLocation: string, returnLocation: string, tag: string): any
	return {
		type = "AstExprFunction",
		location = location,
		args = {},
		vararg = false,
		body = {
			type = "AstStatBlock",
			location = bodyLocation,
			body = {
				{
					type = "AstStatReturn",
					location = returnLocation,
					list = { { type = "AstExprConstantString", location = returnLocation, value = tag } },
				},
			},
		},
	}
end

local firstClosure = closureExpression(firstClosureLocation, "1,28 - 3,3", "2,4 - 2,18", "first")
local secondClosure = closureExpression(secondClosureLocation, "5,28 - 7,3", "6,4 - 6,19", "second")

local function assignment(location: string, targetLocation: string, value: any): any
	return {
		type = "AstStatAssign",
		location = location,
		vars = { localExpression(targetLocation) },
		values = { value },
	}
end

local function callStatement(location: string): any
	return {
		type = "AstStatExpr",
		location = location,
		expr = {
			type = "AstExprCall",
			location = location,
			func = localExpression(location),
			args = {},
			self = false,
		},
	}
end

local statements: { any } = {
	{
		type = "AstStatLocal",
		location = "0,0 - 0,28",
		vars = { target },
		values = { { type = "AstExprConstantNil", location = "0,25 - 0,28" } },
	},
	assignment("1,0 - 3,3", "1,0 - 1,16", firstClosure),
	callStatement(firstCallLocation),
	assignment("5,0 - 7,3", "5,0 - 5,16", secondClosure),
	callStatement(secondCallLocation),
	{ type = "AstStatReturn", location = "9,0 - 9,6", list = {} },
}

local document: any = {
	root = {
		type = "AstStatBlock",
		location = "0,0 - 9,6",
		body = statements,
	},
}

local function evidence(locator: string): any
	return { kind = "dynamic_fixture", locator = locator, digest = sourceDigest }
end

local function manifest(version: string, closureLocation: any): any
	return {
		schema_version = version,
		target_recovery = {
			source_sha256 = sourceDigest,
			call_site_count = 2,
			unresolved_call_count = 2,
			lowered_unresolved_call_count = 2,
			unresolved_target_selectors = { { kind = "local_name", value = "versioned_target" } },
			target_resolutions = {
				{
					call_location = firstCallLocation,
					origin = { closure_value = closureLocation },
					evidence = evidence("fixture:closure-target-resolution"),
				},
			},
			detail = "closure target identity requires authenticated recovery",
			evidence = evidence("fixture:closure-target-frontier"),
		},
	}
end

local acceptedByV14 = pcall(RecoveryManifest.fromDecoded, manifest("lifter_recovery_manifest_v14", firstClosureLocation), "v14-closure")
assert(not acceptedByV14, "v14 manifest accepted a v15 closure origin")

local decoded = RecoveryManifest.fromDecoded(
	manifest("lifter_recovery_manifest_v15", firstClosureLocation),
	"v15-closure"
)
local recovery = decoded.target_recovery
assert(recovery ~= nil and recovery.target_resolutions ~= nil, "v15 manifest lost closure recovery")
assert(
	(recovery :: any).target_resolutions[1].origin.closure_value == firstClosureLocation,
	"v15 manifest changed the closure allocation identity"
)

local acceptedMalformed = pcall(
	RecoveryManifest.fromDecoded,
	manifest("lifter_recovery_manifest_v15", 7),
	"v15-malformed-closure"
)
assert(not acceptedMalformed, "v15 manifest accepted a non-string closure identity")

local lifted = AstFrontend.tryLift(document, {
	program_id = "frontend-closure-target",
	source_name = "frontend-closure-target",
	source_text = sourceText,
	target_recovery = recovery,
})
assert(lifted.program ~= nil and #lifted.diagnostics == 0, "frontend rejected an exact closure allocation")
local program = lifted.program :: any
assert(#program.obligations == 1, "closure recovery did not retain only the later unresolved generation")
assert(
	#program.places == 1 and program.places[1].name_hint == "versioned_target",
	"partial closure recovery renamed every generation of a mutable place"
)
local closureCount = 0
local callCount = 0
for _, instruction in program.instructions do
	if instruction.operation.make_closure ~= nil then
		closureCount += 1
	elseif instruction.operation.call ~= nil then
		callCount += 1
	end
end
assert(closureCount == 2 and callCount == 2, "closure recovery recreated an allocation or changed a call")

local function rejectedClosure(location: string, suffix: string): boolean
	local invalid = RecoveryManifest.fromDecoded(
		manifest("lifter_recovery_manifest_v15", location),
		"v15-closure-" .. suffix
	)
	local result = AstFrontend.tryLift(document, {
		program_id = "frontend-closure-target-" .. suffix,
		source_name = "frontend-closure-target-" .. suffix,
		source_text = sourceText,
		target_recovery = invalid.target_recovery,
	})
	return result.program == nil and result.diagnostics[1].code == "target_recovery_mismatch"
end

assert(rejectedClosure(secondClosureLocation, "wrong-generation"), "closure recovery accepted a later allocation")
assert(rejectedClosure("20,0 - 20,8", "absent"), "closure recovery accepted an absent allocation")

local firstDigest = TargetProofBundle.targetProofDigest(
	sourceDigest,
	firstCallLocation,
	{ closure_value = firstClosureLocation },
	"closure proof"
)
local secondDigest = TargetProofBundle.targetProofDigest(
	sourceDigest,
	firstCallLocation,
	{ closure_value = secondClosureLocation },
	"closure proof"
)
assert(firstDigest ~= secondDigest, "closure proof framing omitted the allocation identity")

return true
