--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")

local AstAdmission = require("./ast_admission")
local AstFrontend = require("./ast_frontend")
local LifterIR = require("./lifter_ir")
local RecoveryManifest = require("./recovery_manifest")
local TargetProofBundle = require("./target_proof_bundle")

local parserPath = process.args[1]
local sourcePath = process.args[2]
local programId = process.args[3]
local outputPath = process.args[4]
local sourceName = process.args[5] or programId
local recoveryArgument = process.args[6]
local recoveryManifestPath = if recoveryArgument == "omit-name-hints" then nil else recoveryArgument
local proofBundlePath = process.args[7]
local proofVerifierPath = process.args[8]
local trustedProofPublicKey = process.args[9]
local nameHintPolicy = if recoveryArgument == "omit-name-hints" then recoveryArgument else process.args[10]

assert(parserPath ~= nil and parserPath ~= "", "expected a luau-ast parser path")
assert(sourcePath ~= nil and sourcePath ~= "", "expected a Luau source path")
assert(programId ~= nil and programId ~= "", "expected a program ID")
assert(outputPath ~= nil and outputPath ~= "", "expected an output JSON path")
assert(sourceName ~= nil and sourceName ~= "", "expected a source evidence name")
assert(
	nameHintPolicy == nil or nameHintPolicy == "omit-name-hints",
	"name-hint policy must be omit-name-hints when provided"
)

local function omitNameHints(value: any)
	if type(value) ~= "table" then
		return
	end

	value.name_hint = nil
	for _, child in value do
		omitNameHints(child)
	end
end

local sourceText = AstAdmission.expectSourceBytes(fs.readFile(sourcePath), sourcePath)
local parsed = process.exec(parserPath, { sourcePath })
if not parsed.ok then
	error(`luau-ast failed with exit code {parsed.code}: {parsed.stderr}`, 0)
end

local document = AstAdmission.decodeParserBytes(
	parsed.stdout,
	`luau-ast output for {sourcePath}`,
	function(bytes: string): any
		return serde.decode("json", bytes)
	end
)
assert(type(document) == "table", "luau-ast returned a non-object document")
local frontendOptions: AstFrontend.Options = {
	program_id = programId,
	source_name = sourceName,
	source_text = sourceText,
}
if recoveryManifestPath ~= nil then
	local proofBundleInput: RecoveryManifest.ProofBundleInput? = nil
	if proofBundlePath ~= nil or proofVerifierPath ~= nil or trustedProofPublicKey ~= nil then
		assert(
			proofBundlePath ~= nil and proofVerifierPath ~= nil and trustedProofPublicKey ~= nil,
			"detached proof bundle requires bytes, verifier, and trusted public key"
		)
		local proofBundleBytes = fs.readFile(proofBundlePath :: string)
		local proofBundleDigest = TargetProofBundle.sha256(proofBundleBytes)
		proofBundleInput = {
			bytes = proofBundleBytes,
			decode = function(bytes: string): any
				return serde.decode("json", bytes)
			end,
			trusted_public_key = trustedProofPublicKey :: string,
			verify_signature = function(message: string, signature: string, publicKey: string): boolean
				assert(message == proofBundleBytes, "proof verifier received bytes from another bundle")
				local verification = process.exec(proofVerifierPath :: string, {
					"verify-file",
					proofBundlePath :: string,
					proofBundleDigest,
					signature,
					publicKey,
				})
				return verification.ok
			end,
		}
	end
	local manifest = RecoveryManifest.fromBytes(
		fs.readFile(recoveryManifestPath),
		recoveryManifestPath,
		function(bytes: string): any
			return serde.decode("json", bytes)
		end,
		proofBundleInput
	)
	frontendOptions.program_obligations = manifest.program_obligations
	frontendOptions.intrinsic_bindings = manifest.intrinsic_bindings
	frontendOptions.target_recovery = manifest.target_recovery
end
local result = AstFrontend.tryLift(document, frontendOptions)
if result.program == nil then
	local messages = {}
	for _, item in result.diagnostics do
		table.insert(messages, AstFrontend.formatDiagnostic(item))
	end
	error(table.concat(messages, "\n"), 0)
end

if nameHintPolicy == "omit-name-hints" then
	omitNameHints(result.program)
end
fs.writeFile(outputPath, LifterIR.encodeJson(result.program, true) .. "\n")
