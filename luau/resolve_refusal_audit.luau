--!strict

-- Refusal audit for `resolve-admitted-readable-ir` (Task T1.2 of docs/lifter/PLAN-T1.md).
--
-- Usage: lune run luau/resolve_refusal_audit.luau <semantic-lifter.exe> <fixture.json> <output-dir>
--
-- Runs `<semantic-lifter.exe> resolve-admitted-readable-ir <fixture.json> <output-dir>/admitted.json`
-- on an input whose admission is refused, then asserts, in order: the exit code is 1; stderr contains
-- `diagnostic=open_profile_obligation`; `<output-dir>/admitted.json` does not exist afterwards (a
-- refused resolve publishes no output). The output directory must exist and must not already hold
-- `admitted.json`, so that an absent file can only mean that nothing was published. Any failure
-- prints one line to stderr and exits 1.

local fs = require("@lune/fs")
local process = require("@lune/process")
local stdio = require("@lune/stdio")

local EXPECTED_EXIT_CODE = 1
local EXPECTED_DIAGNOSTIC = "diagnostic=open_profile_obligation"
local OUTPUT_NAME = "admitted.json"
local USAGE = "usage: lune run luau/resolve_refusal_audit.luau <semantic-lifter.exe> <fixture.json> <output-dir>"

local function firstLine(text: string): string
	return string.match(text, "[^\r\n]*%w[^\r\n]*") or text
end

local function audit(exePath: string?, fixturePath: string?, outputDir: string?): (string?, string?)
	if exePath == nil or exePath == "" or fixturePath == nil or fixturePath == "" or outputDir == nil or outputDir == "" then
		return USAGE, nil
	end
	if not fs.isDir(outputDir) then
		return `output directory {outputDir} does not exist`, nil
	end
	local outputPath = `{outputDir}/{OUTPUT_NAME}`
	if fs.metadata(outputPath).exists then
		return `{outputPath} already exists before the run`, nil
	end

	local spawned, result = pcall(process.exec, exePath, { "resolve-admitted-readable-ir", fixturePath, outputPath })
	if not spawned then
		return `could not run {exePath}: {firstLine(tostring(result))}`, nil
	end
	if result.code ~= EXPECTED_EXIT_CODE then
		return `expected exit code {EXPECTED_EXIT_CODE} from the refused resolve-admitted-readable-ir, got {result.code}`,
			nil
	end
	if string.find(result.stderr, EXPECTED_DIAGNOSTIC, 1, true) == nil then
		return `stderr of the refused resolve-admitted-readable-ir does not contain {EXPECTED_DIAGNOSTIC}`, nil
	end
	if fs.metadata(outputPath).exists then
		local size = if fs.isFile(outputPath) then #fs.readFile(outputPath) else 0
		return `the refused resolve-admitted-readable-ir published its output: {outputPath} exists ({size} bytes)`, nil
	end
	return nil, outputPath
end

local reason, outputPath = audit(process.args[1], process.args[2], process.args[3])
if reason ~= nil then
	stdio.ewrite(`resolve_refusal_audit: FAIL {reason}\n`)
	process.exit(1)
else
	print(`resolve_refusal_audit: ok (exit {EXPECTED_EXIT_CODE}, {EXPECTED_DIAGNOSTIC}, {outputPath} not written)`)
end
