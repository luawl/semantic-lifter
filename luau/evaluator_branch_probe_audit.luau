--!strict

-- Branch audit for the probes of two solver evaluator gaps: integers beyond 2^53 and value-selecting `or`/`and`.
--
-- Usage: lune run luau/evaluator_branch_probe_audit.luau <semantic-lifter.exe> <output-dir> <probe.lifter-ir.json>...
--
-- Each probe is a hand-built chunk whose second function branches on a comparison that Luau decides by double
-- arithmetic or by a value-selecting `or`/`and`, so the resolver must keep both arms. For every probe the audit runs
-- `<semantic-lifter.exe> resolve-ir <probe> <output-dir>/<name>.resolved.lifter-ir.json internal` and asserts that the
-- run exits 0 and that the resolved terminator of the second function's entry block is still a `branch` with both
-- edges. Every probe is resolved before any failure is reported. Any failure prints one line per probe to stderr and
-- exits 1.

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")
local stdio = require("@lune/stdio")

local USAGE =
	"usage: lune run luau/evaluator_branch_probe_audit.luau <semantic-lifter.exe> <output-dir> <probe.lifter-ir.json>..."

local function firstLine(text: string): string
	return string.match(text, "[^\r\n]*%w[^\r\n]*") or text
end

local function probeName(probePath: string): string
	local base = string.match(probePath, "([%w_%.%-]+)$") or probePath
	return (string.gsub(base, "%.lifter%-ir%.json$", ""))
end

local function entryTerminator(resolvedPath: string): (any?, string?)
	local decoded, program = pcall(function(): any
		return serde.decode("json", fs.readFile(resolvedPath))
	end)
	if not decoded or type(program) ~= "table" then
		return nil, "the resolved program is not JSON"
	end
	local functions = program.functions
	local blocks = program.blocks
	if type(functions) ~= "table" or type(blocks) ~= "table" or functions[2] == nil then
		return nil, "the resolved program has no probe function"
	end
	local entry = functions[2].entry_block
	if type(entry) ~= "number" or blocks[entry + 1] == nil then
		return nil, "the probe function has no entry block"
	end
	return blocks[entry + 1].terminator, nil
end

local function auditProbe(exePath: string, outputDir: string, probePath: string): string?
	local name = probeName(probePath)
	local outputPath = `{outputDir}/{name}.resolved.lifter-ir.json`
	local spawned, result = pcall(process.exec, exePath, { "resolve-ir", probePath, outputPath, "internal" })
	if not spawned then
		return `{name}: could not run {exePath}: {firstLine(tostring(result))}`
	end
	if result.code ~= 0 then
		return `{name}: resolve-ir exited {result.code}: {firstLine(result.stderr)}`
	end
	local terminator, problem = entryTerminator(outputPath)
	if problem ~= nil then
		return `{name}: {problem}`
	end
	if type(terminator) ~= "table" or type(terminator.branch) ~= "table" then
		local kind = if type(terminator) == "table" then (next(terminator) or "none") else "none"
		return `{name}: the resolver decided the probe branch (entry terminator {kind}, expected branch)`
	end
	if terminator.branch.then_edge == nil or terminator.branch.else_edge == nil then
		return `{name}: the probe branch lost an arm`
	end
	return nil
end

local exePath = process.args[1]
local outputDir = process.args[2]
local failures: { string } = {}
if exePath == nil or exePath == "" or outputDir == nil or outputDir == "" or process.args[3] == nil then
	table.insert(failures, USAGE)
elseif not fs.isDir(outputDir) then
	table.insert(failures, `output directory {outputDir} does not exist`)
else
	for index = 3, #process.args do
		local failure = auditProbe(exePath, outputDir, process.args[index])
		if failure ~= nil then
			table.insert(failures, failure)
		end
	end
end
if #failures > 0 then
	for _, failure in failures do
		stdio.ewrite(`evaluator_branch_probe_audit: FAIL {failure}\n`)
	end
	process.exit(1)
else
	print(`evaluator_branch_probe_audit: ok ({#process.args - 2} probes keep both arms)`)
end
