--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")

type NameSet = { [string]: boolean }

local MAX_DIAGNOSTIC_BYTES = 4 * 1024 * 1024

local function collectUnknownGlobals(output: string): NameSet
	local names: NameSet = {}
	for name in string.gmatch(output, "TypeError: Unknown global '([^']+)'") do
		names[name] = true
	end
	return names
end

-- luau-analyze reports an all-digit number literal of 2^53 or more that is not the exact digits of its value
-- (2^64 written as 18446744073709552000) as IntegerParsing and still exits 0, so the lines are counted.
local function countIntegerParsing(output: string): number
	local count = 0
	for _ in string.gmatch(output, "IntegerParsing: ") do
		count += 1
	end
	return count
end

local function analyze(analyzerPath: string, sourcePath: string): (NameSet, number)
	local result = process.exec(analyzerPath, { "--mode=strict", sourcePath })
	local output = result.stdout .. "\n" .. result.stderr
	assert(#output <= MAX_DIAGNOSTIC_BYTES, `luau-analyze diagnostics exceeded the bounded oracle limit for {sourcePath}`)
	if not result.ok then
		assert(
			result.code == 1 and string.find(output, "): ", 1, true) ~= nil,
			`luau-analyze failed for {sourcePath} with exit code {result.code}: {output}`
		)
	end
	return collectUnknownGlobals(output), countIntegerParsing(output)
end

local function unexpectedNames(sourceNames: NameSet, generatedNames: NameSet): { string }
	local names: { string } = {}
	for name in generatedNames do
		if sourceNames[name] ~= true then
			table.insert(names, name)
		end
	end
	table.sort(names)
	return names
end

local function assertNoIntroducedGlobals(sourceNames: NameSet, generatedNames: NameSet, generatedPath: string)
	local unexpected = unexpectedNames(sourceNames, generatedNames)
	if #unexpected ~= 0 then
		error(`generated Luau introduced unknown globals in {generatedPath}: {table.concat(unexpected, ", ")}`, 0)
	end
end

local function assertNoIntroducedIntegerParsing(sourceCount: number, generatedCount: number, generatedPath: string)
	if generatedCount > sourceCount then
		error(
			`generated Luau has {generatedCount} IntegerParsing lines where its source has {sourceCount} in {generatedPath}`,
			0
		)
	end
end

local mode = process.args[1]
local analyzerPath = process.args[2]
assert(mode ~= nil and mode ~= "", "expected an oracle mode")
assert(analyzerPath ~= nil and analyzerPath ~= "", "expected a luau-analyze path")

if mode == "check" then
	local sourcePath = process.args[3]
	local generatedPath = process.args[4]
	assert(sourcePath ~= nil and sourcePath ~= "", "expected a source Luau path")
	assert(generatedPath ~= nil and generatedPath ~= "", "expected a generated Luau path")
	local sourceNames, sourceIntegerParsing = analyze(analyzerPath, sourcePath)
	local generatedNames, generatedIntegerParsing = analyze(analyzerPath, generatedPath)
	assertNoIntroducedGlobals(sourceNames, generatedNames, generatedPath)
	assertNoIntroducedIntegerParsing(sourceIntegerParsing, generatedIntegerParsing, generatedPath)
elseif mode == "self-test" then
	local sourcePath = process.args[3]
	local generatedPath = process.args[4]
	assert(sourcePath ~= nil and sourcePath ~= "", "expected a self-test source path")
	assert(generatedPath ~= nil and generatedPath ~= "", "expected a self-test generated path")
	fs.writeFile(sourcePath, "ambient()\n")
	fs.writeFile(generatedPath, "ambient()\nreturn leakedLocal()\n")

	local sourceNames = analyze(analyzerPath, sourcePath)
	local generatedNames = analyze(analyzerPath, generatedPath)
	assert(sourceNames.ambient == true and sourceNames.leakedLocal ~= true, "source diagnostic census changed")
	assert(generatedNames.ambient == true and generatedNames.leakedLocal == true, "generated diagnostic census changed")
	assertNoIntroducedGlobals(sourceNames, sourceNames, sourcePath)
	local ok = pcall(assertNoIntroducedGlobals, sourceNames, generatedNames, generatedPath)
	assert(not ok, "negative lexical oracle did not reject")

	-- 2^64 with its exact digits, and the same double with its shortest digits padded with zeros.
	fs.writeFile(sourcePath, "return 18446744073709551616\n")
	fs.writeFile(generatedPath, "return 18446744073709552000\n")
	local _, exactCount = analyze(analyzerPath, sourcePath)
	local _, paddedCount = analyze(analyzerPath, generatedPath)
	assert(exactCount == 0 and paddedCount == 1, "integer parsing diagnostic census changed")
	assertNoIntroducedIntegerParsing(exactCount, exactCount, sourcePath)
	local integerParsingOk = pcall(assertNoIntroducedIntegerParsing, exactCount, paddedCount, generatedPath)
	assert(not integerParsingOk, "negative integer parsing oracle did not reject")
else
	error(`unknown generated lexical oracle mode {mode}`, 0)
end
