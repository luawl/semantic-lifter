--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")

type Case = {
	name: string,
	source: string,
	compiles: boolean,
	errorFragments: { string }?,
	mode: string?,
	outputFragments: { string }?,
}

local compilerPath = process.args[1]
local reportPath = process.args[2]
assert(compilerPath ~= nil and compilerPath ~= "", "expected a luau-compile path")
assert(reportPath ~= nil and reportPath ~= "", "expected a report path")

local function names(prefix: string, count: number): string
	local result = table.create(count)
	for index = 1, count do
		result[index] = prefix .. tostring(index - 1)
	end
	return table.concat(result, ", ")
end

local function reversedNames(prefix: string, count: number): string
	local result = table.create(count)
	for index = 1, count do
		result[index] = prefix .. tostring(count - index)
	end
	return table.concat(result, ", ")
end

local function retainedResults(count: number): string
	local values = names("r", count)
	return `local f = ...\nlocal {values} = f()\n`
end

local function orderedReturn(count: number): string
	local values = names("r", count)
	return retainedResults(count) .. `return {values}\n`
end

local function invocationFrame(count: number): string
	local values = names("r", count)
	return retainedResults(count) .. `f({values})\nreturn {values}\n`
end

local function tableFrame(count: number): string
	local values = names("r", count)
	return retainedResults(count) .. `local result = \{ {values} \}\nreturn result, {values}\n`
end

local function interpolationFrame(count: number): string
	local values = names("r", count)
	local format = string.rep("%*", count)
	return `local string_format = string.format\n`
		.. retainedResults(count)
		.. `local result = string_format("{format}", {values})\nreturn result, {values}\n`
end

local function reorderedReturn(count: number): string
	return retainedResults(count) .. `return {reversedNames("r", count)}\n`
end

local function expandedReturn(count: number): string
	local values = names("r", count)
	return `return function(f, ...)\n  local {values} = f()\n  return {values}, ...\nend\n`
end

local function storedExpandedReturn(count: number): string
	local values = names("r", count)
	return `local captured_rawget = rawget\nlocal captured_unpack = table.unpack\nreturn function(_producer, carrier, ...)\n  local {values} = ...\n  return {values}, captured_unpack(carrier, 1, captured_rawget(carrier, 0))\nend\n`
end

local function reentrantStoredExpandedReturn(count: number): string
	local values = names("r", count)
	local finalValues = names("final_r", count)
	local reads = table.create(count)
	for index = 1, count do
		reads[index] = `captured_rawget(carrier, {index})`
	end
	return "local captured_rawget = rawget\n"
		.. "local captured_rawset = rawset\n"
		.. "local captured_select = select\n"
		.. "local captured_unpack = table.unpack\n"
		.. "return function(producer)\n"
		.. `  local {finalValues}, carrier\n`
		.. "  while true do\n"
		.. "    carrier = (function(...)\n"
		.. "      local stored_values = {}\n"
		.. '      local stored_count = captured_select("#", ...)\n'
		.. "      captured_rawset(stored_values, 0, stored_count)\n"
		.. "      for stored_index = 1, stored_count do\n"
		.. "        captured_rawset(stored_values, stored_index, (captured_select(stored_index, ...)))\n"
		.. "      end\n"
		.. "      return stored_values\n"
		.. "    end)(producer())\n"
		.. `    local {values} = {table.concat(reads, ", ")}\n`
		.. "    if not r0 then\n"
		.. `      {finalValues} = {values}\n`
		.. "      break\n"
		.. "    end\n"
		.. "  end\n"
		.. `  return {finalValues}, captured_unpack(carrier, 1, captured_rawget(carrier, 0))\n`
		.. "end\n"
end

local function storedAdjustment(count: number): string
	local values = names("r", count)
	local expressions = table.create(count)
	for index = 1, count do
		expressions[index] = `captured_rawget(carrier, {index})`
	end
	return `local captured_rawget = rawget\nlocal captured_unpack = table.unpack\nreturn function(_producer, carrier)\n  local {values} = {table.concat(expressions, ", ")}\n  return captured_unpack(carrier, 1, captured_rawget(carrier, 0))\nend\n`
end

local function fixedReturn(count: number): string
	return "return " .. string.rep("nil, ", count - 1) .. "nil\n"
end

local function fixedResults(count: number): string
	return names("g", count) .. " = produce()\nreturn g0\n"
end

local function expressionDepth(operatorCount: number): string
	return "return 0" .. string.rep(" + 1", operatorCount) .. "\n"
end

local function syntaxDepth(blockCount: number): string
	return string.rep("do\n", blockCount) .. "return 0\n" .. string.rep("end\n", blockCount)
end

local function combinedSyntaxDepth(blockCount: number): string
	local condition = string.rep("f(", 128) .. "true" .. string.rep(")", 128)
	local expression = "0"
	for _ = 1, 128 do
		expression = `if {condition} then 1 else ({expression})`
	end
	return "return function(c, f)\n"
		.. string.rep("if c then\n", blockCount)
		.. `return {expression}\n`
		.. string.rep("end\n", blockCount)
		.. "return 1\nend\n"
end

local function upvalueFrame(middleLocalCount: number): string
	local outer = names("u", 199)
	local middle = names("m", middleLocalCount)
	local captured = if middleLocalCount == 0 then outer else outer .. ", " .. middle
	return `local {outer} = ...\nreturn function(...)\n  local {middle} = ...\n  return function()\n    return {captured}\n  end\nend\n`
end

local function closureFrame(count: number): string
	local lines = table.create(count + 2)
	lines[1] = "local sink = ..."
	for index = 1, count do
		lines[index + 1] = "sink(function() end)"
	end
	lines[count + 2] = "return sink"
	return table.concat(lines, "\n") .. "\n"
end

local function jumpDistance(statementCount: number): string
	-- At O1 each compound update contributes seven bytecode words.
	return "if c then\n" .. string.rep("a+=b\n", statementCount) .. "end\nreturn a\n"
end

local function extendedConstantTable(count: number): string
	local lines = table.create(count + 1)
	for index = 1, count do
		lines[index] = `a="{string.format("%x", index)}"`
	end
	lines[count + 1] = "return a"
	return table.concat(lines, "\n") .. "\n"
end

local localLimit = { "Out of local registers", "exceeded limit 200" }
local totalLimit = { "Out of registers", "exceeded limit 255" }
local upvalueLimit = { "Out of upvalue registers", "exceeded limit 200" }
local closureLimit = { "Exceeded closure limit" }
local jumpLimit = { "Exceeded jump distance limit" }
local resultLimit = { "Exceeded result count limit" }
local returnLimit = { "Exceeded return count limit" }
local recursionLimit = { "Exceeded allowed recursion depth", "simplify your expression" }
local cases: { Case } = {
	{ name = "local-200", source = orderedReturn(199), compiles = true },
	{ name = "local-201", source = orderedReturn(200), compiles = false, errorFragments = localLimit },
	{ name = "invocation-254", source = invocationFrame(126), compiles = true },
	{ name = "invocation-256", source = invocationFrame(127), compiles = false, errorFragments = totalLimit },
	{ name = "table-255", source = tableFrame(126), compiles = true },
	{ name = "table-257", source = tableFrame(127), compiles = false, errorFragments = totalLimit },
	{ name = "interpolation-255", source = interpolationFrame(125), compiles = true },
	{ name = "interpolation-257", source = interpolationFrame(126), compiles = false, errorFragments = totalLimit },
	{ name = "reordered-return-255", source = reorderedReturn(127), compiles = true },
	{ name = "reordered-return-257", source = reorderedReturn(128), compiles = false, errorFragments = totalLimit },
	{ name = "expanded-return-254", source = expandedReturn(126), compiles = true },
	{ name = "expanded-return-256", source = expandedReturn(127), compiles = false, errorFragments = totalLimit },
	{ name = "stored-expanded-return-254", source = storedExpandedReturn(123), compiles = true },
	{ name = "stored-expanded-return-256", source = storedExpandedReturn(124), compiles = false, errorFragments = totalLimit },
	{
		name = "reentrant-stored-expanded-return-local-200",
		source = reentrantStoredExpandedReturn(99),
		compiles = true,
	},
	{
		name = "reentrant-stored-expanded-return-local-202",
		source = reentrantStoredExpandedReturn(100),
		compiles = false,
		errorFragments = localLimit,
	},
	{ name = "stored-adjustment-local-200", source = storedAdjustment(198), compiles = true },
	{ name = "stored-adjustment-local-201", source = storedAdjustment(199), compiles = false, errorFragments = localLimit },
	{ name = "fixed-return-254", source = fixedReturn(254), compiles = true },
	{ name = "fixed-return-255", source = fixedReturn(255), compiles = false, errorFragments = returnLimit },
	{ name = "fixed-results-254", source = fixedResults(254), compiles = true },
	{ name = "fixed-results-255", source = fixedResults(255), compiles = false, errorFragments = resultLimit },
	{ name = "expression-depth-998", source = expressionDepth(998), compiles = true },
	{ name = "expression-depth-999", source = expressionDepth(999), compiles = false, errorFragments = recursionLimit },
	{ name = "syntax-depth-998", source = syntaxDepth(998), compiles = true },
	{ name = "syntax-depth-999", source = syntaxDepth(999), compiles = false, errorFragments = recursionLimit },
	{ name = "combined-depth-512", source = combinedSyntaxDepth(512), compiles = true },
	{ name = "combined-depth-640", source = combinedSyntaxDepth(640), compiles = false, errorFragments = recursionLimit },
	{ name = "upvalue-200", source = upvalueFrame(1), compiles = true },
	{ name = "upvalue-201", source = upvalueFrame(2), compiles = false, errorFragments = upvalueLimit },
	{ name = "closure-32768", source = closureFrame(32768), compiles = true },
	{ name = "closure-32769", source = closureFrame(32769), compiles = false, errorFragments = closureLimit },
	{ name = "jump-distance-8388604", source = jumpDistance(1198372), compiles = true },
	{ name = "jump-distance-8388611", source = jumpDistance(1198373), compiles = false, errorFragments = jumpLimit },
	{
		name = "constant-loadkx-32768",
		source = extendedConstantTable(32769),
		compiles = true,
		mode = "--text",
		outputFragments = { "LOADKX", "K32768" },
	},
}

assert(#process.args == #cases + 2, "expected one generated source path per register case")
local report = table.create(#cases)
for index, case in cases do
	local sourcePath = process.args[index + 2]
	assert(sourcePath ~= nil and sourcePath ~= "", `missing source path for {case.name}`)
	fs.writeFile(sourcePath, case.source)

	local ok, result = pcall(function()
		return process.exec(compilerPath, { case.mode or "--null", sourcePath })
	end)
	local compiled = false
	local output = ""
	if ok then
		local execution = result :: any
		compiled = execution.ok == true and tostring(execution.stderr or "") == ""
		output = tostring(execution.stdout or "") .. tostring(execution.stderr or "")
	else
		output = tostring(result)
	end

	assert(compiled == case.compiles, `{case.name}: compiler result did not match the expected boundary: {output}`)
	if case.errorFragments ~= nil then
		for _, fragment in case.errorFragments do
			assert(string.find(output, fragment, 1, true) ~= nil, `{case.name}: missing compiler diagnostic fragment {fragment}: {output}`)
		end
	end
	if case.outputFragments ~= nil then
		for _, fragment in case.outputFragments do
			assert(string.find(output, fragment, 1, true) ~= nil, `{case.name}: missing compiler output fragment {fragment}`)
		end
	end
	report[index] = `{case.name}={if compiled then "accepted" else "rejected"}`
end

fs.writeFile(reportPath, table.concat(report, "\n") .. "\n")
