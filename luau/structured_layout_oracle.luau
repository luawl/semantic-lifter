--!strict
-- Layout oracle for a generated text whose functions the structured layout must write: no top-level function (a
-- line `<name> = function(` or `local <name> = function(` at column 0, through the next `end` at column 0) may
-- declare the program counter of the flat layout's dispatcher loop (`local __lifter_pc = ...`, or a renamed
-- `__lifter_pc_<n>`). A passing text prints nothing. A failing text prints one line per function written in the
-- flat layout, `<case> <function> flat`, and fails one assertion that counts them.
-- argv: <case name> <generated Luau path>
local fs = require("@lune/fs")
local process = require("@lune/process")

local caseName = process.args[1]
local generatedPath = process.args[2]
assert(caseName ~= nil and caseName ~= "", "expected a case name")
assert(generatedPath ~= nil and generatedPath ~= "", "expected a generated Luau path")

local functions = 0
local flat: { string } = {}
local current = ""
local currentFlat = false
for _, line in string.split(fs.readFile(generatedPath), "\n") do
	local name = string.match(line, "^local ([%a_][%w_]*) = function%(") or string.match(line, "^([%a_][%w_]*) = function%(")
	if name ~= nil then
		functions += 1
		current = name
		currentFlat = false
	elseif current ~= "" and line == "end" then
		if currentFlat then
			table.insert(flat, current)
		end
		current = ""
	elseif current ~= "" and string.match(line, "^%s*local __lifter_pc[_%d]* = ") ~= nil then
		currentFlat = true
	end
end

assert(functions > 0, `{caseName}: no top-level function found`)
for _, flatName in flat do
	print(`{caseName} {flatName} flat`)
end
assert(#flat == 0, `{caseName}: {#flat} of {functions} functions written in the flat layout`)
