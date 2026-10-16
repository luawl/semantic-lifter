--!strict
-- Track T6 (T6.2, T6-NUMERIC-OPERAND-DOUBLE-RENDER): an inlined numeric transition operand that the emitter
-- follows with an operator (` * 1`, ` + <step>`) is rendered grouped. Each input is an admitted crafted IR
-- (luau/fixtures/numeric_operand_*_concat.lifter-ir.json) whose transition control is the inlined `1 .. 2`.
-- Usage: lune run luau/numeric_operand_grouping_audit.luau <luau-numeric|semantic-normalized> <emitted.luau>
local fs = require("@lune/fs")
local process = require("@lune/process")

local mode = process.args[1]
local source = fs.readFile(process.args[2])

local function has(text: string): boolean
	return string.find(source, text, 1, true) ~= nil
end

if mode == "luau-numeric" then
	assert(
		has("for __lifter_numeric_guard = 1 .. 2, header_limit, header_step do break end"),
		"the coercion guard lost its root-context operand list"
	)
	assert(has("numeric_normalized_limit = header_limit * 1"), "a name operand before ' * 1' changed")
	assert(has("numeric_normalized_step = header_step * 1"), "a name operand before ' * 1' changed")
	assert(has("numeric_next_control = (1 .. 2) * 1"), "an inlined control operand before ' * 1' is not grouped")
	assert(
		has("numeric_next_control = (1 .. 2) + numeric_normalized_step"),
		"an inlined control operand before ' + ' is not grouped"
	)
	assert(not has("numeric_next_control = 1 .. 2 * 1"), "the ungrouped ' * 1' line remains")
	assert(not has("numeric_next_control = 1 .. 2 + numeric_normalized_step"), "the ungrouped ' + ' line remains")
elseif mode == "semantic-normalized" then
	assert(
		has("numeric_next_control = (1 .. 2) + numeric_normalized_step"),
		"an inlined control operand before ' + ' is not grouped"
	)
	assert(not has("numeric_next_control = 1 .. 2 + numeric_normalized_step"), "the ungrouped ' + ' line remains")
else
	error("unknown audit mode " .. tostring(mode))
end
print("numeric operand grouping: ok")
