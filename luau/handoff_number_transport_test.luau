--!strict

-- The compiler-disassembly frontend lifts a hand-off whose number constants the adapter wrote with JSON.stringify.
-- This check reads the hand-off given first and the IR the frontend wrote from it given second, takes every "number"
-- member of each from its text with tonumber, and requires the IR's constants to be the hand-off's, in order and bit
-- for bit. The hand-off holds 1.602176634e-19, 4.69e+27 and 2.4823470202363574e-143, which Lune's JSON decoder alone
-- reads one unit in the last place away, then 0.1 and 2.5.

local fs = require("@lune/fs")
local process = require("@lune/process")

local handoffPath = process.args[1]
local irPath = process.args[2]
assert(handoffPath ~= nil and irPath ~= nil, "expected the hand-off and the IR lifted from it")

local expectedTexts = { "1.602176634e-19", "4.69e+27", "2.4823470202363574e-143", "0.1", "2.5" }

local function bits(value: number): string
	return (string.gsub(string.pack(">d", value), ".", function(byte: string): string
		return string.format("%02x", string.byte(byte))
	end))
end

local function numberTexts(path: string): { string }
	local texts = {}
	for text in string.gmatch(fs.readFile(path), '"number"%s*:%s*(%-?%d[%d%.eE+%-]*)') do
		table.insert(texts, text)
	end
	return texts
end

local handoffTexts = numberTexts(handoffPath)
assert(
	table.concat(handoffTexts, ",") == table.concat(expectedTexts, ","),
	`the hand-off holds the number constants {table.concat(handoffTexts, ",")}`
)
local irTexts = numberTexts(irPath)
assert(#irTexts == #handoffTexts, `the IR holds {#irTexts} number constants, the hand-off {#handoffTexts}`)
for index, text in handoffTexts do
	local expected = bits(tonumber(text) :: number)
	local lifted = bits(tonumber(irTexts[index]) :: number)
	assert(lifted == expected, `hand-off number {text} lifted to {lifted}, not {expected}`)
end
