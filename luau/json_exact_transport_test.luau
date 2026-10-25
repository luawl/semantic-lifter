--!strict

-- JsonExact.decode reads every number of a JSON document from its own text. These checks decode documents in an
-- observation layout (arrays of arguments and results) and in a compiler hand-off layout (each constant's "number"
-- member, written with spaces and line breaks) whose number texts Lune's JSON decoder alone reads one or two units in
-- the last place away, beside texts it reads exactly, and require each value to be the double tonumber reads from its
-- text. Strings stay as they are. A string carrying the transport mark, a number with a leading zero, a number beyond
-- the finite doubles and a decoder that hands back a JSON number are refused.

local serde = require("@lune/serde")

local JsonExact = require("./json_exact")

local function decodeJson(bytes: string): any
	return serde.decode("json", bytes)
end

local function bits(value: number): string
	return (string.gsub(string.pack(">d", value), ".", function(byte: string): string
		return string.format("%02x", string.byte(byte))
	end))
end

-- The "%.17g" texts of 2^1023, 2^1022, 0.000001, 1e-9, 1e-12 and 1.602176634e-19, the shortest texts of
-- 1.602176634e-19, 4.69e27 and -2.4823470202363574e-143, a 24-digit integer and 300e-25: the JSON decoder alone reads
-- each of these to a neighbouring double. Then texts it reads exactly.
local texts = {
	"8.9884656743115795e+307",
	"4.4942328371557898e+307",
	"9.9999999999999995e-07",
	"1.0000000000000001e-09",
	"9.9999999999999998e-13",
	"1.6021766339999999e-19",
	"1.602176634e-19",
	"4.69e+27",
	"-2.4823470202363574e-143",
	"123456789012345678901234",
	"300e-25",
	"0.1",
	"2.5",
	"1e-6",
	"7",
	"-0",
	"18446744073709551616",
}

local constants = {}
for _, text in texts do
	table.insert(constants, '{\n      "kind": "constant",\n      "value": {\n        "number": ' .. text .. "\n      }\n    }")
end
local observations = JsonExact.decode(
	'[{"arguments":[' .. table.concat(texts, ",") .. '],"results":["#5","\\u00e9","a\\"1.5e9\\\\",true,-1.5]}]',
	"observation layout",
	decodeJson
)
local handoff = JsonExact.decode(
	'{\n  "schema_version": "compiler_disassembly_handoff_v2",\n  "function_index": 0,\n  "instructions": [\n    '
		.. table.concat(constants, ",\n    ")
		.. "\n  ]\n}\n",
	"hand-off layout",
	decodeJson
)
for index, text in texts do
	local expected = bits(tonumber(text) :: number)
	local argument = observations[1].arguments[index]
	assert(type(argument) == "number", `observation argument {index} did not decode to a number`)
	assert(bits(argument) == expected, `number text {text} decoded to {bits(argument)}, not {expected}`)
	local constant = handoff.instructions[index].value.number
	assert(type(constant) == "number", `hand-off constant {index} did not decode to a number`)
	assert(bits(constant) == expected, `hand-off number text {text} decoded to {bits(constant)}, not {expected}`)
end
local results = observations[1].results
assert(results[1] == "#5" and results[2] == "\u{e9}" and results[3] == 'a"1.5e9\\', "a string changed")
assert(results[4] == true and results[5] == -1.5, "a Boolean or the last number changed")

local function refusal(bytes: string, decode: (string) -> any): string
	local accepted, problem = pcall(JsonExact.decode, bytes, "refused document", decode)
	assert(not accepted, `the document {bytes} was decoded`)
	return tostring(problem)
end
assert(
	string.find(refusal('["\\u00011.5"]', decodeJson), "did not mark", 1, true) ~= nil,
	"a string carrying the transport mark was read as a number"
)
refusal("[01]", decodeJson)
assert(
	string.find(refusal("[1e400]", decodeJson), "names no finite double", 1, true) ~= nil,
	"a number text beyond the finite doubles was admitted"
)
assert(
	string.find(
		refusal("[2.5]", function(_bytes: string): any
			return { 2.5 }
		end),
		"did not use exact text transport",
		1,
		true
	) ~= nil,
	"a decoded JSON number that did not cross the decoder as text was admitted"
)
local bare = JsonExact.decode("1.6021766339999999e-19", "bare number", decodeJson)
assert(bits(bare) == "3c07a4da290c1653", "a bare number document was not read from its text")
