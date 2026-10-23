--!strict

-- luau-ast writes each number literal as the "%.17g" text of the parser's double. These checks decode texts in that
-- layout through AstAdmission.decodeParserBytes with Lune's JSON decoder and require each literal to come back as the
-- double its text names; a number literal whose fields come in another order is refused, and a string value stays a
-- string. A recovery manifest's literal key decoded through AstAdmission.decodeManifestBytes matches the same literal
-- in the target matcher, and a manifest number that is a string beginning with # is refused.

local serde = require("@lune/serde")

local AstAdmission = require("./ast_admission")
local TargetOriginExpressionMatcher = require("./target_origin_expression_matcher")

local function decodeJson(bytes: string): any
	return serde.decode("json", bytes)
end

local function bits(value: number): string
	return (string.gsub(string.pack(">d", value), ".", function(byte: string): string
		return string.format("%02x", string.byte(byte))
	end))
end

-- luau-ast's texts for 2^1023, 2^1022, 0.000001, 1e-9, 1e-12 and 1.602176634e-19, which the JSON decoder alone reads
-- one unit in the last place away, then for the largest finite double, 0.1 and 1e-320.
local texts = {
	"8.9884656743115795e+307",
	"4.4942328371557898e+307",
	"9.9999999999999995e-07",
	"1.0000000000000001e-09",
	"9.9999999999999998e-13",
	"1.6021766339999999e-19",
	"1.7976931348623157e+308",
	"0.10000000000000001",
	"9.9998886718268301e-321",
}
local items = {}
for index, text in texts do
	table.insert(items, `\{"type":"AstExprConstantNumber","location":"{index - 1},1 - {index - 1},2","value":{text}}`)
end
local document = AstAdmission.decodeParserBytes(
	`\{"root":\{"type":"AstStatBlock","location":"0,0 - 9,0","hasEnd":true,"body":[\{"type":"AstStatReturn",`
		.. `"location":"0,0 - 8,2","list":[{table.concat(items, ",")}]}]},"commentLocations":[]}`,
	"number literal transport",
	decodeJson
)
local literals = document.root.body[1].list
for index, text in texts do
	local expected = bits(tonumber(text) :: number)
	local decoded = bits(literals[index].value)
	assert(decoded == expected, `number literal {text} decoded to {decoded}, not {expected}`)
end

local reorderedAccepted, reorderedProblem = pcall(
	AstAdmission.decodeParserBytes,
	'{"type":"AstExprConstantNumber","value":9.9999999999999995e-07,"location":"0,7 - 0,15"}',
	"reordered number literal",
	decodeJson
)
assert(
	not reorderedAccepted
		and string.find(tostring(reorderedProblem), "parser number literal did not use exact text transport", 1, true) ~= nil,
	"a number literal whose fields come in another order was decoded without its text"
)

local stringLiteral = AstAdmission.decodeParserBytes(
	'{"type":"AstExprConstantNumber","location":"0,7 - 0,10","value":"1"}',
	"string number literal",
	decodeJson
)
assert(stringLiteral.value == "1", "a string number literal value did not stay a string")

-- The access handlers[<literal>] against a manifest key {"literal": {"number": <text>}}. 0.000001, 1e-6 and
-- 8.98846567431158e307 match only when the source literal is read exactly; 1.602176634e-19 and the text
-- 9.9999999999999995e-07 only when the manifest number is read exactly as well.
local manifestCases = {
	{ manifest = "0.000001", source = "9.9999999999999995e-07" },
	{ manifest = "1e-6", source = "9.9999999999999995e-07" },
	{ manifest = "8.98846567431158e307", source = "8.9884656743115795e+307" },
	{ manifest = "1.602176634e-19", source = "1.6021766339999999e-19" },
	{ manifest = "9.9999999999999995e-07", source = "9.9999999999999995e-07" },
}
local function noLocalMatch(_expression: any, _origin: any): boolean
	return false
end
for _, case in manifestCases do
	local access = AstAdmission.decodeParserBytes(
		`\{"type":"AstExprIndexExpr","location":"0,7 - 0,21","expr":\{"type":"AstExprGlobal","location":"0,7 - 0,15",`
			.. `"global":"handlers"},"index":\{"type":"AstExprConstantNumber","location":"0,16 - 0,20","value":{case.source}}}`,
		"literal key source",
		decodeJson
	)
	local manifest = AstAdmission.decodeManifestBytes(`\{"literal": \{"number": {case.manifest}}}`, decodeJson)
	local origin = {
		kind = "table_get",
		table_origin = { kind = "environment", name = "handlers" },
		key_origin = { kind = "constant_number", value = manifest.literal.number },
	}
	assert(
		TargetOriginExpressionMatcher.matchesDirect(access, origin, noLocalMatch),
		`the manifest number {case.manifest} did not match the source literal {case.source}`
	)
end

local markedAccepted = pcall(AstAdmission.decodeManifestBytes, '{"literal": {"number": "#7"}}', decodeJson)
assert(not markedAccepted, "a manifest number given as a string beginning with # was read as a number")
