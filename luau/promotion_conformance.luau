--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")

local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output JSON path")

local builder = LifterIR.Builder.new("generic-automatic-solver-promotion")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-automatic-solver-promotion")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local u32 = LifterIR.Types.integer(32, false)

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local probe = builder:reserveFunction({ name_hint = "probe", evidence = evidence })
local chunkBlock = builder:reserveBlock(chunk, { evidence = evidence })
local entry = builder:reserveBlock(probe, { evidence = evidence })
local matched = builder:reserveBlock(probe, { evidence = evidence })
local unreachable = builder:reserveBlock(probe, { evidence = evidence })

builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(probe, entry)

local _, exportedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(probe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "exported" } },
	{ effects = pure, evidence = evidence }
)

local function addU32Constant(value: string, nameHint: string): number
	local _, results = builder:addInstruction(
		entry,
		LifterIR.Operation.constant(LifterIR.Literal.integer(value)),
		{ { type = u32, name_hint = nameHint } },
		{ effects = pure, evidence = evidence }
	)
	return results[1]
end

local left = addU32Constant("6", "left")
local mask = addU32Constant("1", "mask")
local zero = addU32Constant("0", "zero")
local _, bitResults = builder:addInstruction(
	entry,
	LifterIR.Operation.binary("bit_and", left, mask, "primitive"),
	{ { type = u32, name_hint = "masked" } },
	{ effects = pure, evidence = evidence }
)
local _, bitConditionResults = builder:addInstruction(
	entry,
	LifterIR.Operation.binary("equal", bitResults[1], zero, "primitive"),
	{ { type = LifterIR.Types.boolean(), name_hint = "is_zero" } },
	{ effects = pure, evidence = evidence }
)

local function addIntegerConstant(value: string, nameHint: string): number
	local _, results = builder:addInstruction(
		entry,
		LifterIR.Operation.constant(LifterIR.Literal.integer(value)),
		{ { type = LifterIR.Types.integer(), name_hint = nameHint } },
		{ effects = pure, evidence = evidence }
	)
	return results[1]
end

local seven = addIntegerConstant("7", "seven")
local three = addIntegerConstant("3", "three")
local two = addIntegerConstant("2", "two")
local one = addIntegerConstant("1", "one")
local _, floorResults = builder:addInstruction(
	entry,
	LifterIR.Operation.binary("floor_divide", seven, three),
	{ { type = LifterIR.Types.integer(), name_hint = "floor_result" } },
	{ effects = pure, evidence = evidence }
)
local _, remainderResults = builder:addInstruction(
	entry,
	LifterIR.Operation.binary("modulo", seven, three),
	{ { type = LifterIR.Types.integer(), name_hint = "remainder_result" } },
	{ effects = pure, evidence = evidence }
)
local _, floorConditionResults = builder:addInstruction(
	entry,
	LifterIR.Operation.binary("equal", floorResults[1], two, "primitive"),
	{ { type = LifterIR.Types.boolean(), name_hint = "floor_matches" } },
	{ effects = pure, evidence = evidence }
)
local _, remainderConditionResults = builder:addInstruction(
	entry,
	LifterIR.Operation.binary("equal", remainderResults[1], one, "primitive"),
	{ { type = LifterIR.Types.boolean(), name_hint = "remainder_matches" } },
	{ effects = pure, evidence = evidence }
)
local _, numericConditionResults = builder:addInstruction(
	entry,
	LifterIR.Operation.binary("logical_and", floorConditionResults[1], remainderConditionResults[1], "primitive"),
	{ { type = LifterIR.Types.boolean(), name_hint = "numeric_matches" } },
	{ effects = pure, evidence = evidence }
)
local _, conditionResults = builder:addInstruction(
	entry,
	LifterIR.Operation.binary("logical_and", bitConditionResults[1], numericConditionResults[1], "primitive"),
	{ { type = LifterIR.Types.boolean(), name_hint = "all_match" } },
	{ effects = pure, evidence = evidence }
)
local _, matchedResults = builder:addInstruction(
	matched,
	LifterIR.Operation.constant(LifterIR.Literal.string("matched")),
	{ { type = LifterIR.Types.string(), name_hint = "matched_result" } },
	{ effects = pure, evidence = evidence }
)
local _, unreachableResults = builder:addInstruction(
	unreachable,
	LifterIR.Operation.constant(LifterIR.Literal.string("unreachable")),
	{ { type = LifterIR.Types.string(), name_hint = "unreachable_result" } },
	{ effects = pure, evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportedResults[1] }))
builder:finalizeBlock(
	entry,
	LifterIR.Terminator.branch(
		conditionResults[1],
		LifterIR.Edge(matched, {}),
		LifterIR.Edge(unreachable, {})
	)
)
builder:finalizeBlock(matched, LifterIR.Terminator.returnValues({ matchedResults[1] }))
builder:finalizeBlock(unreachable, LifterIR.Terminator.returnValues({ unreachableResults[1] }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(probe)

local encoded = LifterIR.encodeJson(builder:finish(), true)
local decoded = serde.decode("json", encoded)
assert(decoded.program_id == "generic-automatic-solver-promotion", "serialized program ID did not round-trip")
assert(#decoded.solver_terms == 0, "frontend fixture unexpectedly authored solver terms")
fs.writeFile(outputPath, encoded .. "\n")
