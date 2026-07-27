--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-luau-table-access-modes")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-luau-table-access-modes")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local tableType = LifterIR.Types["table"]()
local callEffects = LifterIR.Effects.conservative({
	reads_memory = true,
	writes_memory = true,
	may_throw = true,
	may_yield = true,
	invokes_unknown_code = true,
})

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local probe = builder:reserveFunction({ name_hint = "probe_table_modes", evidence = evidence })
local fallback = builder:reserveFunction({ name_hint = "fallback", evidence = evidence })
builder:addParameter(fallback, tableType, "table_value")
builder:addParameter(fallback, LifterIR.Types.dynamic(), "missing_key")

local chunkBlock = builder:reserveBlock(chunk, { evidence = evidence })
local probeBlock = builder:reserveBlock(probe, { evidence = evidence })
local fallbackBlock = builder:reserveBlock(fallback, { evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(probe, probeBlock)
builder:setFunctionEntry(fallback, fallbackBlock)

local _, exportResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(probe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "probe" } },
	{ effects = pure, evidence = evidence }
)
local exportedProbe = exportResults[1]

local _, setmetatableResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.environmentGet(LifterIR.EnvironmentTarget.ambient(), "setmetatable"),
	{ { type = LifterIR.Types.functionValue(), name_hint = "setmetatable" } },
	{ effects = callEffects, evidence = evidence }
)
local setmetatableValue = setmetatableResults[1]
local _, targetResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.makeTable(),
	{ { type = tableType, name_hint = "target" } },
	{ effects = LifterIR.Effects.tableConstructor(), evidence = evidence }
)
local target = targetResults[1]
local _, metatableResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.makeTable(),
	{ { type = tableType, name_hint = "metatable" } },
	{ effects = LifterIR.Effects.tableConstructor(), evidence = evidence }
)
local metatableValue = metatableResults[1]
local _, fallbackReferenceResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.functionRef(fallback),
	{ { type = LifterIR.Types.functionValue(), name_hint = "fallback" } },
	{ effects = pure, evidence = evidence }
)
local fallbackReference = fallbackReferenceResults[1]
local _, indexKeyResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("__index")),
	{ { type = LifterIR.Types.string(), name_hint = "index_key" } },
	{ effects = pure, evidence = evidence }
)
local indexKey = indexKeyResults[1]
builder:addInstruction(
	probeBlock,
	LifterIR.Operation.tableSet(metatableValue, indexKey, fallbackReference, "semantic"),
	{},
	{ effects = LifterIR.Effects.semanticTableWrite(), evidence = evidence }
)
builder:addInstruction(
	probeBlock,
	LifterIR.Operation.call(setmetatableValue, { target, metatableValue }, LifterIR.ResultArity.fixed(1)),
	{ { type = tableType, name_hint = "configured" } },
	{ effects = callEffects, evidence = evidence }
)
local _, missingKeyResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("missing")),
	{ { type = LifterIR.Types.string(), name_hint = "missing_key" } },
	{ effects = pure, evidence = evidence }
)
local missingKey = missingKeyResults[1]
local rawInstruction, rawResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.tableGet(target, missingKey, "raw"),
	{ { type = LifterIR.Types.nilValue(), name_hint = "raw_value" } },
	{ effects = LifterIR.Effects.rawTableRead(), evidence = evidence }
)
local rawValue = rawResults[1]
local noDispatchPredicate = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.semanticAtom(LifterIR.SemanticAtom.noMetamethodDispatch(rawInstruction))
)
local noDispatchClaim = builder:addClaim(
	LifterIR.Entity.instruction(rawInstruction),
	noDispatchPredicate,
	"unproven",
	false,
	evidence,
	nil,
	LifterIR.ClaimPurpose.noMetamethodDispatch(LifterIR.Effects.rawTableRead())
)
builder:addInstructionClaim(rawInstruction, noDispatchClaim)
local _, semanticResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.tableGet(target, missingKey, "semantic"),
	{ { type = LifterIR.Types.integer(), name_hint = "semantic_value" } },
	{ effects = LifterIR.Effects.semanticTableRead(), evidence = evidence }
)
local semanticValue = semanticResults[1]
local _, nilResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.constant(LifterIR.Literal.nilValue()),
	{ { type = LifterIR.Types.nilValue(), name_hint = "nil_value" } },
	{ effects = pure, evidence = evidence }
)
local nilValue = nilResults[1]
local _, expectedResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("99")),
	{ { type = LifterIR.Types.integer(), name_hint = "expected" } },
	{ effects = pure, evidence = evidence }
)
local expected = expectedResults[1]
local keyedFields: { any } = table.create(256)
for index = 0, 255 do
	local _, keyedKeyResults = builder:addInstruction(
		probeBlock,
		LifterIR.Operation.constant(LifterIR.Literal.integer(tostring(index))),
		{ { type = LifterIR.Types.integer(), name_hint = `keyed_key_{index}` } },
		{ effects = pure, evidence = evidence }
	)
	local _, keyedValueResults = builder:addInstruction(
		probeBlock,
		LifterIR.Operation.constant(LifterIR.Literal.integer(tostring(index * 3 + 7))),
		{ { type = LifterIR.Types.integer(), name_hint = `keyed_value_{index}` } },
		{ effects = pure, evidence = evidence }
	)
	keyedFields[index + 1] = LifterIR.TableConstructorField.keyed(keyedKeyResults[1], keyedValueResults[1])
end
local _, keyedTableResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.makeTableLiteral(keyedFields),
	{ { type = tableType, name_hint = "keyed_values" } },
	{ effects = LifterIR.Effects.tableConstructor(), evidence = evidence }
)
local keyedTable = keyedTableResults[1]
local _, firstKeyResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = LifterIR.Types.integer(), name_hint = "first_key" } },
	{ effects = pure, evidence = evidence }
)
local _, lastKeyResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("255")),
	{ { type = LifterIR.Types.integer(), name_hint = "last_key" } },
	{ effects = pure, evidence = evidence }
)
local _, firstValueResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.tableGet(keyedTable, firstKeyResults[1], "raw"),
	{ { type = LifterIR.Types.integer(), name_hint = "first_keyed_value" } },
	{ effects = LifterIR.Effects.rawTableRead(), evidence = evidence }
)
local _, lastValueResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.tableGet(keyedTable, lastKeyResults[1], "raw"),
	{ { type = LifterIR.Types.integer(), name_hint = "last_keyed_value" } },
	{ effects = LifterIR.Effects.rawTableRead(), evidence = evidence }
)
local _, firstExpectedResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("7")),
	{ { type = LifterIR.Types.integer(), name_hint = "first_keyed_expected" } },
	{ effects = pure, evidence = evidence }
)
local _, lastExpectedResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("772")),
	{ { type = LifterIR.Types.integer(), name_hint = "last_keyed_expected" } },
	{ effects = pure, evidence = evidence }
)
local _, firstKeyedCheckResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("equal", firstValueResults[1], firstExpectedResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "first_keyed_matches" } },
	{ effects = pure, evidence = evidence }
)
local _, lastKeyedCheckResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("equal", lastValueResults[1], lastExpectedResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "last_keyed_matches" } },
	{ effects = pure, evidence = evidence }
)
local _, keyedCheckResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("logical_and", firstKeyedCheckResults[1], lastKeyedCheckResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "keyed_constructor_passed" } },
	{ effects = pure, evidence = evidence }
)
local keyedConstructorPassed = keyedCheckResults[1]
local _, environmentResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.makeTable(),
	{ { type = tableType, name_hint = "environment" } },
	{ effects = LifterIR.Effects.tableConstructor(), evidence = evidence }
)
local environmentValue = environmentResults[1]
builder:addInstruction(
	probeBlock,
	LifterIR.Operation.environmentSet(
		LifterIR.EnvironmentTarget.value(environmentValue),
		"not a source identifier",
		expected,
		"raw"
	),
	{},
	{ effects = LifterIR.Effects.rawTableWrite(), evidence = evidence }
)
local _, environmentReadResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.environmentGet(
		LifterIR.EnvironmentTarget.value(environmentValue),
		"not a source identifier",
		"raw"
	),
	{ { type = LifterIR.Types.integer(), name_hint = "environment_value" } },
	{ effects = LifterIR.Effects.rawTableRead(), evidence = evidence }
)
local environmentRead = environmentReadResults[1]
builder:addInstruction(
	probeBlock,
	LifterIR.Operation.environmentSet(
		LifterIR.EnvironmentTarget.ambient(),
		"not a source identifier",
		expected,
		"semantic"
	),
	{},
	{ effects = LifterIR.Effects.semanticTableWrite(), evidence = evidence }
)
local _, ambientEnvironmentReadResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.environmentGet(
		LifterIR.EnvironmentTarget.ambient(),
		"not a source identifier",
		"semantic"
	),
	{ { type = LifterIR.Types.integer(), name_hint = "ambient_environment_value" } },
	{ effects = LifterIR.Effects.semanticTableRead(), evidence = evidence }
)
local ambientEnvironmentRead = ambientEnvironmentReadResults[1]
local _, rawCheckResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("equal", rawValue, nilValue),
	{ { type = LifterIR.Types.boolean(), name_hint = "raw_bypassed" } },
	{ effects = pure, evidence = evidence }
)
local rawBypassed = rawCheckResults[1]
local _, semanticCheckResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("equal", semanticValue, expected),
	{ { type = LifterIR.Types.boolean(), name_hint = "semantic_dispatched" } },
	{ effects = pure, evidence = evidence }
)
local semanticDispatched = semanticCheckResults[1]
local _, environmentCheckResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("equal", environmentRead, expected),
	{ { type = LifterIR.Types.boolean(), name_hint = "environment_round_trip" } },
	{ effects = pure, evidence = evidence }
)
local environmentRoundTrip = environmentCheckResults[1]
local _, ambientEnvironmentCheckResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("equal", ambientEnvironmentRead, expected),
	{ { type = LifterIR.Types.boolean(), name_hint = "ambient_environment_round_trip" } },
	{ effects = pure, evidence = evidence }
)
local ambientEnvironmentRoundTrip = ambientEnvironmentCheckResults[1]
local _, combinedResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("logical_and", rawBypassed, semanticDispatched),
	{ { type = LifterIR.Types.boolean(), name_hint = "table_modes_passed" } },
	{ effects = pure, evidence = evidence }
)
local tableModesPassed = combinedResults[1]
local _, environmentCombinedResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("logical_and", tableModesPassed, environmentRoundTrip),
	{ { type = LifterIR.Types.boolean(), name_hint = "explicit_environment_passed" } },
	{ effects = pure, evidence = evidence }
)
local explicitEnvironmentPassed = environmentCombinedResults[1]
local _, finalResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("logical_and", explicitEnvironmentPassed, ambientEnvironmentRoundTrip),
	{ { type = LifterIR.Types.boolean(), name_hint = "passed" } },
	{ effects = pure, evidence = evidence }
)
local _, completeResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("logical_and", finalResults[1], keyedConstructorPassed),
	{ { type = LifterIR.Types.boolean(), name_hint = "passed" } },
	{ effects = pure, evidence = evidence }
)
local passed = completeResults[1]

local _, fallbackResults = builder:addInstruction(
	fallbackBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("99")),
	{ { type = LifterIR.Types.integer(), name_hint = "fallback_value" } },
	{ effects = pure, evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportedProbe }))
builder:finalizeBlock(probeBlock, LifterIR.Terminator.returnValues({ passed }))
builder:finalizeBlock(fallbackBlock, LifterIR.Terminator.returnValues({ fallbackResults[1] }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(probe)
builder:finalizeFunction(fallback)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
