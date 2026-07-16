--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

if process.args[1] == "audit" then
	local Audit = require("./irreducible_closure_audit")
	local inputPath = process.args[2]
	local resolvedPath = process.args[3]
	local reresolvedPath = process.args[4]
	local generatedPath = process.args[5]
	assert(inputPath ~= nil and resolvedPath ~= nil and reresolvedPath ~= nil and generatedPath ~= nil, "expected audit artifacts")
	Audit.run(inputPath, resolvedPath, reresolvedPath, generatedPath)
	return
end

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-irreducible-closure-captures")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-irreducible-closure-captures")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local integer = LifterIR.Types.integer()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local factory = builder:reserveFunction({ name_hint = "irreducible_closure_factory", evidence = evidence })
local closureBody = builder:reserveFunction({
	name_hint = "snapshot_counter",
	lexical_parent = factory,
	evidence = evidence,
})

local startSecondary = builder:addParameter(factory, LifterIR.Types.boolean(), "start_secondary")
local seed = builder:addParameter(factory, integer, "seed")
local initialState = builder:addParameter(factory, integer, "initial_state")
local sink = builder:addParameter(factory, LifterIR.Types.table(), "sink")
local delta = builder:addParameter(closureBody, integer, "delta")
local state = builder:addLocalPlace(factory, integer, "state", evidence)
local capturedSnapshot = builder:addValueCapture(closureBody, integer, "captured_snapshot", evidence)
local capturedState = builder:addPlaceCapture(closureBody, integer, "captured_state", evidence)

local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local entry = builder:reserveBlock(factory, { name_hint = "entry", evidence = evidence })
local primary = builder:reserveBlock(factory, { name_hint = "loop_header", evidence = evidence })
local secondary = builder:reserveBlock(factory, { name_hint = "closure_entry", evidence = evidence })
local exit = builder:reserveBlock(factory, { name_hint = "exit", evidence = evidence })
local closureBlock = builder:reserveBlock(closureBody, { name_hint = "entry", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(factory, entry)
builder:setFunctionEntry(closureBody, closureBlock)

local primaryCounter = builder:addBlockParameter(primary, integer, "counter")
local secondaryCounter = builder:addBlockParameter(secondary, integer, "snapshot_counter")
local exitCounter = builder:addBlockParameter(exit, integer, "final_counter")

local _, exportedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(factory),
	{ { type = LifterIR.Types.functionValue(), name_hint = "irreducible_closure_factory" } },
	{ effects = pure, evidence = evidence }
)

builder:addInstruction(
	entry,
	LifterIR.Operation.placeWrite(state, initialState),
	{},
	{ effects = LifterIR.Effects.placeWrite(), evidence = evidence }
)
local _, zeroResults = builder:addInstruction(
	entry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = integer, name_hint = "zero" } },
	{ effects = pure, evidence = evidence }
)
local _, entryOneResults = builder:addInstruction(
	entry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = integer, name_hint = "entry_one" } },
	{ effects = pure, evidence = evidence }
)

local _, primaryOneResults = builder:addInstruction(
	primary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = integer, name_hint = "one" } },
	{ effects = pure, evidence = evidence }
)
local _, continueResults = builder:addInstruction(
	primary,
	LifterIR.Operation.binary("less", primaryCounter, primaryOneResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "needs_closure" } },
	{ effects = pure, evidence = evidence }
)

local _, closureKeyResults = builder:addInstruction(
	secondary,
	LifterIR.Operation.constant(LifterIR.Literal.string("closure")),
	{ { type = LifterIR.Types.string(), name_hint = "closure_key" } },
	{ effects = pure, evidence = evidence }
)
local _, snapshotResults = builder:addInstruction(
	secondary,
	LifterIR.Operation.binary("add", seed, secondaryCounter),
	{ { type = integer, name_hint = "snapshot" } },
	{ effects = pure, evidence = evidence }
)
local _, closureResults = builder:addInstruction(
	secondary,
	LifterIR.Operation.makeClosure(closureBody, {
		LifterIR.CaptureBinding.value(snapshotResults[1]),
		LifterIR.CaptureBinding.place(state),
	}),
	{ { type = LifterIR.Types.functionValue(), name_hint = "snapshot_counter_closure" } },
	{ effects = pure, evidence = evidence }
)
builder:addInstruction(
	secondary,
	LifterIR.Operation.tableSet(sink, closureKeyResults[1], closureResults[1], "raw"),
	{},
	{ effects = LifterIR.Effects.rawTableWrite(), evidence = evidence }
)

local _, currentResults = builder:addInstruction(
	closureBlock,
	LifterIR.Operation.placeRead(capturedState),
	{ { type = integer, name_hint = "current_state" } },
	{ effects = LifterIR.Effects.placeRead(), evidence = evidence }
)
local _, nextResults = builder:addInstruction(
	closureBlock,
	LifterIR.Operation.binary("add", currentResults[1], delta),
	{ { type = integer, name_hint = "next_state" } },
	{ effects = pure, evidence = evidence }
)
builder:addInstruction(
	closureBlock,
	LifterIR.Operation.placeWrite(capturedState, nextResults[1]),
	{},
	{ effects = LifterIR.Effects.placeWrite(), evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportedResults[1] }))
builder:finalizeBlock(
	entry,
	LifterIR.Terminator.branch(
		startSecondary,
		LifterIR.Edge(secondary, { entryOneResults[1] }),
		LifterIR.Edge(primary, { zeroResults[1] })
	)
)
builder:finalizeBlock(
	primary,
	LifterIR.Terminator.branch(
		continueResults[1],
		LifterIR.Edge(secondary, { primaryOneResults[1] }),
		LifterIR.Edge(exit, { primaryCounter })
	)
)
builder:finalizeBlock(secondary, LifterIR.Terminator.jump(LifterIR.Edge(primary, { secondaryCounter })))
builder:finalizeBlock(exit, LifterIR.Terminator.returnValues({ exitCounter }))
builder:finalizeBlock(closureBlock, LifterIR.Terminator.returnValues({ capturedSnapshot, nextResults[1] }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(factory)
builder:finalizeFunction(closureBody)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
