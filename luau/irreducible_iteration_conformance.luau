--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

if process.args[1] == "audit" then
	local Audit = require("./irreducible_iteration_audit")
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

local builder = LifterIR.Builder.new("generic-irreducible-iteration-convergence")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-irreducible-iteration-convergence")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local dynamic = LifterIR.Types.dynamic()
local boolean = LifterIR.Types.boolean()
local number = LifterIR.Types.number()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local numericWorker = builder:reserveFunction({ name_hint = "irreducible_numeric_worker", evidence = evidence })
local genericWorker = builder:reserveFunction({ name_hint = "irreducible_generic_worker", evidence = evidence })

local numericStartLatch = builder:addParameter(numericWorker, boolean, "start_latch")
local numericInitial = builder:addParameter(numericWorker, number, "initial")
local numericLimit = builder:addParameter(numericWorker, number, "limit")
local numericStep = builder:addParameter(numericWorker, number, "step")
local numericObserver = builder:addParameter(numericWorker, LifterIR.Types.functionValue(), "observer")
local numericSelector = builder:addParameter(numericWorker, LifterIR.Types.functionValue(), "selector")

local genericStartLatch = builder:addParameter(genericWorker, boolean, "start_latch")
local genericIterator = builder:addParameter(genericWorker, dynamic, "iterator")
local genericState = builder:addParameter(genericWorker, dynamic, "state")
local genericControl = builder:addParameter(genericWorker, dynamic, "control")
local genericObserver = builder:addParameter(genericWorker, LifterIR.Types.functionValue(), "observer")
local genericSelector = builder:addParameter(genericWorker, LifterIR.Types.functionValue(), "selector")

local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local numericEntry = builder:reserveBlock(numericWorker, { name_hint = "entry", evidence = evidence })
local numericLatch = builder:reserveBlock(numericWorker, { name_hint = "numeric_forwarding_latch_1", evidence = evidence })
local numericSecondLatch = builder:reserveBlock(numericWorker, { name_hint = "numeric_forwarding_latch_2", evidence = evidence })
local numericHeader = builder:reserveBlock(numericWorker, { name_hint = "numeric_header", evidence = evidence })
local numericBody = builder:reserveBlock(numericWorker, { name_hint = "numeric_body", evidence = evidence })
local numericExit = builder:reserveBlock(numericWorker, { name_hint = "numeric_exit", evidence = evidence })
local genericEntry = builder:reserveBlock(genericWorker, { name_hint = "entry", evidence = evidence })
local genericLatch = builder:reserveBlock(genericWorker, { name_hint = "generic_forwarding_latch_1", evidence = evidence })
local genericSecondLatch = builder:reserveBlock(genericWorker, { name_hint = "generic_forwarding_latch_2", evidence = evidence })
local genericHeader = builder:reserveBlock(genericWorker, { name_hint = "generic_header", evidence = evidence })
local genericBody = builder:reserveBlock(genericWorker, { name_hint = "generic_body", evidence = evidence })
local genericExit = builder:reserveBlock(genericWorker, { name_hint = "generic_exit", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(numericWorker, numericEntry)
builder:setFunctionEntry(genericWorker, genericEntry)

local numericLatchControl = builder:addBlockParameter(numericLatch, number, "latch_control")
local numericLatchLimit = builder:addBlockParameter(numericLatch, number, "latch_limit")
local numericLatchStep = builder:addBlockParameter(numericLatch, number, "latch_step")
local numericLatchInitial = builder:addBlockParameter(numericLatch, boolean, "latch_initial")
local numericSecondLimit = builder:addBlockParameter(numericSecondLatch, number, "second_latch_limit")
local numericSecondControl = builder:addBlockParameter(numericSecondLatch, number, "second_latch_control")
local numericSecondStep = builder:addBlockParameter(numericSecondLatch, number, "second_latch_step")
local numericSecondInitial = builder:addBlockParameter(numericSecondLatch, boolean, "second_latch_initial")
local numericHeaderControl = builder:addBlockParameter(numericHeader, number, "header_control")
local numericHeaderLimit = builder:addBlockParameter(numericHeader, number, "header_limit")
local numericHeaderStep = builder:addBlockParameter(numericHeader, number, "header_step")
local numericHeaderInitial = builder:addBlockParameter(numericHeader, boolean, "header_initial")
local numericIndex = builder:addBlockParameter(numericBody, number, "numeric_index")

local genericLatchIterator = builder:addBlockParameter(genericLatch, dynamic, "latch_iterator")
local genericLatchState = builder:addBlockParameter(genericLatch, dynamic, "latch_state")
local genericLatchControl = builder:addBlockParameter(genericLatch, dynamic, "latch_control")
local genericLatchInitial = builder:addBlockParameter(genericLatch, boolean, "latch_initial")
local genericSecondState = builder:addBlockParameter(genericSecondLatch, dynamic, "second_latch_state")
local genericSecondIterator = builder:addBlockParameter(genericSecondLatch, dynamic, "second_latch_iterator")
local genericSecondControl = builder:addBlockParameter(genericSecondLatch, dynamic, "second_latch_control")
local genericSecondInitial = builder:addBlockParameter(genericSecondLatch, boolean, "second_latch_initial")
local genericHeaderIterator = builder:addBlockParameter(genericHeader, dynamic, "header_iterator")
local genericHeaderState = builder:addBlockParameter(genericHeader, dynamic, "header_state")
local genericHeaderControl = builder:addBlockParameter(genericHeader, dynamic, "header_control")
local genericHeaderInitial = builder:addBlockParameter(genericHeader, boolean, "header_initial")
local genericIndex = builder:addBlockParameter(genericBody, dynamic, "generic_index")
local genericValue = builder:addBlockParameter(genericBody, dynamic, "generic_value")

local _, numericExportResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(numericWorker),
	{ { type = LifterIR.Types.functionValue(), name_hint = "irreducible_numeric_worker" } },
	{ effects = pure, evidence = evidence }
)
local _, genericExportResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(genericWorker),
	{ { type = LifterIR.Types.functionValue(), name_hint = "irreducible_generic_worker" } },
	{ effects = pure, evidence = evidence }
)

local _, numericTrueResults = builder:addInstruction(
	numericEntry,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(true)),
	{ { type = boolean, name_hint = "numeric_initial_transition" } },
	{ effects = pure, evidence = evidence }
)
local _, numericSelectorResults = builder:addInstruction(
	numericEntry,
	LifterIR.Operation.call(numericSelector, { numericStartLatch }, LifterIR.ResultArity.fixed(1)),
	{ { type = boolean, name_hint = "selected_numeric_entry" } },
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local _, numericFalseResults = builder:addInstruction(
	numericEntry,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
	{ { type = boolean, name_hint = "numeric_later_transition" } },
	{ effects = pure, evidence = evidence }
)
local _, numericTransition = builder:addInstruction(
	numericHeader,
	LifterIR.Operation.numericForNext(
		numericHeaderControl,
		numericHeaderLimit,
		numericHeaderStep,
		numericHeaderInitial
	),
	{
		{ type = boolean, name_hint = "numeric_has_value" },
		{ type = number, name_hint = "numeric_normalized_limit" },
		{ type = number, name_hint = "numeric_normalized_step" },
		{ type = number, name_hint = "numeric_next_control" },
	},
	{ effects = LifterIR.Effects.numericForNext(), evidence = evidence }
)
builder:addInstruction(
	numericBody,
	LifterIR.Operation.call(numericObserver, { numericIndex }, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)

local _, genericTrueResults = builder:addInstruction(
	genericEntry,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(true)),
	{ { type = boolean, name_hint = "generic_initial_transition" } },
	{ effects = pure, evidence = evidence }
)
local _, genericSelectorResults = builder:addInstruction(
	genericEntry,
	LifterIR.Operation.call(genericSelector, { genericStartLatch }, LifterIR.ResultArity.fixed(1)),
	{ { type = boolean, name_hint = "selected_generic_entry" } },
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local _, genericFalseResults = builder:addInstruction(
	genericEntry,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
	{ { type = boolean, name_hint = "generic_later_transition" } },
	{ effects = pure, evidence = evidence }
)
local _, genericTransition = builder:addInstruction(
	genericHeader,
	LifterIR.Operation.genericForNext(
		genericHeaderIterator,
		genericHeaderState,
		genericHeaderControl,
		genericHeaderInitial,
		2
	),
	{
		{ type = boolean, name_hint = "generic_has_value" },
		{ type = dynamic, name_hint = "generic_prepared_iterator" },
		{ type = dynamic, name_hint = "generic_prepared_state" },
		{ type = dynamic, name_hint = "generic_index" },
		{ type = dynamic, name_hint = "generic_value" },
	},
	{ effects = LifterIR.Effects.genericForNext(), evidence = evidence }
)
builder:addInstruction(
	genericBody,
	LifterIR.Operation.call(genericObserver, { genericIndex, genericValue }, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ numericExportResults[1], genericExportResults[1] }))
builder:finalizeBlock(
	numericEntry,
	LifterIR.Terminator.branch(
		numericSelectorResults[1],
		LifterIR.Edge(numericLatch, { numericInitial, numericLimit, numericStep, numericTrueResults[1] }),
		LifterIR.Edge(numericHeader, { numericInitial, numericLimit, numericStep, numericTrueResults[1] })
	)
)
builder:finalizeBlock(
	numericLatch,
	LifterIR.Terminator.jump(LifterIR.Edge(numericSecondLatch, {
		numericLatchLimit,
		numericLatchControl,
		numericLatchStep,
		numericLatchInitial,
	}))
)
builder:finalizeBlock(
	numericSecondLatch,
	LifterIR.Terminator.jump(LifterIR.Edge(numericHeader, {
		numericSecondControl,
		numericSecondLimit,
		numericSecondStep,
		numericSecondInitial,
	}))
)
builder:finalizeBlock(
	numericHeader,
	LifterIR.Terminator.branch(
		numericTransition[1],
		LifterIR.Edge(numericBody, { numericTransition[4] }),
		LifterIR.Edge(numericExit)
	)
)
builder:finalizeBlock(
	numericBody,
	LifterIR.Terminator.jump(LifterIR.Edge(numericLatch, {
		numericTransition[4],
		numericTransition[2],
		numericTransition[3],
		numericFalseResults[1],
	}))
)
builder:finalizeBlock(
	numericExit,
	LifterIR.Terminator.returnValues({ numericTransition[2], numericTransition[3] })
)

builder:finalizeBlock(
	genericEntry,
	LifterIR.Terminator.branch(
		genericSelectorResults[1],
		LifterIR.Edge(genericLatch, { genericIterator, genericState, genericControl, genericTrueResults[1] }),
		LifterIR.Edge(genericHeader, { genericIterator, genericState, genericControl, genericTrueResults[1] })
	)
)
builder:finalizeBlock(
	genericLatch,
	LifterIR.Terminator.jump(LifterIR.Edge(genericSecondLatch, {
		genericLatchState,
		genericLatchIterator,
		genericLatchControl,
		genericLatchInitial,
	}))
)
builder:finalizeBlock(
	genericSecondLatch,
	LifterIR.Terminator.jump(LifterIR.Edge(genericHeader, {
		genericSecondIterator,
		genericSecondState,
		genericSecondControl,
		genericSecondInitial,
	}))
)
builder:finalizeBlock(
	genericHeader,
	LifterIR.Terminator.branch(
		genericTransition[1],
		LifterIR.Edge(genericBody, { genericTransition[4], genericTransition[5] }),
		LifterIR.Edge(genericExit)
	)
)
builder:finalizeBlock(
	genericBody,
	LifterIR.Terminator.jump(LifterIR.Edge(genericLatch, {
		genericTransition[2],
		genericTransition[3],
		genericTransition[4],
		genericFalseResults[1],
	}))
)
builder:finalizeBlock(genericExit, LifterIR.Terminator.returnValues({}))

builder:finalizeFunction(chunk)
builder:finalizeFunction(numericWorker)
builder:finalizeFunction(genericWorker)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
