--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-iteration-exit-transfer")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-iteration-exit-transfer")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local dynamic = LifterIR.Types.dynamic()
local boolean = LifterIR.Types.boolean()
local number = LifterIR.Types.number()
local functionValue = LifterIR.Types.functionValue()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local numericWorker = builder:reserveFunction({ name_hint = "numeric_exit_transfer", evidence = evidence })
local genericWorker = builder:reserveFunction({ name_hint = "generic_exit_transfer", evidence = evidence })
local nestedWorker = builder:reserveFunction({ name_hint = "nested_numeric_exit_transfer", evidence = evidence })

local numericRun = builder:addParameter(numericWorker, boolean, "run_loop")
local numericInitial = builder:addParameter(numericWorker, number, "initial")
local numericLimit = builder:addParameter(numericWorker, number, "limit")
local numericStep = builder:addParameter(numericWorker, number, "step")
local numericLoopMarker = builder:addParameter(numericWorker, dynamic, "loop_marker")
local numericBypassMarker = builder:addParameter(numericWorker, dynamic, "bypass_marker")
local numericObserver = builder:addParameter(numericWorker, functionValue, "observer")

local genericRun = builder:addParameter(genericWorker, boolean, "run_loop")
local genericIterator = builder:addParameter(genericWorker, dynamic, "iterator")
local genericState = builder:addParameter(genericWorker, dynamic, "state")
local genericControl = builder:addParameter(genericWorker, dynamic, "control")
local genericLoopMarker = builder:addParameter(genericWorker, dynamic, "loop_marker")
local genericBypassMarker = builder:addParameter(genericWorker, dynamic, "bypass_marker")
local genericObserver = builder:addParameter(genericWorker, functionValue, "observer")

local nestedOuterInitial = builder:addParameter(nestedWorker, number, "outer_initial")
local nestedOuterLimit = builder:addParameter(nestedWorker, number, "outer_limit")
local nestedOuterStep = builder:addParameter(nestedWorker, number, "outer_step")
local nestedInnerInitial = builder:addParameter(nestedWorker, number, "inner_initial")
local nestedInnerLimit = builder:addParameter(nestedWorker, number, "inner_limit")
local nestedInnerStep = builder:addParameter(nestedWorker, number, "inner_step")
local nestedMakeMarker = builder:addParameter(nestedWorker, functionValue, "make_marker")
local nestedObserver = builder:addParameter(nestedWorker, functionValue, "observer")
local nestedAfter = builder:addParameter(nestedWorker, functionValue, "after_inner")

local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local numericEntry = builder:reserveBlock(numericWorker, { name_hint = "entry", evidence = evidence })
local numericHeader = builder:reserveBlock(numericWorker, { name_hint = "header", evidence = evidence })
local numericBody = builder:reserveBlock(numericWorker, { name_hint = "body", evidence = evidence })
local numericExit = builder:reserveBlock(numericWorker, { name_hint = "exit", evidence = evidence })
local genericEntry = builder:reserveBlock(genericWorker, { name_hint = "entry", evidence = evidence })
local genericHeader = builder:reserveBlock(genericWorker, { name_hint = "header", evidence = evidence })
local genericBody = builder:reserveBlock(genericWorker, { name_hint = "body", evidence = evidence })
local genericExit = builder:reserveBlock(genericWorker, { name_hint = "exit", evidence = evidence })
local nestedEntry = builder:reserveBlock(nestedWorker, { name_hint = "entry", evidence = evidence })
local nestedOuterHeader = builder:reserveBlock(nestedWorker, { name_hint = "outer_header", evidence = evidence })
local nestedOuterBody = builder:reserveBlock(nestedWorker, { name_hint = "outer_body", evidence = evidence })
local nestedInnerHeader = builder:reserveBlock(nestedWorker, { name_hint = "inner_header", evidence = evidence })
local nestedInnerBody = builder:reserveBlock(nestedWorker, { name_hint = "inner_body", evidence = evidence })
local nestedInnerExit = builder:reserveBlock(nestedWorker, { name_hint = "inner_exit", evidence = evidence })
local nestedExit = builder:reserveBlock(nestedWorker, { name_hint = "exit", evidence = evidence })

builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(numericWorker, numericEntry)
builder:setFunctionEntry(genericWorker, genericEntry)
builder:setFunctionEntry(nestedWorker, nestedEntry)

local numericHeaderControl = builder:addBlockParameter(numericHeader, number, "header_control")
local numericHeaderLimit = builder:addBlockParameter(numericHeader, number, "header_limit")
local numericHeaderStep = builder:addBlockParameter(numericHeader, number, "header_step")
local numericHeaderInitial = builder:addBlockParameter(numericHeader, boolean, "header_initial")
local numericIndex = builder:addBlockParameter(numericBody, number, "numeric_index")
local numericExitMarker = builder:addBlockParameter(numericExit, dynamic, "numeric_exit_marker")

local genericHeaderIterator = builder:addBlockParameter(genericHeader, dynamic, "header_iterator")
local genericHeaderState = builder:addBlockParameter(genericHeader, dynamic, "header_state")
local genericHeaderControl = builder:addBlockParameter(genericHeader, dynamic, "header_control")
local genericHeaderInitial = builder:addBlockParameter(genericHeader, boolean, "header_initial")
local genericIndex = builder:addBlockParameter(genericBody, dynamic, "generic_index")
local genericValue = builder:addBlockParameter(genericBody, dynamic, "generic_value")
local genericExitMarker = builder:addBlockParameter(genericExit, dynamic, "generic_exit_marker")

local nestedOuterControl = builder:addBlockParameter(nestedOuterHeader, number, "outer_control")
local nestedOuterBound = builder:addBlockParameter(nestedOuterHeader, number, "outer_limit")
local nestedOuterStride = builder:addBlockParameter(nestedOuterHeader, number, "outer_step")
local nestedOuterFirst = builder:addBlockParameter(nestedOuterHeader, boolean, "outer_initial")
local nestedOuterIndex = builder:addBlockParameter(nestedOuterBody, number, "outer_index")
local nestedInnerControl = builder:addBlockParameter(nestedInnerHeader, number, "inner_control")
local nestedInnerBound = builder:addBlockParameter(nestedInnerHeader, number, "inner_limit")
local nestedInnerStride = builder:addBlockParameter(nestedInnerHeader, number, "inner_step")
local nestedInnerFirst = builder:addBlockParameter(nestedInnerHeader, boolean, "inner_initial")
local nestedInnerIndex = builder:addBlockParameter(nestedInnerBody, number, "inner_index")
local nestedExitMarker = builder:addBlockParameter(nestedInnerExit, dynamic, "inner_exit_marker")
local nestedExitOuterIndex = builder:addBlockParameter(nestedInnerExit, number, "inner_exit_outer_index")

local _, numericExport = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(numericWorker),
	{ { type = functionValue, name_hint = "numeric_exit_transfer" } },
	{ effects = pure, evidence = evidence }
)
local _, genericExport = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(genericWorker),
	{ { type = functionValue, name_hint = "generic_exit_transfer" } },
	{ effects = pure, evidence = evidence }
)
local _, nestedExport = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(nestedWorker),
	{ { type = functionValue, name_hint = "nested_numeric_exit_transfer" } },
	{ effects = pure, evidence = evidence }
)

local _, numericTrue = builder:addInstruction(
	numericEntry,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(true)),
	{ { type = boolean, name_hint = "numeric_initial_transition" } },
	{ effects = pure, evidence = evidence }
)
local _, numericFalse = builder:addInstruction(
	numericEntry,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
	{ { type = boolean, name_hint = "numeric_later_transition" } },
	{ effects = pure, evidence = evidence }
)
local _, numericTransition = builder:addInstruction(
	numericHeader,
	LifterIR.Operation.numericForNext(numericHeaderControl, numericHeaderLimit, numericHeaderStep, numericHeaderInitial),
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

local _, genericTrue = builder:addInstruction(
	genericEntry,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(true)),
	{ { type = boolean, name_hint = "generic_initial_transition" } },
	{ effects = pure, evidence = evidence }
)
local _, genericFalse = builder:addInstruction(
	genericEntry,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
	{ { type = boolean, name_hint = "generic_later_transition" } },
	{ effects = pure, evidence = evidence }
)
local _, genericTransition = builder:addInstruction(
	genericHeader,
	LifterIR.Operation.genericForNext(genericHeaderIterator, genericHeaderState, genericHeaderControl, genericHeaderInitial, 2),
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

local _, nestedOuterTrue = builder:addInstruction(
	nestedEntry,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(true)),
	{ { type = boolean, name_hint = "outer_initial_transition" } },
	{ effects = pure, evidence = evidence }
)
local _, nestedOuterFalse = builder:addInstruction(
	nestedEntry,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
	{ { type = boolean, name_hint = "outer_later_transition" } },
	{ effects = pure, evidence = evidence }
)
local _, nestedInnerTrue = builder:addInstruction(
	nestedOuterBody,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(true)),
	{ { type = boolean, name_hint = "inner_initial_transition" } },
	{ effects = pure, evidence = evidence }
)
local _, nestedInnerFalse = builder:addInstruction(
	nestedOuterBody,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
	{ { type = boolean, name_hint = "inner_later_transition" } },
	{ effects = pure, evidence = evidence }
)
local _, nestedOuterTransition = builder:addInstruction(
	nestedOuterHeader,
	LifterIR.Operation.numericForNext(nestedOuterControl, nestedOuterBound, nestedOuterStride, nestedOuterFirst),
	{
		{ type = boolean, name_hint = "outer_has_value" },
		{ type = number, name_hint = "outer_normalized_limit" },
		{ type = number, name_hint = "outer_normalized_step" },
		{ type = number, name_hint = "outer_next_control" },
	},
	{ effects = LifterIR.Effects.numericForNext(), evidence = evidence }
)
local _, nestedMarker = builder:addInstruction(
	nestedOuterBody,
	LifterIR.Operation.call(nestedMakeMarker, { nestedOuterIndex }, LifterIR.ResultArity.fixed(1)),
	{ { type = dynamic, name_hint = "iteration_marker" } },
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local _, nestedInnerTransition = builder:addInstruction(
	nestedInnerHeader,
	LifterIR.Operation.numericForNext(nestedInnerControl, nestedInnerBound, nestedInnerStride, nestedInnerFirst),
	{
		{ type = boolean, name_hint = "inner_has_value" },
		{ type = number, name_hint = "inner_normalized_limit" },
		{ type = number, name_hint = "inner_normalized_step" },
		{ type = number, name_hint = "inner_next_control" },
	},
	{ effects = LifterIR.Effects.numericForNext(), evidence = evidence }
)
builder:addInstruction(
	nestedInnerBody,
	LifterIR.Operation.call(nestedObserver, { nestedOuterIndex, nestedInnerIndex }, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
builder:addInstruction(
	nestedInnerExit,
	LifterIR.Operation.call(nestedAfter, { nestedExitMarker, nestedExitOuterIndex }, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ numericExport[1], genericExport[1], nestedExport[1] }))
builder:finalizeBlock(
	numericEntry,
	LifterIR.Terminator.branch(
		numericRun,
		LifterIR.Edge(numericHeader, { numericInitial, numericLimit, numericStep, numericTrue[1] }),
		LifterIR.Edge(numericExit, { numericBypassMarker })
	)
)
builder:finalizeBlock(
	numericHeader,
	LifterIR.Terminator.branch(
		numericTransition[1],
		LifterIR.Edge(numericBody, { numericTransition[4] }),
		LifterIR.Edge(numericExit, { numericLoopMarker })
	)
)
builder:finalizeBlock(
	numericBody,
	LifterIR.Terminator.jump(LifterIR.Edge(numericHeader, {
		numericTransition[4],
		numericTransition[2],
		numericTransition[3],
		numericFalse[1],
	}))
)
builder:finalizeBlock(numericExit, LifterIR.Terminator.returnValues({ numericExitMarker }))

builder:finalizeBlock(
	genericEntry,
	LifterIR.Terminator.branch(
		genericRun,
		LifterIR.Edge(genericHeader, { genericIterator, genericState, genericControl, genericTrue[1] }),
		LifterIR.Edge(genericExit, { genericBypassMarker })
	)
)
builder:finalizeBlock(
	genericHeader,
	LifterIR.Terminator.branch(
		genericTransition[1],
		LifterIR.Edge(genericBody, { genericTransition[4], genericTransition[5] }),
		LifterIR.Edge(genericExit, { genericLoopMarker })
	)
)
builder:finalizeBlock(
	genericBody,
	LifterIR.Terminator.jump(LifterIR.Edge(genericHeader, {
		genericTransition[2],
		genericTransition[3],
		genericTransition[4],
		genericFalse[1],
	}))
)
builder:finalizeBlock(genericExit, LifterIR.Terminator.returnValues({ genericExitMarker }))

builder:finalizeBlock(
	nestedEntry,
	LifterIR.Terminator.jump(LifterIR.Edge(nestedOuterHeader, {
		nestedOuterInitial,
		nestedOuterLimit,
		nestedOuterStep,
		nestedOuterTrue[1],
	}))
)
builder:finalizeBlock(
	nestedOuterHeader,
	LifterIR.Terminator.branch(
		nestedOuterTransition[1],
		LifterIR.Edge(nestedOuterBody, { nestedOuterTransition[4] }),
		LifterIR.Edge(nestedExit, {})
	)
)
builder:finalizeBlock(
	nestedOuterBody,
	LifterIR.Terminator.jump(LifterIR.Edge(nestedInnerHeader, {
		nestedInnerInitial,
		nestedInnerLimit,
		nestedInnerStep,
		nestedInnerTrue[1],
	}))
)
builder:finalizeBlock(
	nestedInnerHeader,
	LifterIR.Terminator.branch(
		nestedInnerTransition[1],
		LifterIR.Edge(nestedInnerBody, { nestedInnerTransition[4] }),
		LifterIR.Edge(nestedInnerExit, { nestedMarker[1], nestedOuterIndex })
	)
)
builder:finalizeBlock(
	nestedInnerBody,
	LifterIR.Terminator.jump(LifterIR.Edge(nestedInnerHeader, {
		nestedInnerTransition[4],
		nestedInnerTransition[2],
		nestedInnerTransition[3],
		nestedInnerFalse[1],
	}))
)
builder:finalizeBlock(
	nestedInnerExit,
	LifterIR.Terminator.jump(LifterIR.Edge(nestedOuterHeader, {
		nestedOuterTransition[4],
		nestedOuterTransition[2],
		nestedOuterTransition[3],
		nestedOuterFalse[1],
	}))
)
builder:finalizeBlock(nestedExit, LifterIR.Terminator.returnValues({}))

builder:finalizeFunction(chunk)
builder:finalizeFunction(numericWorker)
builder:finalizeFunction(genericWorker)
builder:finalizeFunction(nestedWorker)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
