--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-loop-local-lexical-transfer")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-loop-local-lexical-transfer")
local evidence = { proof }
local pure = LifterIR.Effects.pure()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local worker = builder:reserveFunction({ name_hint = "worker", evidence = evidence })
local snapshotBody = builder:reserveFunction({
	name_hint = "snapshot",
	lexical_parent = worker,
	evidence = evidence,
})

local nextValue = builder:addParameter(worker, LifterIR.Types.functionValue(), "next_value")
local record = builder:addParameter(worker, LifterIR.Types.functionValue(), "record")
local recordFinal = builder:addParameter(worker, LifterIR.Types.functionValue(), "record_final")
local capturedIteration = builder:addValueCapture(snapshotBody, LifterIR.Types.integer(), "captured_iteration", evidence)

local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local workerEntry = builder:reserveBlock(worker, { name_hint = "entry", evidence = evidence })
local loopHeader = builder:reserveBlock(worker, { name_hint = "loop_header", evidence = evidence })
local loopBody = builder:reserveBlock(worker, { name_hint = "loop_body", evidence = evidence })
local loopExit = builder:reserveBlock(worker, { name_hint = "loop_exit", evidence = evidence })
local snapshotBlock = builder:reserveBlock(snapshotBody, { name_hint = "entry", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(worker, workerEntry)
builder:setFunctionEntry(snapshotBody, snapshotBlock)

local _, exportResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(worker),
	{ { type = LifterIR.Types.functionValue(), name_hint = "worker" } },
	{ effects = pure, evidence = evidence }
)
local exportedWorker = exportResults[1]

local _, nextResults = builder:addInstruction(
	loopBody,
	LifterIR.Operation.call(nextValue, {}, LifterIR.ResultArity.fixed(2)),
	{
		{ type = LifterIR.Types.boolean(), name_hint = "continue_loop" },
		{ type = LifterIR.Types.integer(), name_hint = "iteration" },
	},
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local continueLoop = nextResults[1]
local iteration = nextResults[2]
local _, closureResults = builder:addInstruction(
	loopBody,
	LifterIR.Operation.makeClosure(snapshotBody, { LifterIR.CaptureBinding.value(iteration) }),
	{ { type = LifterIR.Types.functionValue(), name_hint = "snapshot" } },
	{ effects = pure, evidence = evidence }
)
local snapshot = closureResults[1]
builder:addInstruction(
	loopBody,
	LifterIR.Operation.call(record, { snapshot }, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
builder:addInstruction(
	loopExit,
	LifterIR.Operation.call(recordFinal, { iteration }, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportedWorker }))
builder:finalizeBlock(workerEntry, LifterIR.Terminator.jump(LifterIR.Edge(loopHeader)))
builder:finalizeBlock(loopHeader, LifterIR.Terminator.jump(LifterIR.Edge(loopBody)))
builder:finalizeBlock(
	loopBody,
	LifterIR.Terminator.branch(
		continueLoop,
		LifterIR.Edge(loopHeader),
		LifterIR.Edge(loopExit)
	)
)
builder:finalizeBlock(loopExit, LifterIR.Terminator.returnValues({ iteration }))
builder:finalizeBlock(snapshotBlock, LifterIR.Terminator.returnValues({ capturedIteration }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(worker)
builder:finalizeFunction(snapshotBody)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
