--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-fixed-entry-parameters")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-fixed-entry-parameters")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local dynamic = LifterIR.Types.dynamic()

local chunk = builder:reserveFunction({ name_hint = "chunk", is_variadic = true, evidence = evidence })
local probeBody = builder:reserveFunction({
	name_hint = "probe",
	lexical_parent = chunk,
	evidence = evidence,
})

local first = builder:addParameter(chunk, dynamic, "first")
local second = builder:addParameter(chunk, dynamic, "second")
local capturedFirst = builder:addValueCapture(probeBody, dynamic, "captured_first", evidence)
local capturedSecond = builder:addValueCapture(probeBody, dynamic, "captured_second", evidence)

local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local probeBlock = builder:reserveBlock(probeBody, { name_hint = "entry", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(probeBody, probeBlock)

local _, closureResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.makeClosure(
		probeBody,
		{
			LifterIR.CaptureBinding.value(first),
			LifterIR.CaptureBinding.value(second),
		}
	),
	{ { type = LifterIR.Types.functionValue(), name_hint = "probe" } },
	{ effects = pure, evidence = evidence }
)
local probe = closureResults[1]

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ probe }))
builder:finalizeBlock(probeBlock, LifterIR.Terminator.returnValues({ capturedFirst, capturedSecond }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(probeBody)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
