--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-closed-pack-discard")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-closed-pack-discard")
local evidence = { proof }
local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local producer = builder:addParameter(chunk, LifterIR.Types.functionValue(), "producer")
local observe = builder:addParameter(chunk, LifterIR.Types.functionValue(), "observe")
local entry = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, entry)

local _, produced = builder:addInstruction(
	entry,
	LifterIR.Operation.call(producer, {}, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.functionValue(), name_hint = "packed_marker" } },
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local _, closedPack = builder:addValuePack(entry, { produced[1] }, { evidence = evidence })
builder:addInstruction(
	entry,
	LifterIR.Operation.call(observe, {}, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
builder:addInstruction(
	entry,
	LifterIR.Operation.adjustPack(closedPack),
	{},
	{ effects = LifterIR.Effects.pure(), evidence = evidence }
)

builder:finalizeBlock(entry, LifterIR.Terminator.returnPack(closedPack))
builder:finalizeFunction(chunk)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
