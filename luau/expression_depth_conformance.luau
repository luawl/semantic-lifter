--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local operationCount = 1100
local builder = LifterIR.Builder.new("generic-bounded-expression-depth")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-bounded-expression-depth")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local integer = LifterIR.Types.integer()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local worker = builder:reserveFunction({ name_hint = "sum_chain", evidence = evidence })
local initial = builder:addParameter(worker, integer, "initial")
local increment = builder:addParameter(worker, integer, "increment")
local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local workerBlock = builder:reserveBlock(worker, { name_hint = "entry", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(worker, workerBlock)

local _, exportResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(worker),
	{ { type = LifterIR.Types.functionValue(), name_hint = "sum_chain" } },
	{ effects = pure, evidence = evidence }
)

local current = initial
for index = 1, operationCount do
	local _, results = builder:addInstruction(
		workerBlock,
		LifterIR.Operation.binary("add", current, increment),
		{ { type = integer, name_hint = "sum" .. tostring(index) } },
		{ effects = pure, evidence = evidence }
	)
	current = results[1]
end

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportResults[1] }))
builder:finalizeBlock(workerBlock, LifterIR.Terminator.returnValues({ current }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(worker)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
