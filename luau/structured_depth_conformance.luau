--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local requestedDepth = tonumber(process.args[2] or "")
local nestedBranchCount = requestedDepth or 64
assert(nestedBranchCount >= 1 and nestedBranchCount % 1 == 0, "expected a positive integer nesting depth")
local composedBranchCount = 12

local builder = LifterIR.Builder.new("generic-structured-parser-depth")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-structured-parser-depth")
local evidence = { proof }
local pure = LifterIR.Effects.pure()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local worker = builder:reserveFunction({ name_hint = "nested_choice", evidence = evidence })
local composed = builder:reserveFunction({ name_hint = "composed_choice", evidence = evidence })
local predicate = builder:addParameter(worker, LifterIR.Types.functionValue(), "predicate")
local success = builder:addParameter(worker, LifterIR.Types.integer(), "success")
local failure = builder:addParameter(worker, LifterIR.Types.integer(), "failure")
local initialChoice = builder:addParameter(composed, LifterIR.Types.boolean(), "initial_choice")
local thenChoice = builder:addParameter(composed, LifterIR.Types.boolean(), "then_choice")
local elseChoice = builder:addParameter(composed, LifterIR.Types.boolean(), "else_choice")
local chunkBlock = builder:reserveBlock(chunk, { evidence = evidence })
local branchBlocks: { number } = table.create(nestedBranchCount)
local failureBlocks: { number } = table.create(nestedBranchCount)
for index = 1, nestedBranchCount do
	branchBlocks[index] = builder:reserveBlock(worker, { evidence = evidence })
	failureBlocks[index] = builder:reserveBlock(worker, { evidence = evidence })
end
local successBlock = builder:reserveBlock(worker, { evidence = evidence })
local composedBranches: { number } = table.create(composedBranchCount)
local composedThenBlocks: { number } = table.create(composedBranchCount)
local composedElseBlocks: { number } = table.create(composedBranchCount)
local composedConditions: { number } = table.create(composedBranchCount)
for index = 1, composedBranchCount do
	composedBranches[index] = builder:reserveBlock(composed, { evidence = evidence })
	composedThenBlocks[index] = builder:reserveBlock(composed, { evidence = evidence })
	composedElseBlocks[index] = builder:reserveBlock(composed, { evidence = evidence })
	composedConditions[index] = if index == 1
		then initialChoice
		else builder:addBlockParameter(composedBranches[index], LifterIR.Types.boolean(), "choice")
end
local composedReturn = builder:reserveBlock(composed, { evidence = evidence })
local composedResult = builder:addBlockParameter(composedReturn, LifterIR.Types.boolean(), "choice")

builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(worker, branchBlocks[1])
builder:setFunctionEntry(composed, composedBranches[1])

local _, exported = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(worker),
	{ { type = LifterIR.Types.functionValue(), name_hint = "nested_choice" } },
	{ effects = pure, evidence = evidence }
)
local _, composedExport = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(composed),
	{ { type = LifterIR.Types.functionValue(), name_hint = "composed_choice" } },
	{ effects = pure, evidence = evidence }
)
builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exported[1], composedExport[1] }))

for index = 1, nestedBranchCount do
	local deeper = if index == nestedBranchCount then successBlock else branchBlocks[index + 1]
	local _, condition = builder:addInstruction(
		branchBlocks[index],
		LifterIR.Operation.call(predicate, {}, LifterIR.ResultArity.fixed(1)),
		{ { type = LifterIR.Types.boolean(), name_hint = "condition" } },
		{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
	)
	builder:finalizeBlock(
		branchBlocks[index],
		LifterIR.Terminator.branch(condition[1], LifterIR.Edge(deeper), LifterIR.Edge(failureBlocks[index]))
	)
	builder:finalizeBlock(failureBlocks[index], LifterIR.Terminator.returnValues({ failure }))
end
builder:finalizeBlock(successBlock, LifterIR.Terminator.returnValues({ success }))

for index = 1, composedBranchCount do
	local join = if index == composedBranchCount then composedReturn else composedBranches[index + 1]
	builder:finalizeBlock(
		composedBranches[index],
		LifterIR.Terminator.branch(
			composedConditions[index],
			LifterIR.Edge(composedThenBlocks[index]),
			LifterIR.Edge(composedElseBlocks[index])
		)
	)
	builder:finalizeBlock(composedThenBlocks[index], LifterIR.Terminator.jump(LifterIR.Edge(join, { thenChoice })))
	builder:finalizeBlock(composedElseBlocks[index], LifterIR.Terminator.jump(LifterIR.Edge(join, { elseChoice })))
end
builder:finalizeBlock(composedReturn, LifterIR.Terminator.returnValues({ composedResult }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(worker)
builder:finalizeFunction(composed)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
