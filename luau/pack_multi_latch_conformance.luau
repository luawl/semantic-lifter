--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-pack-multi-latch")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-pack-multi-latch")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local dynamicCall = LifterIR.Effects.dynamicCall()
local dynamic = LifterIR.Types.dynamic()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local worker = builder:reserveFunction({ name_hint = "multi_latch_worker", evidence = evidence })
local producer = builder:addParameter(worker, LifterIR.Types.functionValue(), "producer")
local earlyContinueDecision = builder:addParameter(worker, LifterIR.Types.functionValue(), "early_continue")
local chooseLatch = builder:addParameter(worker, LifterIR.Types.functionValue(), "choose_latch")
local firstLatchDecision = builder:addParameter(worker, LifterIR.Types.functionValue(), "first_latch")
local secondLatchDecision = builder:addParameter(worker, LifterIR.Types.functionValue(), "second_latch")

local chunkEntry = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local setupBlock = builder:reserveBlock(worker, { name_hint = "setup", evidence = evidence })
local producerBlock = builder:reserveBlock(worker, { name_hint = "producer", evidence = evidence })
local adjustmentBlock = builder:reserveBlock(worker, { name_hint = "adjustment", evidence = evidence })
local firstLatchBlock = builder:reserveBlock(worker, { name_hint = "first_latch", evidence = evidence })
local secondLatchBlock = builder:reserveBlock(worker, { name_hint = "second_latch", evidence = evidence })
local sharedExitForward = builder:reserveBlock(worker, { name_hint = "shared_exit_forward", evidence = evidence })
local exitBlock = builder:reserveBlock(worker, { name_hint = "exit", evidence = evidence })

local producerCounter = builder:addBlockParameter(producerBlock, LifterIR.Types.integer(), "counter")

builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkEntry)
builder:setFunctionEntry(worker, setupBlock)

local _, workerResults = builder:addInstruction(
	chunkEntry,
	LifterIR.Operation.functionRef(worker),
	{ { type = LifterIR.Types.functionValue(), name_hint = "multi_latch_worker" } },
	{ effects = pure, evidence = evidence }
)
builder:finalizeBlock(chunkEntry, LifterIR.Terminator.returnValues({ workerResults[1] }))

local _, zeroResults = builder:addInstruction(
	setupBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = LifterIR.Types.integer(), name_hint = "zero" } },
	{ effects = pure, evidence = evidence }
)
local _, oneResults = builder:addInstruction(
	setupBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = LifterIR.Types.integer(), name_hint = "one" } },
	{ effects = pure, evidence = evidence }
)
builder:finalizeBlock(setupBlock, LifterIR.Terminator.jump(LifterIR.Edge(producerBlock, { zeroResults[1] })))

local _, producerPack = builder:addOpenCall(producerBlock, producer, {}, {
	effects = dynamicCall,
	evidence = evidence,
})
local _, producerNextResults = builder:addInstruction(
	producerBlock,
	LifterIR.Operation.binary("add", producerCounter, oneResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "next_counter" } },
	{ effects = pure, evidence = evidence }
)
local _, earlyContinueResults = builder:addInstruction(
	producerBlock,
	LifterIR.Operation.call(earlyContinueDecision, { producerNextResults[1] }, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.boolean(), name_hint = "continue_early" } },
	{ effects = dynamicCall, evidence = evidence }
)
builder:finalizeBlock(
	producerBlock,
	LifterIR.Terminator.branch(
		earlyContinueResults[1],
		LifterIR.Edge(producerBlock, { producerNextResults[1] }),
		LifterIR.Edge(adjustmentBlock, {})
	)
)

local _, adjustedResults = builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.adjustPack(producerPack),
	{
		{ type = LifterIR.Types.integer(), name_hint = "current_first" },
		{ type = dynamic, name_hint = "current_second" },
	},
	{ effects = pure, evidence = evidence }
)
local _, choiceResults = builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.call(chooseLatch, { producerNextResults[1] }, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.boolean(), name_hint = "use_first_latch" } },
	{ effects = dynamicCall, evidence = evidence }
)
builder:finalizeBlock(
	adjustmentBlock,
	LifterIR.Terminator.branch(
		choiceResults[1],
		LifterIR.Edge(firstLatchBlock, {}),
		LifterIR.Edge(secondLatchBlock, {})
	)
)

local _, firstContinueResults = builder:addInstruction(
	firstLatchBlock,
	LifterIR.Operation.call(firstLatchDecision, { producerNextResults[1] }, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.boolean(), name_hint = "continue_from_first" } },
	{ effects = dynamicCall, evidence = evidence }
)
builder:finalizeBlock(
	firstLatchBlock,
	LifterIR.Terminator.branch(
		firstContinueResults[1],
		LifterIR.Edge(producerBlock, { producerNextResults[1] }),
		LifterIR.Edge(sharedExitForward, {})
	)
)

local _, secondContinueResults = builder:addInstruction(
	secondLatchBlock,
	LifterIR.Operation.call(secondLatchDecision, { producerNextResults[1] }, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.boolean(), name_hint = "continue_from_second" } },
	{ effects = dynamicCall, evidence = evidence }
)
builder:finalizeBlock(
	secondLatchBlock,
	LifterIR.Terminator.branch(
		secondContinueResults[1],
		LifterIR.Edge(producerBlock, { producerNextResults[1] }),
		LifterIR.Edge(sharedExitForward, {})
	)
)
builder:finalizeBlock(sharedExitForward, LifterIR.Terminator.jump(LifterIR.Edge(exitBlock, {})))
builder:finalizeBlock(
	exitBlock,
	LifterIR.Terminator.returnExpanded({ adjustedResults[1], adjustedResults[2], producerNextResults[1] }, producerPack)
)

builder:finalizeFunction(chunk)
builder:finalizeFunction(worker)
fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
