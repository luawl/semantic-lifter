--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-open-pack-projection")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-open-pack-projection")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local dynamicCall = LifterIR.Effects.dynamicCall()
local integer = LifterIR.Types.integer()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local producer = builder:addParameter(chunk, LifterIR.Types.functionValue(), "producer")
local consumer = builder:addParameter(chunk, LifterIR.Types.functionValue(), "consumer")
local afterConsumer = builder:addParameter(chunk, LifterIR.Types.functionValue(), "after_consumer")
local chooseThen = builder:addParameter(chunk, LifterIR.Types.boolean(), "choose_then")
local entry = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local producerBlock = builder:reserveBlock(chunk, { name_hint = "producer", evidence = evidence })
local thenBlock = builder:reserveBlock(chunk, { name_hint = "then_path", evidence = evidence })
local elseBlock = builder:reserveBlock(chunk, { name_hint = "else_path", evidence = evidence })
local join = builder:reserveBlock(chunk, { name_hint = "join", evidence = evidence })
local latchThen = builder:reserveBlock(chunk, { name_hint = "latch_then", evidence = evidence })
local latchElse = builder:reserveBlock(chunk, { name_hint = "latch_else", evidence = evidence })
local latchMerge = builder:reserveBlock(chunk, { name_hint = "latch_merge", evidence = evidence })
local reentryDispatch = builder:reserveBlock(chunk, { name_hint = "reentry_dispatch", evidence = evidence })
local reentryRelay = builder:reserveBlock(chunk, { name_hint = "reentry_relay", evidence = evidence })
local exitBlock = builder:reserveBlock(chunk, { name_hint = "exit", evidence = evidence })
local counter = builder:addBlockParameter(producerBlock, integer, "counter")
local pathMarker = builder:addBlockParameter(join, integer, "path_marker")
local latchMarker = builder:addBlockParameter(latchMerge, integer, "latch_marker")
local reentryCounter = builder:addBlockParameter(reentryDispatch, integer, "reentry_counter")
local relayCounter = builder:addBlockParameter(reentryRelay, integer, "relay_counter")
local finalResult = builder:addBlockParameter(exitBlock, LifterIR.Types.table(), "final_result")
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, entry)

local _, zeroResults = builder:addInstruction(
	entry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = integer, name_hint = "zero" } },
	{ effects = pure, evidence = evidence }
)
local _, oneResults = builder:addInstruction(
	entry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = integer, name_hint = "one" } },
	{ effects = pure, evidence = evidence }
)
local _, projectedPack = builder:addOpenCall(producerBlock, producer, {}, {
	effects = dynamicCall,
	evidence = evidence,
})
local _, suffixResults = builder:addInstruction(
	producerBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = integer, name_hint = "producer_suffix" } },
	{ effects = pure, evidence = evidence }
)
local _, prefixResults = builder:addInstruction(
	join,
	LifterIR.Operation.constant(LifterIR.Literal.integer("7")),
	{ { type = integer, name_hint = "consumer_prefix" } },
	{ effects = pure, evidence = evidence }
)
local _, thenResults = builder:addInstruction(
	thenBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("11")),
	{ { type = integer, name_hint = "then_marker" } },
	{ effects = pure, evidence = evidence }
)
local _, elseResults = builder:addInstruction(
	elseBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("22")),
	{ { type = integer, name_hint = "else_marker" } },
	{ effects = pure, evidence = evidence }
)
local _, consumedResults = builder:addInstruction(
	join,
	LifterIR.Operation.call(
		consumer,
		{ suffixResults[1], pathMarker, prefixResults[1] },
		LifterIR.ResultArity.fixed(1),
		projectedPack
	),
	{ { type = LifterIR.Types.table(), name_hint = "consumed_result" } },
	{ effects = dynamicCall, evidence = evidence }
)
local _, latchThenResults = builder:addInstruction(
	latchThen,
	LifterIR.Operation.constant(LifterIR.Literal.integer("31")),
	{ { type = integer, name_hint = "latch_then_marker" } },
	{ effects = pure, evidence = evidence }
)
local _, latchElseResults = builder:addInstruction(
	latchElse,
	LifterIR.Operation.constant(LifterIR.Literal.integer("32")),
	{ { type = integer, name_hint = "latch_else_marker" } },
	{ effects = pure, evidence = evidence }
)
builder:addInstruction(
	latchMerge,
	LifterIR.Operation.call(afterConsumer, { latchMarker }, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = dynamicCall, evidence = evidence }
)
local _, continueResults = builder:addInstruction(
	latchMerge,
	LifterIR.Operation.binary("less", counter, oneResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "continue_loop" } },
	{ effects = pure, evidence = evidence }
)
local _, nextResults = builder:addInstruction(
	latchMerge,
	LifterIR.Operation.binary("add", counter, oneResults[1]),
	{ { type = integer, name_hint = "next_counter" } },
	{ effects = pure, evidence = evidence }
)
local _, relayedCounterResults = builder:addInstruction(
	reentryRelay,
	LifterIR.Operation.binary("add", relayCounter, zeroResults[1]),
	{ { type = integer, name_hint = "relayed_counter" } },
	{ effects = pure, evidence = evidence }
)

builder:finalizeBlock(entry, LifterIR.Terminator.jump(LifterIR.Edge(producerBlock, { zeroResults[1] })))
builder:finalizeBlock(
	producerBlock,
	LifterIR.Terminator.branch(chooseThen, LifterIR.Edge(thenBlock), LifterIR.Edge(elseBlock))
)
builder:finalizeBlock(thenBlock, LifterIR.Terminator.jump(LifterIR.Edge(join, { thenResults[1] })))
builder:finalizeBlock(elseBlock, LifterIR.Terminator.jump(LifterIR.Edge(join, { elseResults[1] })))
builder:finalizeBlock(
	join,
	LifterIR.Terminator.branch(chooseThen, LifterIR.Edge(latchThen), LifterIR.Edge(latchElse))
)
builder:finalizeBlock(latchThen, LifterIR.Terminator.jump(LifterIR.Edge(latchMerge, { latchThenResults[1] })))
builder:finalizeBlock(latchElse, LifterIR.Terminator.jump(LifterIR.Edge(latchMerge, { latchElseResults[1] })))
builder:finalizeBlock(
	latchMerge,
	LifterIR.Terminator.branch(
		continueResults[1],
		LifterIR.Edge(reentryDispatch, { nextResults[1] }),
		LifterIR.Edge(exitBlock, { consumedResults[1] })
	)
)
builder:finalizeBlock(
	reentryDispatch,
	LifterIR.Terminator.branch(
		chooseThen,
		LifterIR.Edge(producerBlock, { reentryCounter }),
		LifterIR.Edge(reentryRelay, { reentryCounter })
	)
)
builder:finalizeBlock(reentryRelay, LifterIR.Terminator.jump(LifterIR.Edge(producerBlock, { relayedCounterResults[1] })))
builder:finalizeBlock(exitBlock, LifterIR.Terminator.returnValues({ finalResult }))
builder:finalizeFunction(chunk)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
