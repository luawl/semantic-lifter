--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-pack-return-storage")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-pack-return-storage")
local evidence = { proof }
local dynamicCall = LifterIR.Effects.dynamicCall()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local returnWorker = builder:reserveFunction({ name_hint = "return_tail", evidence = evidence })
local invocationWorker = builder:reserveFunction({ name_hint = "invocation_tail", evidence = evidence })
local literalWorker = builder:reserveFunction({ name_hint = "literal_tail", evidence = evidence })
local writeWorker = builder:reserveFunction({ name_hint = "write_tail", evidence = evidence })
local reuseWorker = builder:reserveFunction({ name_hint = "reuse_tail", evidence = evidence })

local chunkBlock = builder:reserveBlock(chunk, { name_hint = "exports", evidence = evidence })
local returnProducerBlock = builder:reserveBlock(returnWorker, { name_hint = "producer", evidence = evidence })
local returnConsumerBlock = builder:reserveBlock(returnWorker, { name_hint = "return", evidence = evidence })
local invocationProducerBlock = builder:reserveBlock(invocationWorker, { name_hint = "producer", evidence = evidence })
local invocationConsumerBlock = builder:reserveBlock(invocationWorker, { name_hint = "consume", evidence = evidence })
local literalProducerBlock = builder:reserveBlock(literalWorker, { name_hint = "producer", evidence = evidence })
local literalConsumerBlock = builder:reserveBlock(literalWorker, { name_hint = "construct", evidence = evidence })
local writeProducerBlock = builder:reserveBlock(writeWorker, { name_hint = "producer", evidence = evidence })
local writeConsumerBlock = builder:reserveBlock(writeWorker, { name_hint = "write", evidence = evidence })
local reuseProducerBlock = builder:reserveBlock(reuseWorker, { name_hint = "producer", evidence = evidence })
local reuseConsumerBlock = builder:reserveBlock(reuseWorker, { name_hint = "reuse", evidence = evidence })

builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(returnWorker, returnProducerBlock)
builder:setFunctionEntry(invocationWorker, invocationProducerBlock)
builder:setFunctionEntry(literalWorker, literalProducerBlock)
builder:setFunctionEntry(writeWorker, writeProducerBlock)
builder:setFunctionEntry(reuseWorker, reuseProducerBlock)

local exportedWorkers: { number } = {}
for _, worker in { returnWorker, invocationWorker, literalWorker, writeWorker, reuseWorker } do
	local _, results = builder:addInstruction(
		chunkBlock,
		LifterIR.Operation.functionRef(worker),
		{ { type = LifterIR.Types.functionValue(), name_hint = "worker" } },
		{ effects = LifterIR.Effects.pure(), evidence = evidence }
	)
	table.insert(exportedWorkers, results[1])
end
builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues(exportedWorkers))

local returnProducer = builder:addParameter(returnWorker, LifterIR.Types.functionValue(), "producer")
local returnObserve = builder:addParameter(returnWorker, LifterIR.Types.functionValue(), "observe")
local _, returnPack = builder:addOpenCall(returnProducerBlock, returnProducer, {}, {
	effects = dynamicCall,
	evidence = evidence,
})
local _, returnObserved = builder:addInstruction(
	returnConsumerBlock,
	LifterIR.Operation.call(returnObserve, {}, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.integer(), name_hint = "observed" } },
	{ effects = dynamicCall, evidence = evidence }
)
builder:finalizeBlock(returnProducerBlock, LifterIR.Terminator.jump(LifterIR.Edge(returnConsumerBlock)))
builder:finalizeBlock(returnConsumerBlock, LifterIR.Terminator.returnExpanded({ returnObserved[1] }, returnPack))

local invocationProducer = builder:addParameter(invocationWorker, LifterIR.Types.functionValue(), "producer")
local invocationObserve = builder:addParameter(invocationWorker, LifterIR.Types.functionValue(), "observe")
local invocationConsume = builder:addParameter(invocationWorker, LifterIR.Types.functionValue(), "consume")
local _, invocationPack = builder:addOpenCall(invocationProducerBlock, invocationProducer, {}, {
	effects = dynamicCall,
	evidence = evidence,
})
local _, invocationObserved = builder:addInstruction(
	invocationConsumerBlock,
	LifterIR.Operation.call(invocationObserve, {}, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.integer(), name_hint = "observed" } },
	{ effects = dynamicCall, evidence = evidence }
)
local _, invocationResult = builder:addInstruction(
	invocationConsumerBlock,
	LifterIR.Operation.call(
		invocationConsume,
		{ invocationObserved[1] },
		LifterIR.ResultArity.fixed(1),
		invocationPack
	),
	{ { type = LifterIR.Types.table(), name_hint = "consumed" } },
	{ effects = dynamicCall, evidence = evidence }
)
builder:finalizeBlock(invocationProducerBlock, LifterIR.Terminator.jump(LifterIR.Edge(invocationConsumerBlock)))
builder:finalizeBlock(invocationConsumerBlock, LifterIR.Terminator.returnValues({ invocationResult[1] }))

local literalProducer = builder:addParameter(literalWorker, LifterIR.Types.functionValue(), "producer")
local literalObserve = builder:addParameter(literalWorker, LifterIR.Types.functionValue(), "observe")
local _, literalPack = builder:addOpenCall(literalProducerBlock, literalProducer, {}, {
	effects = dynamicCall,
	evidence = evidence,
})
local _, literalObserved = builder:addInstruction(
	literalConsumerBlock,
	LifterIR.Operation.call(literalObserve, {}, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.integer(), name_hint = "observed" } },
	{ effects = dynamicCall, evidence = evidence }
)
local _, literalResult = builder:addInstruction(
	literalConsumerBlock,
	LifterIR.Operation.makeTableLiteral({ LifterIR.TableConstructorField.list(literalObserved[1]) }, literalPack),
	{ { type = LifterIR.Types.table(), name_hint = "constructed" } },
	{ effects = LifterIR.Effects.tableConstructor(), evidence = evidence }
)
builder:finalizeBlock(literalProducerBlock, LifterIR.Terminator.jump(LifterIR.Edge(literalConsumerBlock)))
builder:finalizeBlock(literalConsumerBlock, LifterIR.Terminator.returnValues({ literalResult[1] }))

local writeProducer = builder:addParameter(writeWorker, LifterIR.Types.functionValue(), "producer")
local writeObserve = builder:addParameter(writeWorker, LifterIR.Types.functionValue(), "observe")
local writeTarget = builder:addParameter(writeWorker, LifterIR.Types.table(), "target")
local _, writePack = builder:addOpenCall(writeProducerBlock, writeProducer, {}, {
	effects = dynamicCall,
	evidence = evidence,
})
local _, writeObserved = builder:addInstruction(
	writeConsumerBlock,
	LifterIR.Operation.call(writeObserve, {}, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.integer(), name_hint = "observed" } },
	{ effects = dynamicCall, evidence = evidence }
)
builder:addInstruction(
	writeConsumerBlock,
	LifterIR.Operation.tableSetPack(writeTarget, 2, writePack),
	{},
	{ effects = LifterIR.Effects.rawTableWrite(), evidence = evidence }
)
builder:finalizeBlock(writeProducerBlock, LifterIR.Terminator.jump(LifterIR.Edge(writeConsumerBlock)))
builder:finalizeBlock(writeConsumerBlock, LifterIR.Terminator.returnValues({ writeObserved[1] }))

local reuseProducer = builder:addParameter(reuseWorker, LifterIR.Types.functionValue(), "producer")
local reuseObserve = builder:addParameter(reuseWorker, LifterIR.Types.functionValue(), "observe")
local reuseConsume = builder:addParameter(reuseWorker, LifterIR.Types.functionValue(), "consume")
local reuseTarget = builder:addParameter(reuseWorker, LifterIR.Types.table(), "target")
local _, reusePack = builder:addOpenCall(reuseProducerBlock, reuseProducer, {}, {
	effects = dynamicCall,
	evidence = evidence,
})
local _, reuseObserved = builder:addInstruction(
	reuseConsumerBlock,
	LifterIR.Operation.call(reuseObserve, {}, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.integer(), name_hint = "observed" } },
	{ effects = dynamicCall, evidence = evidence }
)
local _, firstReuse = builder:addInstruction(
	reuseConsumerBlock,
	LifterIR.Operation.call(reuseConsume, { reuseObserved[1] }, LifterIR.ResultArity.fixed(1), reusePack),
	{ { type = LifterIR.Types.table(), name_hint = "first_reuse" } },
	{ effects = dynamicCall, evidence = evidence }
)
local _, secondReuse = builder:addInstruction(
	reuseConsumerBlock,
	LifterIR.Operation.call(reuseConsume, { reuseObserved[1] }, LifterIR.ResultArity.fixed(1), reusePack),
	{ { type = LifterIR.Types.table(), name_hint = "second_reuse" } },
	{ effects = dynamicCall, evidence = evidence }
)
local _, reuseLiteral = builder:addInstruction(
	reuseConsumerBlock,
	LifterIR.Operation.makeTableLiteral({ LifterIR.TableConstructorField.list(reuseObserved[1]) }, reusePack),
	{ { type = LifterIR.Types.table(), name_hint = "reuse_literal" } },
	{ effects = LifterIR.Effects.tableConstructor(), evidence = evidence }
)
builder:addInstruction(
	reuseConsumerBlock,
	LifterIR.Operation.tableSetPack(reuseTarget, 2, reusePack),
	{},
	{ effects = LifterIR.Effects.rawTableWrite(), evidence = evidence }
)
builder:finalizeBlock(reuseProducerBlock, LifterIR.Terminator.jump(LifterIR.Edge(reuseConsumerBlock)))
builder:finalizeBlock(
	reuseConsumerBlock,
	LifterIR.Terminator.returnExpanded({ firstReuse[1], secondReuse[1], reuseLiteral[1], reuseObserved[1] }, reusePack)
)

builder:finalizeFunction(chunk)
builder:finalizeFunction(returnWorker)
builder:finalizeFunction(invocationWorker)
builder:finalizeFunction(literalWorker)
builder:finalizeFunction(writeWorker)
builder:finalizeFunction(reuseWorker)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
