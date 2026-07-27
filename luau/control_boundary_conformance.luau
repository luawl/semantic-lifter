--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-luau-control-boundaries")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-luau-control-boundaries")
local evidence = { proof }
local pure = LifterIR.Effects.pure()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local probe = builder:reserveFunction({ name_hint = "probe_boundaries", evidence = evidence })
local thrower = builder:reserveFunction({ name_hint = "thrower", evidence = evidence })
local worker = builder:reserveFunction({ name_hint = "worker", evidence = evidence })
local packProducer = builder:reserveFunction({ name_hint = "pack_producer", evidence = evidence })
local projectedTerminal = builder:reserveFunction({ name_hint = "project_terminal", evidence = evidence })
local chunkBlock = builder:reserveBlock(chunk, { evidence = evidence })
local probeBlock = builder:reserveBlock(probe, { evidence = evidence })
local throwerBlock = builder:reserveBlock(thrower, { evidence = evidence })
local workerBlock = builder:reserveBlock(worker, { evidence = evidence })
local packProducerBlock = builder:reserveBlock(packProducer, { evidence = evidence })
local projectedReturn = builder:reserveBlock(projectedTerminal, { evidence = evidence })
local projectedNested = builder:reserveBlock(projectedTerminal, { evidence = evidence })
local projectedDirect = builder:reserveBlock(projectedTerminal, { evidence = evidence })
local projectedEntry = builder:reserveBlock(projectedTerminal, { evidence = evidence })
local projectedJoin = builder:reserveBlock(projectedTerminal, { evidence = evidence })
local projectedEarly = builder:reserveBlock(projectedTerminal, { evidence = evidence })
local projectedNestedEntry = builder:reserveBlock(projectedTerminal, { evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(probe, probeBlock)
builder:setFunctionEntry(thrower, throwerBlock)
builder:setFunctionEntry(worker, workerBlock)
builder:setFunctionEntry(packProducer, packProducerBlock)
builder:setFunctionEntry(projectedTerminal, projectedEntry)

local function addSingle(block: number, operation: any, valueType: any, nameHint: string, effects: any): number
	local _, results = builder:addInstruction(
		block,
		operation,
		{ { type = valueType, name_hint = nameHint } },
		{ effects = effects, evidence = evidence }
	)
	return results[1]
end

local function addBinary(block: number, operator: string, left: number, right: number, nameHint: string): number
	return addSingle(
		block,
		LifterIR.Operation.binary(operator, left, right),
		LifterIR.Types.boolean(),
		nameHint,
		pure
	)
end

local function addAnd(left: number, right: number, nameHint: string): number
	return addBinary(probeBlock, "logical_and", left, right, nameHint)
end

local exportedProbe = addSingle(
	chunkBlock,
	LifterIR.Operation.functionRef(probe),
	LifterIR.Types.functionValue(),
	"probe",
	pure
)
local exportedProjectedTerminal = addSingle(
	chunkBlock,
	LifterIR.Operation.functionRef(projectedTerminal),
	LifterIR.Types.functionValue(),
	"project_terminal",
	pure
)

local projectedOuter = builder:addParameter(projectedTerminal, LifterIR.Types.boolean(), "outer_condition")
local projectedInner = builder:addParameter(projectedTerminal, LifterIR.Types.boolean(), "inner_condition")
local projectedEarlyValue = builder:addParameter(projectedTerminal, LifterIR.Types.string(), "early_value")
local projectedFallbackValue = builder:addParameter(projectedTerminal, LifterIR.Types.string(), "fallback_value")
local projectedObserver = builder:addParameter(projectedTerminal, LifterIR.Types.functionValue(), "observer")
local projectedResult = builder:addBlockParameter(projectedReturn, LifterIR.Types.string(), "result")
local projectedObserved = addSingle(
	projectedReturn,
	LifterIR.Operation.call(projectedObserver, { projectedResult }, LifterIR.ResultArity.fixed(1)),
	LifterIR.Types.string(),
	"observed",
	LifterIR.Effects.dynamicCall()
)

local throwerReference = addSingle(
	probeBlock,
	LifterIR.Operation.functionRef(thrower),
	LifterIR.Types.functionValue(),
	"thrower",
	pure
)
local packProducerReference = addSingle(
	probeBlock,
	LifterIR.Operation.functionRef(packProducer),
	LifterIR.Types.functionValue(),
	"pack_producer",
	pure
)
local _, protectedArguments = builder:addOpenCall(
	probeBlock,
	packProducerReference,
	{},
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local _, protectedPack = builder:addOpenProtectedCall(
	probeBlock,
	throwerReference,
	nil,
	{},
	{ effects = LifterIR.Effects.protectedInvocation(), evidence = evidence },
	protectedArguments
)
local _, protectedResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.adjustPack(protectedPack),
	{
		{ type = LifterIR.Types.boolean(), name_hint = "protected_ok" },
		{ type = LifterIR.Types.string(), name_hint = "protected_error" },
	},
	{ effects = pure, evidence = evidence }
)
local protectedOk = protectedResults[1]
local protectedError = protectedResults[2]

local workerReference = addSingle(
	probeBlock,
	LifterIR.Operation.functionRef(worker),
	LifterIR.Types.functionValue(),
	"worker",
	pure
)
local thread = addSingle(
	probeBlock,
	LifterIR.Operation.coroutineCreate(workerReference),
	LifterIR.Types.thread(),
	"thread",
	LifterIR.Effects.coroutineCreate()
)
local _, resumeArguments = builder:addOpenCall(
	probeBlock,
	packProducerReference,
	{},
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local _, firstResumePack = builder:addOpenCoroutineResume(
	probeBlock,
	thread,
	{},
	{ effects = LifterIR.Effects.coroutineResume(), evidence = evidence },
	resumeArguments
)
local _, firstResumeResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.adjustPack(firstResumePack),
	{
		{ type = LifterIR.Types.boolean(), name_hint = "first_resume_ok" },
		{ type = LifterIR.Types.string(), name_hint = "yielded_value" },
	},
	{ effects = pure, evidence = evidence }
)
local firstResumeOk = firstResumeResults[1]
local yieldedValue = firstResumeResults[2]

local resumeInput = addSingle(
	probeBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("resume-value")),
	LifterIR.Types.string(),
	"resume_input",
	pure
)
local _, secondResumeResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.coroutineResume(thread, { resumeInput }, LifterIR.ResultArity.fixed(2)),
	{
		{ type = LifterIR.Types.boolean(), name_hint = "second_resume_ok" },
		{ type = LifterIR.Types.string(), name_hint = "returned_value" },
	},
	{ effects = LifterIR.Effects.coroutineResume(), evidence = evidence }
)
local secondResumeOk = secondResumeResults[1]
local returnedValue = secondResumeResults[2]

local expectedError = addSingle(
	probeBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("boom")),
	LifterIR.Types.string(),
	"expected_error",
	pure
)
local expectedYield = addSingle(
	probeBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("pause")),
	LifterIR.Types.string(),
	"expected_yield",
	pure
)
local protectedFailed = addSingle(
	probeBlock,
	LifterIR.Operation.unary("logical_not", protectedOk),
	LifterIR.Types.boolean(),
	"protected_failed",
	pure
)
local errorPreserved = addBinary(probeBlock, "equal", protectedError, expectedError, "error_preserved")
local yieldPreserved = addBinary(probeBlock, "equal", yieldedValue, expectedYield, "yield_preserved")
local resumePreserved = addBinary(probeBlock, "equal", returnedValue, resumeInput, "resume_preserved")
local protectedPassed = addAnd(protectedFailed, errorPreserved, "protected_passed")
local firstResumePassed = addAnd(firstResumeOk, yieldPreserved, "first_resume_passed")
local secondResumePassed = addAnd(secondResumeOk, resumePreserved, "second_resume_passed")
local resumesPassed = addAnd(firstResumePassed, secondResumePassed, "resumes_passed")
local passed = addAnd(protectedPassed, resumesPassed, "passed")

local thrownValue = addSingle(
	throwerBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("boom")),
	LifterIR.Types.string(),
	"thrown_value",
	pure
)

local pauseValue = addSingle(
	workerBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("pause")),
	LifterIR.Types.string(),
	"pause_value",
	pure
)
local workerProducerReference = addSingle(
	workerBlock,
	LifterIR.Operation.functionRef(packProducer),
	LifterIR.Types.functionValue(),
	"pack_producer",
	pure
)
local _, yieldedTail = builder:addOpenCall(
	workerBlock,
	workerProducerReference,
	{},
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local _, resumedPack = builder:addOpenCoroutineYield(
	workerBlock,
	{ pauseValue },
	{ effects = LifterIR.Effects.coroutineYield(), evidence = evidence },
	yieldedTail
)
local _, resumedResults = builder:addInstruction(
	workerBlock,
	LifterIR.Operation.adjustPack(resumedPack),
	{ { type = LifterIR.Types.string(), name_hint = "resumed_value" } },
	{ effects = pure, evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportedProbe, exportedProjectedTerminal }))
builder:finalizeBlock(probeBlock, LifterIR.Terminator.returnValues({ passed }))
builder:finalizeBlock(throwerBlock, LifterIR.Terminator.throwError(thrownValue, 0))
builder:finalizeBlock(workerBlock, LifterIR.Terminator.returnValues({ resumedResults[1] }))
local producerFirst = addSingle(
	packProducerBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("pack-a")),
	LifterIR.Types.string(),
	"pack_a",
	pure
)
local producerSecond = addSingle(
	packProducerBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("pack-b")),
	LifterIR.Types.string(),
	"pack_b",
	pure
)
builder:finalizeBlock(packProducerBlock, LifterIR.Terminator.returnValues({ producerFirst, producerSecond }))
builder:finalizeBlock(
	projectedEntry,
	LifterIR.Terminator.branch(
		projectedOuter,
		LifterIR.Edge(projectedNestedEntry),
		LifterIR.Edge(projectedDirect)
	)
)
builder:finalizeBlock(projectedDirect, LifterIR.Terminator.jump(LifterIR.Edge(projectedJoin)))
builder:finalizeBlock(projectedNestedEntry, LifterIR.Terminator.jump(LifterIR.Edge(projectedNested)))
builder:finalizeBlock(
	projectedNested,
	LifterIR.Terminator.branch(
		projectedInner,
		LifterIR.Edge(projectedEarly),
		LifterIR.Edge(projectedJoin)
	)
)
builder:finalizeBlock(
	projectedEarly,
	LifterIR.Terminator.jump(LifterIR.Edge(projectedReturn, { projectedEarlyValue }))
)
builder:finalizeBlock(
	projectedJoin,
	LifterIR.Terminator.jump(LifterIR.Edge(projectedReturn, { projectedFallbackValue }))
)
builder:finalizeBlock(projectedReturn, LifterIR.Terminator.returnValues({ projectedObserved }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(probe)
builder:finalizeFunction(thrower)
builder:finalizeFunction(worker)
builder:finalizeFunction(packProducer)
builder:finalizeFunction(projectedTerminal)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
