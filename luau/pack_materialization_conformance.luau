--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-pack-materialization")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-pack-materialization")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local dynamicCall = LifterIR.Effects.dynamicCall()
local protectedCall = LifterIR.Effects.protectedInvocation()
local coroutineResume = LifterIR.Effects.coroutineResume()
local coroutineYield = LifterIR.Effects.coroutineYield()
local namecall = LifterIR.Effects.namecall()
local dynamic = LifterIR.Types.dynamic()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local storedPackWorker = builder:reserveFunction({ name_hint = "stored_pack_worker", evidence = evidence })
local cyclicPackWorker = builder:reserveFunction({ name_hint = "cyclic_pack_worker", evidence = evidence })
local captureFreeBody = builder:reserveFunction({
	name_hint = "capture_free",
	lexical_parent = cyclicPackWorker,
	evidence = evidence,
})
local stableRootBody = builder:reserveFunction({
	name_hint = "stable_root",
	lexical_parent = cyclicPackWorker,
	evidence = evidence,
})
local iterationCaptureBody = builder:reserveFunction({
	name_hint = "iteration_capture",
	lexical_parent = cyclicPackWorker,
	evidence = evidence,
})
local producer = builder:addParameter(chunk, LifterIR.Types.functionValue(), "producer")
local observe = builder:addParameter(chunk, LifterIR.Types.functionValue(), "observe")
local selector = builder:addParameter(chunk, LifterIR.Types.boolean(), "selector")
local protectedProducer = builder:addParameter(chunk, LifterIR.Types.functionValue(), "pcall")
local resumeThread = builder:addParameter(chunk, LifterIR.Types.thread(), "resume_thread")
local namecallReceiver = builder:addParameter(chunk, LifterIR.Types.table(), "namecall_receiver")
local mutateProbe = builder:addParameter(chunk, LifterIR.Types.functionValue(), "mutate_probe")
local storedProducer = builder:addParameter(storedPackWorker, LifterIR.Types.functionValue(), "stored_producer")
local cyclicProducer = builder:addParameter(cyclicPackWorker, LifterIR.Types.functionValue(), "cyclic_producer")
local cyclicFailure = builder:addParameter(cyclicPackWorker, LifterIR.Types.functionValue(), "xpcall")
local cyclicSkip = builder:addParameter(cyclicPackWorker, LifterIR.Types.functionValue(), "should_skip")
local cyclicSecondSkip = builder:addParameter(cyclicPackWorker, LifterIR.Types.functionValue(), "should_skip_second")
local cyclicLimit = builder:addParameter(cyclicPackWorker, LifterIR.Types.integer(), "limit")
local captureFreeValue = builder:addParameter(captureFreeBody, LifterIR.Types.integer(), "value")
local capturedLimit = builder:addValueCapture(stableRootBody, LifterIR.Types.integer(), "captured_limit", evidence)
local capturedSeed = builder:addValueCapture(stableRootBody, LifterIR.Types.integer(), "captured_seed", evidence)
local entry = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local forwardingBlock = builder:reserveBlock(chunk, { name_hint = "forwarding", evidence = evidence })
local alternateForwardingBlock = builder:reserveBlock(chunk, { name_hint = "alternate_forwarding", evidence = evidence })
local adjustmentBlock = builder:reserveBlock(chunk, { name_hint = "adjustment", evidence = evidence })
local packConsumerBlock = builder:reserveBlock(chunk, { name_hint = "pack_consumer", evidence = evidence })
local narrowBlock = builder:reserveBlock(chunk, { name_hint = "narrow", evidence = evidence })
local wideBlock = builder:reserveBlock(chunk, { name_hint = "wide", evidence = evidence })
local storedPackProducerBlock = builder:reserveBlock(storedPackWorker, { name_hint = "producer", evidence = evidence })
local storedPackAdjustmentBlock = builder:reserveBlock(storedPackWorker, { name_hint = "adjustment", evidence = evidence })
local storedPackWideAdjustmentBlock = builder:reserveBlock(storedPackWorker, { name_hint = "wide_adjustment", evidence = evidence })
local storedPackReturnBlock = builder:reserveBlock(storedPackWorker, { name_hint = "return", evidence = evidence })
local cyclicSetup = builder:reserveBlock(cyclicPackWorker, { name_hint = "setup", evidence = evidence })
local cyclicPreheader = builder:reserveBlock(cyclicPackWorker, { name_hint = "preheader", evidence = evidence })
local cyclicProducerBlock = builder:reserveBlock(cyclicPackWorker, { name_hint = "producer", evidence = evidence })
local cyclicEarlyContinueBlock = builder:reserveBlock(cyclicPackWorker, { name_hint = "early_continue", evidence = evidence })
local cyclicAdjustmentBlock = builder:reserveBlock(cyclicPackWorker, { name_hint = "adjustment", evidence = evidence })
local cyclicCallBlock = builder:reserveBlock(cyclicPackWorker, { name_hint = "iteration_calls", evidence = evidence })
local cyclicExit = builder:reserveBlock(cyclicPackWorker, { name_hint = "exit", evidence = evidence })
local captureFreeBlock = builder:reserveBlock(captureFreeBody, { name_hint = "entry", evidence = evidence })
local stableRootBlock = builder:reserveBlock(stableRootBody, { name_hint = "entry", evidence = evidence })
local iterationCaptureBlock = builder:reserveBlock(iterationCaptureBody, { name_hint = "entry", evidence = evidence })
local cyclicEarlyRelayBlock = builder:reserveBlock(cyclicPackWorker, { name_hint = "early_relay", evidence = evidence })
local cyclicSecondDecisionBlock = builder:reserveBlock(cyclicPackWorker, { name_hint = "second_decision", evidence = evidence })
local forwardedObserve = builder:addBlockParameter(forwardingBlock, LifterIR.Types.functionValue(), "forwarded_observe")
local alternateForwardedObserve = builder:addBlockParameter(alternateForwardingBlock, LifterIR.Types.functionValue(), "alternate_forwarded_observe")
local adjustmentObserve = builder:addBlockParameter(adjustmentBlock, LifterIR.Types.functionValue(), "adjustment_observe")
local narrowObserve = builder:addBlockParameter(narrowBlock, LifterIR.Types.functionValue(), "narrow_observe")
local wideObserve = builder:addBlockParameter(wideBlock, LifterIR.Types.functionValue(), "wide_observe")
local cyclicStableSeed = builder:addBlockParameter(cyclicPreheader, LifterIR.Types.integer(), "stable_seed")
local cyclicProducerCounter = builder:addBlockParameter(cyclicProducerBlock, LifterIR.Types.integer(), "counter")
local cyclicEarlyCounter = builder:addBlockParameter(cyclicEarlyContinueBlock, LifterIR.Types.integer(), "early_counter")
local cyclicAdjustmentCounter = builder:addBlockParameter(cyclicAdjustmentBlock, LifterIR.Types.integer(), "adjustment_counter")
local cyclicCallClosure = builder:addBlockParameter(cyclicCallBlock, LifterIR.Types.functionValue(), "iteration_capture_parameter")
local cyclicExitFirst = builder:addBlockParameter(cyclicExit, LifterIR.Types.integer(), "final_first")
local cyclicExitSecond = builder:addBlockParameter(cyclicExit, dynamic, "final_second")
local cyclicExitCounter = builder:addBlockParameter(cyclicExit, LifterIR.Types.integer(), "final_counter")
local cyclicExitEcho = builder:addBlockParameter(cyclicExit, LifterIR.Types.integer(), "final_echo")
local cyclicExitLimit = builder:addBlockParameter(cyclicExit, LifterIR.Types.integer(), "final_limit")
local cyclicExitCaptured = builder:addBlockParameter(cyclicExit, LifterIR.Types.integer(), "final_captured")
local cyclicExitProtectedOk = builder:addBlockParameter(cyclicExit, LifterIR.Types.boolean(), "final_protected_ok")
local cyclicSecondCounter = builder:addBlockParameter(
	cyclicSecondDecisionBlock,
	LifterIR.Types.integer(),
	"second_counter"
)
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, entry)
builder:setFunctionEntry(storedPackWorker, storedPackProducerBlock)
builder:setFunctionEntry(cyclicPackWorker, cyclicSetup)
builder:setFunctionEntry(captureFreeBody, captureFreeBlock)
builder:setFunctionEntry(stableRootBody, stableRootBlock)
builder:setFunctionEntry(iterationCaptureBody, iterationCaptureBlock)

local _, storedWorkerResults = builder:addInstruction(
	entry,
	LifterIR.Operation.functionRef(storedPackWorker),
	{ { type = LifterIR.Types.functionValue(), name_hint = "stored_pack_worker" } },
	{ effects = pure, evidence = evidence }
)
local storedWorkerRef = storedWorkerResults[1]
local _, cyclicWorkerResults = builder:addInstruction(
	entry,
	LifterIR.Operation.functionRef(cyclicPackWorker),
	{ { type = LifterIR.Types.functionValue(), name_hint = "cyclic_pack_worker" } },
	{ effects = pure, evidence = evidence }
)
local cyclicWorkerRef = cyclicWorkerResults[1]

local _, storedPack = builder:addOpenCall(storedPackProducerBlock, storedProducer, {}, {
	effects = dynamicCall,
	evidence = evidence,
})
local _, storedFixed = builder:addInstruction(
	storedPackAdjustmentBlock,
	LifterIR.Operation.adjustPack(storedPack),
	{
		{ type = dynamic, name_hint = "stored_first" },
		{ type = dynamic, name_hint = "stored_second" },
	},
	{ effects = pure, evidence = evidence }
)
local _, storedWide = builder:addInstruction(
	storedPackWideAdjustmentBlock,
	LifterIR.Operation.adjustPack(storedPack),
	{
		{ type = dynamic, name_hint = "stored_wide_first" },
		{ type = dynamic, name_hint = "stored_wide_second" },
		{ type = dynamic, name_hint = "stored_wide_third" },
		{ type = dynamic, name_hint = "stored_wide_fourth" },
	},
	{ effects = pure, evidence = evidence }
)

local _, fixedPack = builder:addOpenCall(entry, producer, {}, {
	effects = dynamicCall,
	evidence = evidence,
})
builder:finalizeBlock(
	entry,
	LifterIR.Terminator.branch(
		selector,
		LifterIR.Edge(forwardingBlock, { observe }),
		LifterIR.Edge(alternateForwardingBlock, { observe })
	)
)
builder:addInstruction(
	forwardingBlock,
	LifterIR.Operation.call(forwardedObserve, {}, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = dynamicCall, evidence = evidence }
)
builder:finalizeBlock(
	forwardingBlock,
	LifterIR.Terminator.jump(LifterIR.Edge(adjustmentBlock, { forwardedObserve }))
)
builder:addInstruction(
	alternateForwardingBlock,
	LifterIR.Operation.call(alternateForwardedObserve, {}, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = dynamicCall, evidence = evidence }
)
builder:finalizeBlock(
	alternateForwardingBlock,
	LifterIR.Terminator.jump(LifterIR.Edge(adjustmentBlock, { alternateForwardedObserve }))
)
local _, fixedResults = builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.adjustPack(fixedPack),
	{
		{ type = LifterIR.Types.functionValue(), name_hint = "marker" },
		{ type = dynamic, name_hint = "missing" },
		{ type = LifterIR.Types.integer(), name_hint = "third" },
		{ type = dynamic, name_hint = "filled" },
	},
	{ effects = pure, evidence = evidence }
)

local _, protectedPack = builder:addOpenProtectedCall(adjustmentBlock, protectedProducer, nil, {}, {
	effects = protectedCall,
	evidence = evidence,
})
builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.call(adjustmentObserve, {}, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = dynamicCall, evidence = evidence }
)
local _, protectedResults = builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.adjustPack(protectedPack),
	{
		{ type = LifterIR.Types.boolean(), name_hint = "protected_ok" },
		{ type = dynamic, name_hint = "protected_first" },
		{ type = dynamic, name_hint = "protected_second" },
		{ type = dynamic, name_hint = "protected_third" },
	},
	{ effects = pure, evidence = evidence }
)

local _, resumePack = builder:addOpenCoroutineResume(adjustmentBlock, resumeThread, {}, {
	effects = coroutineResume,
	evidence = evidence,
})
builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.call(adjustmentObserve, {}, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = dynamicCall, evidence = evidence }
)
local _, resumeResults = builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.adjustPack(resumePack),
	{
		{ type = LifterIR.Types.boolean(), name_hint = "resume_ok" },
		{ type = dynamic, name_hint = "resume_first" },
		{ type = dynamic, name_hint = "resume_second" },
		{ type = dynamic, name_hint = "resume_third" },
	},
	{ effects = pure, evidence = evidence }
)

local _, namecallPack = builder:addOpenNamecall(adjustmentBlock, namecallReceiver, "produce", {}, {
	effects = namecall,
	evidence = evidence,
})
builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.call(adjustmentObserve, {}, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = dynamicCall, evidence = evidence }
)
local _, namecallResults = builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.adjustPack(namecallPack),
	{
		{ type = dynamic, name_hint = "namecall_first" },
		{ type = dynamic, name_hint = "namecall_second" },
		{ type = dynamic, name_hint = "namecall_third" },
		{ type = dynamic, name_hint = "namecall_fourth" },
	},
	{ effects = pure, evidence = evidence }
)

local _, yieldPack = builder:addOpenCoroutineYield(
	adjustmentBlock,
	{ fixedResults[1], fixedResults[2], fixedResults[3] },
	{ effects = coroutineYield, evidence = evidence }
)
builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.call(adjustmentObserve, {}, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = dynamicCall, evidence = evidence }
)
local _, yieldResults = builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.adjustPack(yieldPack),
	{
		{ type = LifterIR.Types.integer(), name_hint = "yield_first" },
		{ type = dynamic, name_hint = "yield_second" },
		{ type = LifterIR.Types.integer(), name_hint = "yield_third" },
		{ type = dynamic, name_hint = "yield_fourth" },
	},
	{ effects = pure, evidence = evidence }
)

local _, discardedPack = builder:addOpenCall(adjustmentBlock, producer, {}, {
	effects = dynamicCall,
	evidence = evidence,
})
builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.call(adjustmentObserve, {}, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = dynamicCall, evidence = evidence }
)
builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.adjustPack(discardedPack),
	{},
	{ effects = pure, evidence = evidence }
)

local _, repeatedPack = builder:addOpenCall(adjustmentBlock, producer, {}, {
	effects = dynamicCall,
	evidence = evidence,
})
local _, nonadjacentProbeResults = builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.environmentGet(LifterIR.EnvironmentTarget.ambient(), "pack_order_probe"),
	{ { type = LifterIR.Types.functionValue(), name_hint = "nonadjacent_probe" } },
	{ effects = LifterIR.Effects.semanticTableRead(), evidence = evidence }
)
local _, nonadjacentProbePack = builder:addValuePack(adjustmentBlock, { nonadjacentProbeResults[1] }, {
	effects = pure,
	evidence = evidence,
})
builder:addInstruction(
	adjustmentBlock,
	LifterIR.Operation.call(mutateProbe, {}, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = dynamicCall, evidence = evidence }
)
builder:finalizeBlock(adjustmentBlock, LifterIR.Terminator.jump(LifterIR.Edge(packConsumerBlock)))
builder:addInstruction(
	packConsumerBlock,
	LifterIR.Operation.call(adjustmentObserve, {}, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = dynamicCall, evidence = evidence }
)
builder:finalizeBlock(
	packConsumerBlock,
	LifterIR.Terminator.branch(
		selector,
		LifterIR.Edge(narrowBlock, { adjustmentObserve }),
		LifterIR.Edge(wideBlock, { adjustmentObserve })
	)
)
builder:addInstruction(
	narrowBlock,
	LifterIR.Operation.call(narrowObserve, {}, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = dynamicCall, evidence = evidence }
)
local _, narrowProbeAdjusted = builder:addInstruction(
	narrowBlock,
	LifterIR.Operation.adjustPack(nonadjacentProbePack),
	{ { type = LifterIR.Types.functionValue(), name_hint = "narrow_snapshotted_probe" } },
	{ effects = pure, evidence = evidence }
)
local _, repeatedResults = builder:addInstruction(
	narrowBlock,
	LifterIR.Operation.adjustPack(repeatedPack),
	{
		{ type = LifterIR.Types.integer(), name_hint = "repeated_first" },
		{ type = dynamic, name_hint = "repeated_second" },
	},
	{ effects = pure, evidence = evidence }
)
builder:addInstruction(
	wideBlock,
	LifterIR.Operation.call(wideObserve, {}, LifterIR.ResultArity.fixed(0)),
	{},
	{ effects = dynamicCall, evidence = evidence }
)
local _, wideProbeAdjusted = builder:addInstruction(
	wideBlock,
	LifterIR.Operation.adjustPack(nonadjacentProbePack),
	{ { type = LifterIR.Types.functionValue(), name_hint = "wide_snapshotted_probe" } },
	{ effects = pure, evidence = evidence }
)
local _, canonicalResults = builder:addInstruction(
	wideBlock,
	LifterIR.Operation.adjustPack(repeatedPack),
	{
		{ type = LifterIR.Types.integer(), name_hint = "canonical_first" },
		{ type = dynamic, name_hint = "canonical_second" },
		{ type = LifterIR.Types.integer(), name_hint = "canonical_third" },
	},
	{ effects = pure, evidence = evidence }
)

local _, cyclicZeroResults = builder:addInstruction(
	cyclicPreheader,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = LifterIR.Types.integer(), name_hint = "zero" } },
	{ effects = pure, evidence = evidence }
)
local _, cyclicOneResults = builder:addInstruction(
	cyclicPreheader,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = LifterIR.Types.integer(), name_hint = "one" } },
	{ effects = pure, evidence = evidence }
)
local _, cyclicSeedResults = builder:addInstruction(
	cyclicSetup,
	LifterIR.Operation.constant(LifterIR.Literal.integer("7")),
	{ { type = LifterIR.Types.integer(), name_hint = "stable_seed" } },
	{ effects = pure, evidence = evidence }
)
local _, cyclicSharedInitialResults = builder:addInstruction(
	cyclicSetup,
	LifterIR.Operation.constant(LifterIR.Literal.integer("5")),
	{ { type = LifterIR.Types.integer(), name_hint = "shared_initial" } },
	{ effects = pure, evidence = evidence }
)
local cyclicSharedState = builder:addAllocatedPlace(
	cyclicSetup,
	cyclicSharedInitialResults[1],
	LifterIR.Types.integer(),
	"shared_state",
	evidence
)
local capturedSharedState = builder:addPlaceCapture(
	stableRootBody,
	LifterIR.Types.integer(),
	"captured_shared_state",
	evidence
)
local capturedIterationFirst = builder:addValueCapture(
	iterationCaptureBody,
	LifterIR.Types.integer(),
	"captured_iteration_first",
	evidence
)
local capturedIterationState = builder:addPlaceCapture(
	iterationCaptureBody,
	LifterIR.Types.integer(),
	"captured_iteration_state",
	evidence
)
local _, cyclicPack = builder:addOpenCall(cyclicProducerBlock, cyclicProducer, {}, {
	effects = dynamicCall,
	evidence = evidence,
})
local _, cyclicEarlyNextResults = builder:addInstruction(
	cyclicProducerBlock,
	LifterIR.Operation.binary("add", cyclicProducerCounter, cyclicOneResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "early_next_counter" } },
	{ effects = pure, evidence = evidence }
)
local _, cyclicSkipResults = builder:addInstruction(
	cyclicProducerBlock,
	LifterIR.Operation.call(cyclicSkip, { cyclicProducerCounter }, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.boolean(), name_hint = "skip_consumers" } },
	{ effects = dynamicCall, evidence = evidence }
)
local _, cyclicAdjustedResults = builder:addInstruction(
	cyclicAdjustmentBlock,
	LifterIR.Operation.adjustPack(cyclicPack),
	{
		{ type = LifterIR.Types.integer(), name_hint = "cyclic_first" },
		{ type = dynamic, name_hint = "cyclic_second" },
	},
	{ effects = pure, evidence = evidence }
)
local cyclicIterationState = builder:addAllocatedPlace(
	cyclicAdjustmentBlock,
	cyclicAdjustedResults[1],
	LifterIR.Types.integer(),
	"iteration_state",
	evidence
)
local _, captureFreeClosureResults = builder:addInstruction(
	cyclicAdjustmentBlock,
	LifterIR.Operation.makeClosure(captureFreeBody, {}),
	{ { type = LifterIR.Types.functionValue(), name_hint = "capture_free" } },
	{ effects = pure, evidence = evidence }
)
local _, captureFreeCallResults = builder:addInstruction(
	cyclicAdjustmentBlock,
	LifterIR.Operation.call(
		captureFreeClosureResults[1],
		{ cyclicAdjustedResults[1] },
		LifterIR.ResultArity.fixed(1)
	),
	{ { type = LifterIR.Types.integer(), name_hint = "echoed_first" } },
	{ effects = dynamicCall, evidence = evidence }
)
local _, stableRootClosureResults = builder:addInstruction(
	cyclicAdjustmentBlock,
	LifterIR.Operation.makeClosure(stableRootBody, {
		LifterIR.CaptureBinding.value(cyclicLimit),
		LifterIR.CaptureBinding.value(cyclicStableSeed),
		LifterIR.CaptureBinding.place(cyclicSharedState),
	}),
	{ { type = LifterIR.Types.functionValue(), name_hint = "stable_root" } },
	{ effects = pure, evidence = evidence }
)
local _, stableRootCallResults = builder:addInstruction(
	cyclicAdjustmentBlock,
	LifterIR.Operation.call(stableRootClosureResults[1], {}, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.integer(), name_hint = "stable_limit" } },
	{ effects = dynamicCall, evidence = evidence }
)
local _, iterationCaptureClosureResults = builder:addInstruction(
	cyclicAdjustmentBlock,
	LifterIR.Operation.makeClosure(iterationCaptureBody, {
		LifterIR.CaptureBinding.value(cyclicAdjustedResults[1]),
		LifterIR.CaptureBinding.place(cyclicIterationState),
	}),
	{ { type = LifterIR.Types.functionValue(), name_hint = "iteration_capture" } },
	{ effects = pure, evidence = evidence }
)
local _, iterationCaptureAliasResults = builder:addInstruction(
	cyclicAdjustmentBlock,
	LifterIR.Operation.copy(iterationCaptureClosureResults[1]),
	{ { type = LifterIR.Types.functionValue(), name_hint = "iteration_capture_alias" } },
	{ effects = pure, evidence = evidence }
)
local _, iterationCaptureCallResults = builder:addInstruction(
	cyclicCallBlock,
	LifterIR.Operation.call(cyclicCallClosure, {}, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.integer(), name_hint = "captured_first" } },
	{ effects = dynamicCall, evidence = evidence }
)
local _, iterationCaptureSecondCallResults = builder:addInstruction(
	cyclicCallBlock,
	LifterIR.Operation.call(cyclicCallClosure, {}, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.integer(), name_hint = "captured_second" } },
	{ effects = dynamicCall, evidence = evidence }
)
local _, iterationCaptureCombinedResults = builder:addInstruction(
	cyclicCallBlock,
	LifterIR.Operation.binary("add", iterationCaptureCallResults[1], iterationCaptureSecondCallResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "captured_combined" } },
	{ effects = pure, evidence = evidence }
)
local _, iterationCaptureProtectedPack = builder:addOpenProtectedCall(
	cyclicCallBlock,
	cyclicFailure,
	cyclicCallClosure,
	{},
	{ effects = protectedCall, evidence = evidence }
)
local _, iterationCaptureProtectedResults = builder:addInstruction(
	cyclicCallBlock,
	LifterIR.Operation.adjustPack(iterationCaptureProtectedPack),
	{
		{ type = LifterIR.Types.boolean(), name_hint = "captured_protected_ok" },
		{ type = LifterIR.Types.integer(), name_hint = "captured_protected_value" },
	},
	{ effects = pure, evidence = evidence }
)
local _, iterationCaptureTotalResults = builder:addInstruction(
	cyclicCallBlock,
	LifterIR.Operation.binary("add", iterationCaptureCombinedResults[1], iterationCaptureProtectedResults[2]),
	{ { type = LifterIR.Types.integer(), name_hint = "captured_total" } },
	{ effects = pure, evidence = evidence }
)
local _, cyclicNextResults = builder:addInstruction(
	cyclicCallBlock,
	LifterIR.Operation.binary("add", cyclicAdjustmentCounter, cyclicOneResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "next_counter" } },
	{ effects = pure, evidence = evidence }
)
local _, cyclicContinueResults = builder:addInstruction(
	cyclicCallBlock,
	LifterIR.Operation.binary("less", cyclicNextResults[1], cyclicLimit),
	{ { type = LifterIR.Types.boolean(), name_hint = "continue_loop" } },
	{ effects = pure, evidence = evidence }
)

builder:finalizeBlock(
	storedPackProducerBlock,
	LifterIR.Terminator.jump(LifterIR.Edge(storedPackAdjustmentBlock, {}))
)
builder:finalizeBlock(
	storedPackAdjustmentBlock,
	LifterIR.Terminator.jump(LifterIR.Edge(storedPackWideAdjustmentBlock, {}))
)
builder:finalizeBlock(
	storedPackWideAdjustmentBlock,
	LifterIR.Terminator.jump(LifterIR.Edge(storedPackReturnBlock, {}))
)
builder:finalizeBlock(
	storedPackReturnBlock,
	LifterIR.Terminator.returnExpanded(
		{ storedFixed[1], storedFixed[2], storedWide[1], storedWide[2], storedWide[3], storedWide[4] },
		storedPack
	)
)
builder:finalizeBlock(cyclicSetup, LifterIR.Terminator.jump(LifterIR.Edge(cyclicPreheader, { cyclicSeedResults[1] })))
builder:finalizeBlock(
	cyclicPreheader,
	LifterIR.Terminator.jump(LifterIR.Edge(cyclicProducerBlock, { cyclicZeroResults[1] }))
)
local _, cyclicEarlyForwardedResults = builder:addInstruction(
	cyclicEarlyContinueBlock,
	LifterIR.Operation.copy(cyclicEarlyCounter),
	{ { type = LifterIR.Types.integer(), name_hint = "forwarded_early_counter" } },
	{ effects = pure, evidence = evidence }
)
local cyclicRelayCounter = builder:addBlockParameter(
	cyclicEarlyRelayBlock,
	LifterIR.Types.integer(),
	"relayed_early_counter"
)
local _, cyclicRelayForwardedResults = builder:addInstruction(
	cyclicEarlyRelayBlock,
	LifterIR.Operation.copy(cyclicRelayCounter),
	{ { type = LifterIR.Types.integer(), name_hint = "copied_relayed_early_counter" } },
	{ effects = pure, evidence = evidence }
)
local _, cyclicSecondSkipResults = builder:addInstruction(
	cyclicSecondDecisionBlock,
	LifterIR.Operation.call(cyclicSecondSkip, { cyclicSecondCounter }, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.boolean(), name_hint = "second_skip_consumers" } },
	{ effects = dynamicCall, evidence = evidence }
)
local _, cyclicSecondForwardedResults = builder:addInstruction(
	cyclicSecondDecisionBlock,
	LifterIR.Operation.copy(cyclicEarlyNextResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "second_forwarded_early_counter" } },
	{ effects = pure, evidence = evidence }
)
builder:finalizeBlock(
	cyclicProducerBlock,
	LifterIR.Terminator.branch(
		cyclicSkipResults[1],
		LifterIR.Edge(cyclicEarlyContinueBlock, { cyclicEarlyNextResults[1] }),
		LifterIR.Edge(cyclicSecondDecisionBlock, { cyclicProducerCounter })
	)
)
builder:finalizeBlock(
	cyclicEarlyContinueBlock,
	LifterIR.Terminator.jump(LifterIR.Edge(cyclicEarlyRelayBlock, { cyclicEarlyForwardedResults[1] }))
)
builder:finalizeBlock(
	cyclicEarlyRelayBlock,
	LifterIR.Terminator.jump(LifterIR.Edge(cyclicProducerBlock, { cyclicRelayForwardedResults[1] }))
)
builder:finalizeBlock(
	cyclicSecondDecisionBlock,
	LifterIR.Terminator.branch(
		cyclicSecondSkipResults[1],
		LifterIR.Edge(cyclicEarlyRelayBlock, { cyclicSecondForwardedResults[1] }),
		LifterIR.Edge(cyclicAdjustmentBlock, { cyclicSecondCounter })
	)
)
builder:finalizeBlock(
	cyclicAdjustmentBlock,
	LifterIR.Terminator.jump(LifterIR.Edge(cyclicCallBlock, { iterationCaptureAliasResults[1] }))
)
builder:finalizeBlock(
	cyclicCallBlock,
	LifterIR.Terminator.branch(
		cyclicContinueResults[1],
		LifterIR.Edge(cyclicProducerBlock, { cyclicNextResults[1] }),
		LifterIR.Edge(
			cyclicExit,
			{
				cyclicAdjustedResults[1],
				cyclicAdjustedResults[2],
				cyclicNextResults[1],
				captureFreeCallResults[1],
				stableRootCallResults[1],
				iterationCaptureTotalResults[1],
				iterationCaptureProtectedResults[1],
			}
		)
	)
)
builder:finalizeBlock(
	cyclicExit,
	LifterIR.Terminator.returnExpanded(
		{
			cyclicExitFirst,
			cyclicExitSecond,
			cyclicExitCounter,
			cyclicExitEcho,
			cyclicExitLimit,
			cyclicExitCaptured,
			cyclicExitProtectedOk,
		},
		cyclicPack
	)
)
builder:finalizeBlock(captureFreeBlock, LifterIR.Terminator.returnValues({ captureFreeValue }))
local _, capturedIterationStateResults = builder:addInstruction(
	iterationCaptureBlock,
	LifterIR.Operation.placeRead(capturedIterationState),
	{ { type = LifterIR.Types.integer(), name_hint = "captured_iteration_state" } },
	{ effects = LifterIR.Effects.placeRead(), evidence = evidence }
)
local _, capturedIterationTotalResults = builder:addInstruction(
	iterationCaptureBlock,
	LifterIR.Operation.binary("add", capturedIterationFirst, capturedIterationStateResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "captured_iteration_total" } },
	{ effects = pure, evidence = evidence }
)
builder:finalizeBlock(iterationCaptureBlock, LifterIR.Terminator.returnValues({ capturedIterationTotalResults[1] }))
local _, stableContextResults = builder:addInstruction(
	stableRootBlock,
	LifterIR.Operation.binary("add", capturedLimit, capturedSeed),
	{ { type = LifterIR.Types.integer(), name_hint = "stable_context" } },
	{ effects = pure, evidence = evidence }
)
local _, capturedSharedResults = builder:addInstruction(
	stableRootBlock,
	LifterIR.Operation.placeRead(capturedSharedState),
	{ { type = LifterIR.Types.integer(), name_hint = "shared_value" } },
	{ effects = LifterIR.Effects.placeRead(), evidence = evidence }
)
local _, stableTotalResults = builder:addInstruction(
	stableRootBlock,
	LifterIR.Operation.binary("add", stableContextResults[1], capturedSharedResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "stable_total" } },
	{ effects = pure, evidence = evidence }
)
builder:finalizeBlock(stableRootBlock, LifterIR.Terminator.returnValues({ stableTotalResults[1] }))

local function returnedWith(tail: { number }, snapshottedProbe: any): { number }
	local returned = {}
	for _, value in fixedResults do
		table.insert(returned, value)
	end
	for _, value in protectedResults do
		table.insert(returned, value)
	end
	for _, value in resumeResults do
		table.insert(returned, value)
	end
	for _, value in namecallResults do
		table.insert(returned, value)
	end
	for _, value in yieldResults do
		table.insert(returned, value)
	end
	for _, value in tail do
		table.insert(returned, value)
	end
	table.insert(returned, snapshottedProbe)
	table.insert(returned, storedWorkerRef)
	table.insert(returned, cyclicWorkerRef)
	return returned
end
builder:finalizeBlock(narrowBlock, LifterIR.Terminator.returnValues(returnedWith(repeatedResults, narrowProbeAdjusted[1])))
builder:finalizeBlock(wideBlock, LifterIR.Terminator.returnValues(returnedWith(canonicalResults, wideProbeAdjusted[1])))
builder:finalizeFunction(chunk)
builder:finalizeFunction(storedPackWorker)
builder:finalizeFunction(cyclicPackWorker)
builder:finalizeFunction(captureFreeBody)
builder:finalizeFunction(stableRootBody)
builder:finalizeFunction(iterationCaptureBody)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
