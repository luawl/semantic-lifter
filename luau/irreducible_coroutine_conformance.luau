--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

if process.args[1] == "audit" then
	local Audit = require("./irreducible_coroutine_audit")
	local inputPath = process.args[2]
	local resolvedPath = process.args[3]
	local reresolvedPath = process.args[4]
	local generatedPath = process.args[5]
	assert(inputPath ~= nil and resolvedPath ~= nil and reresolvedPath ~= nil and generatedPath ~= nil, "expected audit artifacts")
	Audit.run(inputPath, resolvedPath, reresolvedPath, generatedPath)
	return
end

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-irreducible-coroutine-control")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-irreducible-coroutine-control")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local integer = LifterIR.Types.integer()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local probe = builder:reserveFunction({
	name_hint = "irreducible_coroutine_probe",
	is_variadic = true,
	evidence = evidence,
})
local worker = builder:reserveFunction({
	name_hint = "irreducible_coroutine_worker",
	is_variadic = true,
	evidence = evidence,
})
local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local probeEntry = builder:reserveBlock(probe, { name_hint = "probe_entry", evidence = evidence })
local probePrimary = builder:reserveBlock(probe, { name_hint = "probe_header", evidence = evidence })
local probeSecondary = builder:reserveBlock(probe, { name_hint = "resume_entry", evidence = evidence })
local probeExit = builder:reserveBlock(probe, { name_hint = "probe_exit", evidence = evidence })
local entry = builder:reserveBlock(worker, { name_hint = "entry", evidence = evidence })
local primary = builder:reserveBlock(worker, { name_hint = "loop_header", evidence = evidence })
local secondary = builder:reserveBlock(worker, { name_hint = "yield_entry", evidence = evidence })
local exit = builder:reserveBlock(worker, { name_hint = "exit", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(probe, probeEntry)
builder:setFunctionEntry(worker, entry)

local probeStartSecondary = builder:addParameter(probe, LifterIR.Types.boolean(), "start_secondary")
local probeWorkerStartSecondary = builder:addParameter(probe, LifterIR.Types.boolean(), "worker_start_secondary")
local probeResumeValue = builder:addParameter(probe, integer, "resume_value")
local probeVerifier = builder:addParameter(probe, LifterIR.Types.functionValue(), "verifier")
local probeVarargs = builder:addVarargPack(probe, evidence)
local probePrimaryCounter = builder:addBlockParameter(probePrimary, integer, "probe_counter")
local probePrimarySummary = builder:addBlockParameter(probePrimary, integer, "probe_summary")
local probeSecondaryCounter = builder:addBlockParameter(probeSecondary, integer, "probe_resume_counter")
local probeSecondarySummary = builder:addBlockParameter(probeSecondary, integer, "probe_resume_summary")
local probeExitSummary = builder:addBlockParameter(probeExit, integer, "probe_final_summary")
local startSecondary = builder:addParameter(worker, LifterIR.Types.boolean(), "start_secondary")
local workerVarargs = builder:addVarargPack(worker, evidence)
local primaryCounter = builder:addBlockParameter(primary, integer, "counter")
local secondaryCounter = builder:addBlockParameter(secondary, integer, "yield_counter")
local exitCounter = builder:addBlockParameter(exit, integer, "final_counter")

local _, exportedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(probe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "irreducible_coroutine_probe" } },
	{ effects = pure, evidence = evidence }
)
local _, probeZeroResults = builder:addInstruction(
	probeEntry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = integer, name_hint = "probe_zero" } },
	{ effects = pure, evidence = evidence }
)
local _, probeUnsetResults = builder:addInstruction(
	probeEntry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("-1")),
	{ { type = integer, name_hint = "probe_unset" } },
	{ effects = pure, evidence = evidence }
)
local _, probeHeaderZeroResults = builder:addInstruction(
	probePrimary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = integer, name_hint = "probe_header_zero" } },
	{ effects = pure, evidence = evidence }
)
local _, probeNeedsRunResults = builder:addInstruction(
	probePrimary,
	LifterIR.Operation.binary("equal", probePrimaryCounter, probeHeaderZeroResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "probe_needs_run" } },
	{ effects = pure, evidence = evidence }
)
local _, workerReferenceResults = builder:addInstruction(
	probeSecondary,
	LifterIR.Operation.functionRef(worker),
	{ { type = LifterIR.Types.functionValue(), name_hint = "coroutine_worker" } },
	{ effects = pure, evidence = evidence }
)
local _, threadResults = builder:addInstruction(
	probeSecondary,
	LifterIR.Operation.coroutineCreate(workerReferenceResults[1]),
	{ { type = LifterIR.Types.thread(), name_hint = "worker_thread" } },
	{ effects = LifterIR.Effects.coroutineCreate(), evidence = evidence }
)
local _, firstResumeResults = builder:addInstruction(
	probeSecondary,
	LifterIR.Operation.coroutineResume(
		threadResults[1],
		{ probeWorkerStartSecondary },
		LifterIR.ResultArity.fixed(5),
		probeVarargs
	),
	{
		{ type = LifterIR.Types.boolean(), name_hint = "first_resume_ok" },
		{ type = integer, name_hint = "yielded_counter" },
		{ type = LifterIR.Types.string(), name_hint = "yielded_head" },
		{ type = LifterIR.Types.nilValue(), name_hint = "yielded_hole" },
		{ type = integer, name_hint = "yielded_tail" },
	},
	{ effects = LifterIR.Effects.coroutineResume(), evidence = evidence }
)
local _, secondResumePack = builder:addOpenCoroutineResume(
	probeSecondary,
	threadResults[1],
	{ probeResumeValue },
	{
		effects = LifterIR.Effects.coroutineResume(),
		evidence = evidence,
		result_pack_shape = LifterIR.PackShape.open({ LifterIR.Types.boolean(), integer }),
	}
)
local _, secondResumeResults = builder:addInstruction(
	probeSecondary,
	LifterIR.Operation.adjustPack(secondResumePack),
	{
		{ type = LifterIR.Types.boolean(), name_hint = "second_resume_ok" },
		{ type = integer, name_hint = "final_counter" },
	},
	{ effects = pure, evidence = evidence }
)
local _, verifierResults = builder:addInstruction(
	probeSecondary,
	LifterIR.Operation.call(
		probeVerifier,
		{
			firstResumeResults[1],
			firstResumeResults[2],
			firstResumeResults[3],
			firstResumeResults[4],
			firstResumeResults[5],
			secondResumeResults[1],
			secondResumeResults[2],
		},
		LifterIR.ResultArity.fixed(1)
	),
	{ { type = integer, name_hint = "verified_counter" } },
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local _, probeOneResults = builder:addInstruction(
	probeSecondary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = integer, name_hint = "probe_one" } },
	{ effects = pure, evidence = evidence }
)
local _, zeroResults = builder:addInstruction(
	entry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = integer, name_hint = "zero" } },
	{ effects = pure, evidence = evidence }
)
local _, oneResults = builder:addInstruction(
	primary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = integer, name_hint = "one" } },
	{ effects = pure, evidence = evidence }
)
local _, nextResults = builder:addInstruction(
	primary,
	LifterIR.Operation.binary("add", primaryCounter, oneResults[1]),
	{ { type = integer, name_hint = "next_counter" } },
	{ effects = pure, evidence = evidence }
)
local _, limitResults = builder:addInstruction(
	primary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("3")),
	{ { type = integer, name_hint = "limit" } },
	{ effects = pure, evidence = evidence }
)
local _, continueResults = builder:addInstruction(
	primary,
	LifterIR.Operation.binary("less", nextResults[1], limitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "continue_loop" } },
	{ effects = pure, evidence = evidence }
)
local _, resumedPack = builder:addOpenCoroutineYield(
	secondary,
	{ secondaryCounter },
	{
		effects = LifterIR.Effects.coroutineYield(),
		evidence = evidence,
		result_pack_shape = LifterIR.PackShape.open({ integer }),
	},
	workerVarargs
)
local _, resumedResults = builder:addInstruction(
	secondary,
	LifterIR.Operation.adjustPack(resumedPack),
	{ { type = integer, name_hint = "resumed_counter" } },
	{ effects = pure, evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportedResults[1] }))
builder:finalizeBlock(
	probeEntry,
	LifterIR.Terminator.branch(
		probeStartSecondary,
		LifterIR.Edge(probeSecondary, { probeZeroResults[1], probeUnsetResults[1] }),
		LifterIR.Edge(probePrimary, { probeZeroResults[1], probeUnsetResults[1] })
	)
)
builder:finalizeBlock(
	probePrimary,
	LifterIR.Terminator.branch(
		probeNeedsRunResults[1],
		LifterIR.Edge(probeSecondary, { probePrimaryCounter, probePrimarySummary }),
		LifterIR.Edge(probeExit, { probePrimarySummary })
	)
)
builder:finalizeBlock(
	probeSecondary,
	LifterIR.Terminator.jump(LifterIR.Edge(probePrimary, { probeOneResults[1], verifierResults[1] }))
)
builder:finalizeBlock(probeExit, LifterIR.Terminator.returnValues({ probeExitSummary }))
builder:finalizeBlock(
	entry,
	LifterIR.Terminator.branch(
		startSecondary,
		LifterIR.Edge(secondary, { zeroResults[1] }),
		LifterIR.Edge(primary, { zeroResults[1] })
	)
)
builder:finalizeBlock(
	primary,
	LifterIR.Terminator.branch(
		continueResults[1],
		LifterIR.Edge(secondary, { nextResults[1] }),
		LifterIR.Edge(exit, { nextResults[1] })
	)
)
builder:finalizeBlock(secondary, LifterIR.Terminator.jump(LifterIR.Edge(primary, { resumedResults[1] })))
builder:finalizeBlock(exit, LifterIR.Terminator.returnValues({ exitCounter }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(probe)
builder:finalizeFunction(worker)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
