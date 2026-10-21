--!strict
-- Dominating-exit regression: the native inner loop's exit is the enclosing loop header,
-- whose parameters are live in the native loop body. Both numeric and semantic-normalized workers
-- must preserve the break value without applying the exhaustion-edge copy to other exits.
local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("iteration-dominating-break-exit")
local proof = builder:addEvidence("dynamic_fixture", "fixture:iteration-dominating-break-exit")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local dynamic = LifterIR.Types.dynamic()
local boolean = LifterIR.Types.boolean()
local number = LifterIR.Types.number()
local functionValue = LifterIR.Types.functionValue()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)

type Variant = "numeric" | "semantic"

local function addWorker(variant: Variant): number
	local worker = builder:reserveFunction({ name_hint = `{variant}_dominating_worker`, evidence = evidence })
	local n = builder:addParameter(worker, number, "n")
	local rounds = builder:addParameter(worker, number, "rounds")
	local pick = builder:addParameter(worker, functionValue, "pick")
	local stateType = if variant == "numeric" then number else dynamic
	local accType = if variant == "numeric" then number else dynamic

	local entry = builder:reserveBlock(worker, { name_hint = "entry", evidence = evidence })
	local outerHeader = builder:reserveBlock(worker, { name_hint = "outer_header", evidence = evidence })
	local outerBody = builder:reserveBlock(worker, { name_hint = "outer_body", evidence = evidence })
	local innerHeader = builder:reserveBlock(worker, { name_hint = "inner_header", evidence = evidence })
	local innerBody = builder:reserveBlock(worker, { name_hint = "inner_body", evidence = evidence })
	local done = builder:reserveBlock(worker, { name_hint = "done", evidence = evidence })
	builder:setFunctionEntry(worker, entry)

	local acc = builder:addBlockParameter(outerHeader, accType, "acc")
	local round = builder:addBlockParameter(outerHeader, number, "round")
	local innerControl = builder:addBlockParameter(innerHeader, stateType, "inner_control")
	local innerLimit = builder:addBlockParameter(innerHeader, stateType, "inner_limit")
	local innerStep = builder:addBlockParameter(innerHeader, stateType, "inner_step")
	local innerFlag = builder:addBlockParameter(innerHeader, boolean, "inner_initial")
	local index = builder:addBlockParameter(innerBody, stateType, "index")
	local result = builder:addBlockParameter(done, accType, "result")

	local _, exported = builder:addInstruction(
		chunkBlock,
		LifterIR.Operation.functionRef(worker),
		{ { type = functionValue, name_hint = "dominating_worker" } },
		{ effects = pure, evidence = evidence }
	)
	local _, zero = builder:addInstruction(
		entry,
		LifterIR.Operation.constant(LifterIR.Literal.number(0)),
		{ { type = number, name_hint = "zero" } },
		{ effects = pure, evidence = evidence }
	)
	local _, one = builder:addInstruction(
		entry,
		LifterIR.Operation.constant(LifterIR.Literal.number(1)),
		{ { type = number, name_hint = "one" } },
		{ effects = pure, evidence = evidence }
	)
	local _, hundred = builder:addInstruction(
		entry,
		LifterIR.Operation.constant(LifterIR.Literal.number(100)),
		{ { type = number, name_hint = "hundred" } },
		{ effects = pure, evidence = evidence }
	)
	local _, entryFlag = builder:addInstruction(
		entry,
		LifterIR.Operation.constant(LifterIR.Literal.boolean(variant == "numeric")),
		{ { type = boolean, name_hint = "entry_flag" } },
		{ effects = pure, evidence = evidence }
	)
	local _, laterFlag = builder:addInstruction(
		entry,
		LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
		{ { type = boolean, name_hint = "later_flag" } },
		{ effects = pure, evidence = evidence }
	)
	local _, more = builder:addInstruction(
		outerHeader,
		LifterIR.Operation.binary("less", round, rounds, "primitive"),
		{ { type = boolean, name_hint = "more" } },
		{ effects = pure, evidence = evidence }
	)
	local _, nextRound = builder:addInstruction(
		outerBody,
		LifterIR.Operation.binary("add", round, one[1], "primitive"),
		{ { type = number, name_hint = "next_round" } },
		{ effects = pure, evidence = evidence }
	)
	local _, bumped = builder:addInstruction(
		outerBody,
		LifterIR.Operation.binary("add", acc, hundred[1], "semantic"),
		{ { type = accType, name_hint = "bumped" } },
		{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
	)

	local transition
	if variant == "numeric" then
		local _, results = builder:addInstruction(
			innerHeader,
			LifterIR.Operation.numericForNext(innerControl, innerLimit, innerStep, innerFlag),
			{
				{ type = boolean, name_hint = "has_value" },
				{ type = number, name_hint = "next_limit" },
				{ type = number, name_hint = "next_step" },
				{ type = number, name_hint = "next_control" },
			},
			{ effects = LifterIR.Effects.numericForNext(), evidence = evidence }
		)
		transition = results
	else
		local _, results = builder:addInstruction(
			innerHeader,
			LifterIR.Operation.numericForNext(innerControl, innerLimit, innerStep, innerFlag, LifterIR.NumericForMode.semanticNormalized),
			{
				{ type = boolean, name_hint = "has_value" },
				{ type = dynamic, name_hint = "next_limit" },
				{ type = dynamic, name_hint = "next_step" },
				{ type = dynamic, name_hint = "next_control" },
			},
			{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
		)
		transition = results
	end
	local _, hit = builder:addInstruction(
		innerBody,
		LifterIR.Operation.call(pick, { index, acc }, LifterIR.ResultArity.fixed(1)),
		{ { type = dynamic, name_hint = "hit" } },
		{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
	)

	local initialControl = if variant == "numeric" then one[1] else zero[1]
	builder:finalizeBlock(entry, LifterIR.Terminator.jump(LifterIR.Edge(outerHeader, { zero[1], zero[1] })))
	builder:finalizeBlock(
		outerHeader,
		LifterIR.Terminator.branch(more[1], LifterIR.Edge(outerBody, {}), LifterIR.Edge(done, { acc }))
	)
	builder:finalizeBlock(
		outerBody,
		LifterIR.Terminator.jump(LifterIR.Edge(innerHeader, { initialControl, n, one[1], entryFlag[1] }))
	)
	builder:finalizeBlock(
		innerHeader,
		LifterIR.Terminator.branch(transition[1], LifterIR.Edge(innerBody, { transition[4] }), LifterIR.Edge(outerHeader, { bumped[1], nextRound[1] }))
	)
	builder:finalizeBlock(
		innerBody,
		LifterIR.Terminator.branch(
			hit[1],
			LifterIR.Edge(outerHeader, { index, nextRound[1] }),
			LifterIR.Edge(innerHeader, { transition[4], transition[2], transition[3], laterFlag[1] })
		)
	)
	builder:finalizeBlock(done, LifterIR.Terminator.returnValues({ result }))
	builder:finalizeFunction(worker)
	return worker
end

local numericWorker = addWorker("numeric")
local semanticWorker = addWorker("semantic")
local _, numericExport = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(numericWorker),
	{ { type = functionValue, name_hint = "numeric_worker" } },
	{ effects = pure, evidence = evidence }
)
local _, semanticExport = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(semanticWorker),
	{ { type = functionValue, name_hint = "semantic_worker" } },
	{ effects = pure, evidence = evidence }
)
builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ numericExport[1], semanticExport[1] }))
builder:finalizeFunction(chunk)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
