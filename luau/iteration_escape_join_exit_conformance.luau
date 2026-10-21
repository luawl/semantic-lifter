--!strict
-- Escape-to-join regression: a native inner loop exits to a different block, and the
-- enclosing loop header's parameters are read at that join. The inner exhaustion copy must not
-- overwrite the values visible on the escape path. The three workers exercise numeric, generic,
-- and semantic-normalized inner iteration.
local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("iteration-escape-join-exit")
local proof = builder:addEvidence("dynamic_fixture", "fixture:iteration-escape-join-exit")
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

type Variant = "numeric" | "generic" | "semantic"

local function addWorker(variant: Variant): number
	local worker = builder:reserveFunction({ name_hint = `{variant}_join_worker`, evidence = evidence })
	local firstInput
	local secondInput
	local thirdInput
	if variant == "generic" then
		firstInput = builder:addParameter(worker, dynamic, "iterator")
		secondInput = builder:addParameter(worker, dynamic, "state")
		thirdInput = builder:addParameter(worker, dynamic, "control")
	else
		firstInput = builder:addParameter(worker, number, "n")
	end
	local rounds = builder:addParameter(worker, number, "rounds")
	local gate = builder:addParameter(worker, number, "gate")
	local pick = builder:addParameter(worker, functionValue, "pick")
	local stateType = if variant == "numeric" then number else dynamic

	local entry = builder:reserveBlock(worker, { name_hint = "entry", evidence = evidence })
	local outerHeader = builder:reserveBlock(worker, { name_hint = "outer_header", evidence = evidence })
	local outerBody = builder:reserveBlock(worker, { name_hint = "outer_body", evidence = evidence })
	local innerHeader = builder:reserveBlock(worker, { name_hint = "inner_header", evidence = evidence })
	local innerBody = builder:reserveBlock(worker, { name_hint = "inner_body", evidence = evidence })
	local join = builder:reserveBlock(worker, { name_hint = "join", evidence = evidence })
	local done = builder:reserveBlock(worker, { name_hint = "done", evidence = evidence })
	builder:setFunctionEntry(worker, entry)

	local acc = builder:addBlockParameter(outerHeader, number, "acc")
	local round = builder:addBlockParameter(outerHeader, number, "round")
	local innerControl = builder:addBlockParameter(innerHeader, stateType, "inner_control")
	local innerLimit = builder:addBlockParameter(innerHeader, stateType, "inner_limit")
	local innerStep = builder:addBlockParameter(innerHeader, stateType, "inner_step")
	local innerFlag = builder:addBlockParameter(innerHeader, boolean, "inner_initial")
	local index = builder:addBlockParameter(innerBody, stateType, "index")
	local doneAcc = builder:addBlockParameter(done, number, "done_acc")
	local doneRound = builder:addBlockParameter(done, number, "done_round")

	local _, exported = builder:addInstruction(
		chunkBlock,
		LifterIR.Operation.functionRef(worker),
		{ { type = functionValue, name_hint = "join_worker" } },
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
	local _, firstEntry = builder:addInstruction(
		entry,
		LifterIR.Operation.constant(LifterIR.Literal.boolean(variant ~= "semantic")),
		{ { type = boolean, name_hint = "first_entry" } },
		{ effects = pure, evidence = evidence }
	)
	local _, laterEntry = builder:addInstruction(
		entry,
		LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
		{ { type = boolean, name_hint = "later_entry" } },
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
		LifterIR.Operation.binary("add", acc, hundred[1], "primitive"),
		{ { type = number, name_hint = "bumped" } },
		{ effects = pure, evidence = evidence }
	)
	local _, gated = builder:addInstruction(
		outerBody,
		LifterIR.Operation.binary("less", round, gate, "primitive"),
		{ { type = boolean, name_hint = "gated" } },
		{ effects = pure, evidence = evidence }
	)

	local transition
	if variant == "generic" then
		local _, results = builder:addInstruction(
			innerHeader,
			LifterIR.Operation.genericForNext(innerControl, innerLimit, innerStep, innerFlag, 1),
			{
				{ type = boolean, name_hint = "has_value" },
				{ type = dynamic, name_hint = "prepared_iterator" },
				{ type = dynamic, name_hint = "prepared_state" },
				{ type = dynamic, name_hint = "next_index" },
			},
			{ effects = LifterIR.Effects.genericForNext(), evidence = evidence }
		)
		transition = results
	elseif variant == "numeric" then
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
	local _, joined = builder:addInstruction(
		join,
		LifterIR.Operation.binary("add", acc, one[1], "primitive"),
		{ { type = number, name_hint = "joined" } },
		{ effects = pure, evidence = evidence }
	)

	local initialArguments
	if variant == "generic" then
		initialArguments = { firstInput, secondInput, thirdInput, firstEntry[1] }
	elseif variant == "numeric" then
		initialArguments = { one[1], firstInput, one[1], firstEntry[1] }
	else
		initialArguments = { zero[1], firstInput, one[1], firstEntry[1] }
	end
	local backEdge = if variant == "generic"
		then { transition[2], transition[3], transition[4], laterEntry[1] }
		else { transition[4], transition[2], transition[3], laterEntry[1] }

	builder:finalizeBlock(entry, LifterIR.Terminator.jump(LifterIR.Edge(outerHeader, { zero[1], zero[1] })))
	builder:finalizeBlock(
		outerHeader,
		LifterIR.Terminator.branch(more[1], LifterIR.Edge(outerBody, {}), LifterIR.Edge(done, { acc, round }))
	)
	builder:finalizeBlock(
		outerBody,
		LifterIR.Terminator.branch(gated[1], LifterIR.Edge(innerHeader, initialArguments), LifterIR.Edge(join, {}))
	)
	builder:finalizeBlock(
		innerHeader,
		LifterIR.Terminator.branch(transition[1], LifterIR.Edge(innerBody, { transition[4] }), LifterIR.Edge(outerHeader, { bumped[1], nextRound[1] }))
	)
	builder:finalizeBlock(
		innerBody,
		LifterIR.Terminator.branch(hit[1], LifterIR.Edge(join, {}), LifterIR.Edge(innerHeader, backEdge))
	)
	builder:finalizeBlock(join, LifterIR.Terminator.jump(LifterIR.Edge(outerHeader, { joined[1], nextRound[1] })))
	builder:finalizeBlock(done, LifterIR.Terminator.returnValues({ doneAcc, doneRound }))
	builder:finalizeFunction(worker)
	return worker
end

local numericWorker = addWorker("numeric")
local genericWorker = addWorker("generic")
local semanticWorker = addWorker("semantic")
local exports = {}
for _, worker in { numericWorker, genericWorker, semanticWorker } do
	local _, exported = builder:addInstruction(
		chunkBlock,
		LifterIR.Operation.functionRef(worker),
		{ { type = functionValue, name_hint = "exported_worker" } },
		{ effects = pure, evidence = evidence }
	)
	table.insert(exports, exported[1])
end
builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues(exports))
builder:finalizeFunction(chunk)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
