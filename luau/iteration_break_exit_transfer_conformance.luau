--!strict
-- Conformance fixture: a break and the exhaustion of a native loop feed the same exit parameter.
-- One chunk returns three workers. In each, a native-iteration header's exhaustion edge carries a
-- loop-invariant function parameter (the marker) into the exit block's single parameter, and the
-- body's break edge carries the body value (the index) into the same parameter. The exit block
-- returns its parameter, so each worker means "the first index for which pick(index) is truthy,
-- else marker".
--   numeric_break_exit_transfer: luau_numeric numeric_for_next (entered with the flag true)
--   generic_break_exit_transfer: generic_for_next with one loop variable (entered with the flag true)
--   semantic_break_exit_transfer: semantic_normalized numeric_for_next (entered with the flag false,
--     externalInitialValue, src/iteration_protocol.zig:951-956)
local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("iteration-break-exit-transfer")
local proof = builder:addEvidence("dynamic_fixture", "fixture:iteration-break-exit-transfer")
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
	local worker = builder:reserveFunction({ name_hint = `{variant}_break_exit_transfer`, evidence = evidence })
	local stateType = if variant == "numeric" then number else dynamic
	local first = builder:addParameter(worker, stateType, if variant == "generic" then `{variant}_iterator` else `{variant}_initial`)
	local second = builder:addParameter(worker, stateType, if variant == "generic" then `{variant}_state` else `{variant}_limit`)
	local third = builder:addParameter(worker, stateType, if variant == "generic" then `{variant}_control` else `{variant}_step`)
	local marker = builder:addParameter(worker, dynamic, `{variant}_marker`)
	local pick = builder:addParameter(worker, functionValue, `{variant}_pick`)

	local entry = builder:reserveBlock(worker, { name_hint = "entry", evidence = evidence })
	local header = builder:reserveBlock(worker, { name_hint = "header", evidence = evidence })
	local body = builder:reserveBlock(worker, { name_hint = "body", evidence = evidence })
	local exit = builder:reserveBlock(worker, { name_hint = "exit", evidence = evidence })
	builder:setFunctionEntry(worker, entry)

	local h1 = builder:addBlockParameter(header, stateType, `{variant}_header_1`)
	local h2 = builder:addBlockParameter(header, stateType, `{variant}_header_2`)
	local h3 = builder:addBlockParameter(header, stateType, `{variant}_header_3`)
	local hInitial = builder:addBlockParameter(header, boolean, `{variant}_header_initial`)
	local index = builder:addBlockParameter(body, stateType, `{variant}_index`)
	local found = builder:addBlockParameter(exit, dynamic, `{variant}_found`)

	local _, entryFlag = builder:addInstruction(
		entry,
		LifterIR.Operation.constant(LifterIR.Literal.boolean(variant ~= "semantic")),
		{ { type = boolean, name_hint = `{variant}_entry_flag` } },
		{ effects = pure, evidence = evidence }
	)
	local _, laterFlag = builder:addInstruction(
		entry,
		LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
		{ { type = boolean, name_hint = `{variant}_later_flag` } },
		{ effects = pure, evidence = evidence }
	)

	local transition
	if variant == "generic" then
		_, transition = builder:addInstruction(
			header,
			LifterIR.Operation.genericForNext(h1, h2, h3, hInitial, 1),
			{
				{ type = boolean, name_hint = `{variant}_has_value` },
				{ type = dynamic, name_hint = `{variant}_prepared_iterator` },
				{ type = dynamic, name_hint = `{variant}_prepared_state` },
				{ type = dynamic, name_hint = `{variant}_next_index` },
			},
			{ effects = LifterIR.Effects.genericForNext(), evidence = evidence }
		)
	elseif variant == "numeric" then
		_, transition = builder:addInstruction(
			header,
			LifterIR.Operation.numericForNext(h1, h2, h3, hInitial),
			{
				{ type = boolean, name_hint = `{variant}_has_value` },
				{ type = number, name_hint = `{variant}_next_limit` },
				{ type = number, name_hint = `{variant}_next_step` },
				{ type = number, name_hint = `{variant}_next_control` },
			},
			{ effects = LifterIR.Effects.numericForNext(), evidence = evidence }
		)
	else
		_, transition = builder:addInstruction(
			header,
			LifterIR.Operation.numericForNext(h1, h2, h3, hInitial, LifterIR.NumericForMode.semanticNormalized),
			{
				{ type = boolean, name_hint = `{variant}_has_value` },
				{ type = dynamic, name_hint = `{variant}_normalized_limit` },
				{ type = dynamic, name_hint = `{variant}_normalized_step` },
				{ type = dynamic, name_hint = `{variant}_next_control` },
			},
			{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
		)
	end
	local _, picked = builder:addInstruction(
		body,
		LifterIR.Operation.call(pick, { index }, LifterIR.ResultArity.fixed(1)),
		{ { type = dynamic, name_hint = `{variant}_picked` } },
		{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
	)

	builder:finalizeBlock(entry, LifterIR.Terminator.jump(LifterIR.Edge(header, { first, second, third, entryFlag[1] })))
	builder:finalizeBlock(
		header,
		LifterIR.Terminator.branch(transition[1], LifterIR.Edge(body, { transition[4] }), LifterIR.Edge(exit, { marker }))
	)
	local backEdge = if variant == "generic"
		then { transition[2], transition[3], transition[4], laterFlag[1] }
		else { transition[4], transition[2], transition[3], laterFlag[1] }
	builder:finalizeBlock(
		body,
		LifterIR.Terminator.branch(picked[1], LifterIR.Edge(exit, { index }), LifterIR.Edge(header, backEdge))
	)
	builder:finalizeBlock(exit, LifterIR.Terminator.returnValues({ found }))
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
