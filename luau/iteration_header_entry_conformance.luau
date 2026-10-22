-- Native loop header entered from an inner loop exit, a loop control exit, a loop-boundary escape arm, or a
-- loop exit and a loop-boundary exit arm before the loop. A native numeric, generic or semantic-normalized
-- loop computes its own header state, so none of these edges may assign the header's parameters.
-- Each worker is worker(first, second, third, marker, m, f, g, observe); the loop runs index over the
-- first three arguments, and its exhaustion edge passes marker to the exit block, which returns it.
-- The chunk returns twelve workers: for each shape in the order arm_inner_loop_exits_to_header,
-- inner_latch_exit, nested_while_continue and pre_while_boundary_entry, the numeric, generic and
-- semantic-normalized variant.
local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("iteration-header-entry")
local proof = builder:addEvidence("dynamic_fixture", "fixture:iteration-header-entry")
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

local function constant(block, literal, ty, hint)
	local _, results = builder:addInstruction(block, LifterIR.Operation.constant(literal), { { type = ty, name_hint = hint } }, { effects = pure, evidence = evidence })
	return results[1]
end

local function call(block, fn, args, hint)
	local _, results = builder:addInstruction(block, LifterIR.Operation.call(fn, args, LifterIR.ResultArity.fixed(1)), { { type = dynamic, name_hint = hint } }, { effects = LifterIR.Effects.dynamicCall(), evidence = evidence })
	return results[1]
end

local function binary(block, op, a, b, ty, hint)
	local _, results = builder:addInstruction(block, LifterIR.Operation.binary(op, a, b, "primitive"), { { type = ty, name_hint = hint } }, { effects = pure, evidence = evidence })
	return results[1]
end

local function transition(kind, header, h1, h2, h3, hInit)
	if kind == "generic" then
		local _, t = builder:addInstruction(header, LifterIR.Operation.genericForNext(h1, h2, h3, hInit, 1), {
			{ type = boolean, name_hint = "has_value" },
			{ type = dynamic, name_hint = "prepared_iterator" },
			{ type = dynamic, name_hint = "prepared_state" },
			{ type = dynamic, name_hint = "next_index" },
		}, { effects = LifterIR.Effects.genericForNext(), evidence = evidence })
		return t, { t[2], t[3], t[4] }
	elseif kind == "semantic" then
		local _, t = builder:addInstruction(header, LifterIR.Operation.numericForNext(h1, h2, h3, hInit, LifterIR.NumericForMode.semanticNormalized), {
			{ type = boolean, name_hint = "has_value" },
			{ type = dynamic, name_hint = "normalized_limit" },
			{ type = dynamic, name_hint = "normalized_step" },
			{ type = dynamic, name_hint = "next_control" },
		}, { effects = LifterIR.Effects.dynamicCall(), evidence = evidence })
		return t, { t[4], t[2], t[3] }
	end
	local _, t = builder:addInstruction(header, LifterIR.Operation.numericForNext(h1, h2, h3, hInit), {
		{ type = boolean, name_hint = "has_value" },
		{ type = number, name_hint = "next_limit" },
		{ type = number, name_hint = "next_step" },
		{ type = number, name_hint = "next_control" },
	}, { effects = LifterIR.Effects.numericForNext(), evidence = evidence })
	return t, { t[4], t[2], t[3] }
end

local function addWorker(shape, kind)
	local stateType = if kind == "numeric" then number else dynamic
	local worker = builder:reserveFunction({ name_hint = shape .. "_" .. kind, evidence = evidence })
	local p1 = builder:addParameter(worker, stateType, "first")
	local p2 = builder:addParameter(worker, stateType, "second")
	local p3 = builder:addParameter(worker, stateType, "third")
	local marker = builder:addParameter(worker, dynamic, "marker")
	local m = builder:addParameter(worker, number, "m")
	local f = builder:addParameter(worker, functionValue, "f")
	builder:addParameter(worker, functionValue, "g")
	local observe = builder:addParameter(worker, functionValue, "observe")

	local function block(hint)
		return builder:reserveBlock(worker, { name_hint = hint, evidence = evidence })
	end

	local entry = block("entry")
	local header = block("header")
	local body = block("body")
	local exit = block("exit")
	builder:setFunctionEntry(worker, entry)
	local h1 = builder:addBlockParameter(header, stateType, "h1")
	local h2 = builder:addBlockParameter(header, stateType, "h2")
	local h3 = builder:addBlockParameter(header, stateType, "h3")
	local hInit = builder:addBlockParameter(header, boolean, "h_initial")
	local index = builder:addBlockParameter(body, stateType, "index")
	local found = builder:addBlockParameter(exit, dynamic, "found")
	local one = constant(entry, LifterIR.Literal.number(1), number, "one")
	local entryFlag = constant(entry, LifterIR.Literal.boolean(kind ~= "semantic"), boolean, "entry_flag")
	local laterFlag = constant(entry, LifterIR.Literal.boolean(false), boolean, "later_flag")
	local t, back3 = transition(kind, header, h1, h2, h3, hInit)
	local function back()
		return LifterIR.Edge(header, { back3[1], back3[2], back3[3], laterFlag })
	end
	local function enterHeader()
		return LifterIR.Edge(header, { p1, p2, p3, entryFlag })
	end
	builder:finalizeBlock(header, LifterIR.Terminator.branch(t[1], LifterIR.Edge(body, { t[4] }), LifterIR.Edge(exit, { marker })))
	builder:finalizeBlock(exit, LifterIR.Terminator.returnValues({ found }))
	local entryFinalized = false

	if shape == "arm_inner_loop_exits_to_header" then
		-- for index do if f(index) then local j = 1 while not (m < j) do observe(j) j += 1 end
		-- <the inner loop's exit enters the header> else observe(index) end end
		local innerHeader = block("inner_header")
		local innerBody = block("inner_body")
		local join = block("join")
		local j = builder:addBlockParameter(innerHeader, number, "j")
		local c = call(body, f, { index }, "c")
		local innerDone = binary(innerHeader, "less", m, j, boolean, "inner_done")
		call(innerBody, observe, { j }, "inner_observed")
		local nextJ = binary(innerBody, "add", j, one, number, "next_j")
		call(join, observe, { index }, "observed")
		builder:finalizeBlock(body, LifterIR.Terminator.branch(c, LifterIR.Edge(innerHeader, { one }), LifterIR.Edge(join, {})))
		builder:finalizeBlock(innerHeader, LifterIR.Terminator.branch(innerDone, back(), LifterIR.Edge(innerBody, {})))
		builder:finalizeBlock(innerBody, LifterIR.Terminator.jump(LifterIR.Edge(innerHeader, { nextJ })))
		builder:finalizeBlock(join, LifterIR.Terminator.jump(back()))
	elseif shape == "inner_latch_exit" then
		-- for index do local j = 1 repeat observe(j) local nj = j + 1 <if m < nj: the loop control's exit
		-- enters the header> j = nj until false end
		local latchHeader = block("latch_header")
		local latchTail = block("latch_tail")
		local j = builder:addBlockParameter(latchHeader, number, "j")
		call(latchHeader, observe, { j }, "inner_observed")
		local nextJ = binary(latchTail, "add", j, one, number, "next_j")
		local done = binary(latchTail, "less", m, nextJ, boolean, "inner_done")
		builder:finalizeBlock(body, LifterIR.Terminator.jump(LifterIR.Edge(latchHeader, { one })))
		builder:finalizeBlock(latchHeader, LifterIR.Terminator.jump(LifterIR.Edge(latchTail, {})))
		builder:finalizeBlock(latchTail, LifterIR.Terminator.branch(done, back(), LifterIR.Edge(latchHeader, { nextJ })))
	elseif shape == "nested_while_continue" then
		-- for index do local j = 1 while not (m < j) do if f(index, j) then <leave the inner loop for the
		-- header> end j += 1 end observe(index) end
		local innerHeader = block("inner_header")
		local innerBody = block("inner_body")
		local rest = block("rest")
		local j = builder:addBlockParameter(innerHeader, number, "j")
		local innerDone = binary(innerHeader, "less", m, j, boolean, "inner_done")
		local skipped = call(innerBody, f, { index, j }, "skipped")
		local nextJ = binary(innerBody, "add", j, one, number, "next_j")
		call(rest, observe, { index }, "observed")
		builder:finalizeBlock(body, LifterIR.Terminator.jump(LifterIR.Edge(innerHeader, { one })))
		builder:finalizeBlock(innerHeader, LifterIR.Terminator.branch(innerDone, LifterIR.Edge(rest, {}), LifterIR.Edge(innerBody, {})))
		builder:finalizeBlock(innerBody, LifterIR.Terminator.branch(skipped, back(), LifterIR.Edge(innerHeader, { nextJ })))
		builder:finalizeBlock(rest, LifterIR.Terminator.jump(back()))
	elseif shape == "pre_while_boundary_entry" then
		-- local j = 1 while not (m < j) do if f(j) then <leave the loop for the header> end observe(j) j += 1 end
		-- for index do observe(index) end (both exits of the first loop enter the header with the same arguments)
		local preHeader = block("pre_header")
		local preBody = block("pre_body")
		local preWork = block("pre_work")
		local pj = builder:addBlockParameter(preHeader, number, "pj")
		local preDone = binary(preHeader, "less", m, pj, boolean, "pre_done")
		local preStop = call(preBody, f, { pj }, "pre_stop")
		call(preWork, observe, { pj }, "pre_observed")
		local nextPj = binary(preWork, "add", pj, one, number, "next_pj")
		call(body, observe, { index }, "observed")
		builder:finalizeBlock(entry, LifterIR.Terminator.jump(LifterIR.Edge(preHeader, { one })))
		entryFinalized = true
		builder:finalizeBlock(preHeader, LifterIR.Terminator.branch(preDone, enterHeader(), LifterIR.Edge(preBody, {})))
		builder:finalizeBlock(preBody, LifterIR.Terminator.branch(preStop, enterHeader(), LifterIR.Edge(preWork, {})))
		builder:finalizeBlock(preWork, LifterIR.Terminator.jump(LifterIR.Edge(preHeader, { nextPj })))
		builder:finalizeBlock(body, LifterIR.Terminator.jump(back()))
	else
		error("unknown shape " .. tostring(shape))
	end

	if not entryFinalized then
		builder:finalizeBlock(entry, LifterIR.Terminator.jump(enterHeader()))
	end
	builder:finalizeFunction(worker)
	return worker
end

local exports = {}
for _, shape in { "arm_inner_loop_exits_to_header", "inner_latch_exit", "nested_while_continue", "pre_while_boundary_entry" } do
	for _, kind in { "numeric", "generic", "semantic" } do
		local worker = addWorker(shape, kind)
		local _, exported = builder:addInstruction(chunkBlock, LifterIR.Operation.functionRef(worker), { { type = functionValue, name_hint = "exported_worker" } }, { effects = pure, evidence = evidence })
		table.insert(exports, exported[1])
	end
end
builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues(exports))
builder:finalizeFunction(chunk)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
