-- A native loop whose body re-enters its header through a pure forwarding block,
-- forwarder(forwarded_control, forwarded_limit, forwarded_step, forwarded_initial) -> header: the native loop computes
-- its own header state, so the forwarder's parameters are dead and no edge into it may assign them. Each worker is
-- worker(first, second, third, marker, m, f, g, observe) and runs a native numeric, generic or semantic-normalized
-- loop over its first three parameters; the exhaustion edge passes marker to the exit block, which returns it. Each
-- shape puts another writer in front of the forwarder:
--   latch_diamond: for index do if f(index) and g(index) then <next index> end observe(index) end
--   loop_exit_forwarder: for index do if f(index) then local j = 1 while not (m < j) do observe(j) j += 1 end
--     else observe(index) end end
--   native_exit_forwarder: the same with the inner loop a native numeric for over 1, m, 1
--   entry_forwarder: local j = 1 while not (m < j) do if f(j) then break end observe(j) j += 1 end
--     for index do observe(index) if not f(index) then observe(index) end end, where both exits of the while enter an
--     entry forwarder(initial_control, initial_limit, initial_step) -> header whose parameters the for line reads, so
--     its copies stay
--   boundary_exit_forwarder: for index do local j = 1 while not (m < j) do if f(index, j) then break end observe(j)
--     j += 1 end end
--   escape_arm_forwarder: for index do if f(index) then local j = 1 while not (m < j) do if g(j) then <next index> end
--     observe(j) j += 1 end observe(index) else observe(index) end end
--   latch_exit_forwarder: for index do local j = 1 repeat observe(j) local nj = j + 1 if m < nj then break end
--     j = nj until false end
--   chain_forwarder: latch_diamond with the inner arm entering a first forwarder that jumps to the second
--   branch_expression_join: for index do observe(index) local x = if f(index) then 1 else m end, where x is a
--     one-parameter join that enters the header with the transition state itself, so it is no forwarder and keeps
--     its declaration
-- The chunk returns 27 workers: for each shape in this order, the numeric, generic and semantic-normalized variant.
local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local SHAPES = {
	"latch_diamond",
	"loop_exit_forwarder",
	"native_exit_forwarder",
	"entry_forwarder",
	"boundary_exit_forwarder",
	"escape_arm_forwarder",
	"latch_exit_forwarder",
	"chain_forwarder",
	"branch_expression_join",
}
local KINDS = { "numeric", "generic", "semantic" }

local builder = LifterIR.Builder.new("iteration-header-forwarder")
local proof = builder:addEvidence("dynamic_fixture", "fixture:iteration-header-forwarder")
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

local function buildWorker(shape, kind)
	local function transition(header, h1, h2, h3, hInit)
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

	local stateType = if kind == "numeric" then number else dynamic
	local worker = builder:reserveFunction({ name_hint = shape .. "_" .. kind, evidence = evidence })
	local p1 = builder:addParameter(worker, stateType, "first")
	local p2 = builder:addParameter(worker, stateType, "second")
	local p3 = builder:addParameter(worker, stateType, "third")
	local marker = builder:addParameter(worker, dynamic, "marker")
	local m = builder:addParameter(worker, number, "m")
	local f = builder:addParameter(worker, functionValue, "f")
	local g = builder:addParameter(worker, functionValue, "g")
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
	local t, back3 = transition(header, h1, h2, h3, hInit)
	builder:finalizeBlock(header, LifterIR.Terminator.branch(t[1], LifterIR.Edge(body, { t[4] }), LifterIR.Edge(exit, { marker })))
	builder:finalizeBlock(exit, LifterIR.Terminator.returnValues({ found }))

	local latch = nil
	if shape ~= "branch_expression_join" then
		latch = block("forwarder")
		local l1 = builder:addBlockParameter(latch, stateType, "forwarded_control")
		local l2 = builder:addBlockParameter(latch, stateType, "forwarded_limit")
		local l3 = builder:addBlockParameter(latch, stateType, "forwarded_step")
		local l4 = builder:addBlockParameter(latch, boolean, "forwarded_initial")
		builder:finalizeBlock(latch, LifterIR.Terminator.jump(LifterIR.Edge(header, { l1, l2, l3, l4 })))
	end
	local function toLatch()
		return LifterIR.Edge(latch, { back3[1], back3[2], back3[3], laterFlag })
	end
	local entryFinalized = false

	if shape == "latch_diamond" then
		-- for index do if f(index) and g(index) then <continue through the forwarder> end observe(index) end
		local inner = block("inner")
		local join = block("join")
		local c = call(body, f, { index }, "c")
		local d = call(inner, g, { index }, "d")
		call(join, observe, { index }, "observed")
		builder:finalizeBlock(body, LifterIR.Terminator.branch(c, LifterIR.Edge(inner, {}), LifterIR.Edge(join, {})))
		builder:finalizeBlock(inner, LifterIR.Terminator.branch(d, toLatch(), LifterIR.Edge(join, {})))
		builder:finalizeBlock(join, LifterIR.Terminator.jump(toLatch()))
	elseif shape == "loop_exit_forwarder" then
		-- for index do if f(index) then local j = 1 while not (m < j) do observe(j) j += 1 end else observe(index) end end
		local innerHeader = block("inner_header")
		local innerBody = block("inner_body")
		local other = block("other")
		local j = builder:addBlockParameter(innerHeader, number, "j")
		local c = call(body, f, { index }, "c")
		local innerDone = binary(innerHeader, "less", m, j, boolean, "inner_done")
		call(innerBody, observe, { j }, "inner_observed")
		local nextJ = binary(innerBody, "add", j, one, number, "next_j")
		call(other, observe, { index }, "observed")
		builder:finalizeBlock(body, LifterIR.Terminator.branch(c, LifterIR.Edge(innerHeader, { one }), LifterIR.Edge(other, {})))
		builder:finalizeBlock(innerHeader, LifterIR.Terminator.branch(innerDone, toLatch(), LifterIR.Edge(innerBody, {})))
		builder:finalizeBlock(innerBody, LifterIR.Terminator.jump(LifterIR.Edge(innerHeader, { nextJ })))
		builder:finalizeBlock(other, LifterIR.Terminator.jump(toLatch()))
	elseif shape == "native_exit_forwarder" then
		-- the same program with the inner loop a native numeric for (1, m, 1) whose exit enters the forwarder
		local innerHeader = block("inner_header")
		local innerBody = block("inner_body")
		local other = block("other")
		local i1 = builder:addBlockParameter(innerHeader, number, "i1")
		local i2 = builder:addBlockParameter(innerHeader, number, "i2")
		local i3 = builder:addBlockParameter(innerHeader, number, "i3")
		local i4 = builder:addBlockParameter(innerHeader, boolean, "i4")
		local jv = builder:addBlockParameter(innerBody, number, "jv")
		local innerFlag = constant(entry, LifterIR.Literal.boolean(true), boolean, "inner_flag")
		local _, it = builder:addInstruction(innerHeader, LifterIR.Operation.numericForNext(i1, i2, i3, i4), {
			{ type = boolean, name_hint = "inner_has_value" },
			{ type = number, name_hint = "inner_limit" },
			{ type = number, name_hint = "inner_step" },
			{ type = number, name_hint = "inner_next" },
		}, { effects = LifterIR.Effects.numericForNext(), evidence = evidence })
		local c = call(body, f, { index }, "c")
		call(innerBody, observe, { jv }, "inner_observed")
		call(other, observe, { index }, "observed")
		builder:finalizeBlock(body, LifterIR.Terminator.branch(c, LifterIR.Edge(innerHeader, { one, m, one, innerFlag }), LifterIR.Edge(other, {})))
		builder:finalizeBlock(innerHeader, LifterIR.Terminator.branch(it[1], LifterIR.Edge(innerBody, { it[4] }), toLatch()))
		builder:finalizeBlock(innerBody, LifterIR.Terminator.jump(LifterIR.Edge(innerHeader, { it[4], it[2], it[3], laterFlag })))
		builder:finalizeBlock(other, LifterIR.Terminator.jump(toLatch()))
	elseif shape == "entry_forwarder" then
		-- local j = 1 while not (m < j) do if f(j) then break end observe(j) j += 1 end
		-- for index do observe(index) if not f(index) then observe(index) end end
		-- (both exits of the while enter the entry forwarder, whose parameters the for line reads)
		local preHeader = block("pre_header")
		local preBody = block("pre_body")
		local preWork = block("pre_work")
		local entryForwarder = block("entry_forwarder")
		local e1 = builder:addBlockParameter(entryForwarder, stateType, "initial_control")
		local e2 = builder:addBlockParameter(entryForwarder, stateType, "initial_limit")
		local e3 = builder:addBlockParameter(entryForwarder, stateType, "initial_step")
		local pj = builder:addBlockParameter(preHeader, number, "pj")
		local preDone = binary(preHeader, "less", m, pj, boolean, "pre_done")
		local preStop = call(preBody, f, { pj }, "pre_stop")
		call(preWork, observe, { pj }, "pre_observed")
		local nextPj = binary(preWork, "add", pj, one, number, "next_pj")
		call(body, observe, { index }, "observed")
		builder:finalizeBlock(entry, LifterIR.Terminator.jump(LifterIR.Edge(preHeader, { one })))
		entryFinalized = true
		builder:finalizeBlock(preHeader, LifterIR.Terminator.branch(preDone, LifterIR.Edge(entryForwarder, { p1, p2, p3 }), LifterIR.Edge(preBody, {})))
		builder:finalizeBlock(preBody, LifterIR.Terminator.branch(preStop, LifterIR.Edge(entryForwarder, { p1, p2, p3 }), LifterIR.Edge(preWork, {})))
		builder:finalizeBlock(preWork, LifterIR.Terminator.jump(LifterIR.Edge(preHeader, { nextPj })))
		builder:finalizeBlock(entryForwarder, LifterIR.Terminator.jump(LifterIR.Edge(header, { e1, e2, e3, entryFlag })))
		local c = call(body, f, { index }, "c")
		local other = block("other")
		call(other, observe, { index }, "again")
		builder:finalizeBlock(body, LifterIR.Terminator.branch(c, toLatch(), LifterIR.Edge(other, {})))
		builder:finalizeBlock(other, LifterIR.Terminator.jump(toLatch()))
	elseif shape == "boundary_exit_forwarder" then
		-- for index do local j = 1 while not (m < j) do if f(index, j) then break end observe(j) j += 1 end end
		-- (the while's exit and its body's early exit both enter the forwarder)
		local innerHeader = block("inner_header")
		local innerBody = block("inner_body")
		local work = block("work")
		local j = builder:addBlockParameter(innerHeader, number, "j")
		local innerDone = binary(innerHeader, "less", m, j, boolean, "inner_done")
		local skipped = call(innerBody, f, { index, j }, "skipped")
		call(work, observe, { j }, "inner_observed")
		local nextJ = binary(work, "add", j, one, number, "next_j")
		builder:finalizeBlock(body, LifterIR.Terminator.jump(LifterIR.Edge(innerHeader, { one })))
		builder:finalizeBlock(innerHeader, LifterIR.Terminator.branch(innerDone, toLatch(), LifterIR.Edge(innerBody, {})))
		builder:finalizeBlock(innerBody, LifterIR.Terminator.branch(skipped, toLatch(), LifterIR.Edge(work, {})))
		builder:finalizeBlock(work, LifterIR.Terminator.jump(LifterIR.Edge(innerHeader, { nextJ })))
	elseif shape == "escape_arm_forwarder" then
		-- for index do if f(index) then local j = 1 while not (m < j) do if g(j) then <continue> end observe(j)
		-- j += 1 end observe(index) else observe(index) end end
		local innerHeader = block("inner_header")
		local innerBody = block("inner_body")
		local work = block("work")
		local after = block("after")
		local other = block("other")
		local j = builder:addBlockParameter(innerHeader, number, "j")
		local c = call(body, f, { index }, "c")
		local innerDone = binary(innerHeader, "less", m, j, boolean, "inner_done")
		local skipped = call(innerBody, g, { j }, "skipped")
		call(work, observe, { j }, "inner_observed")
		local nextJ = binary(work, "add", j, one, number, "next_j")
		call(after, observe, { index }, "after_observed")
		call(other, observe, { index }, "observed")
		builder:finalizeBlock(body, LifterIR.Terminator.branch(c, LifterIR.Edge(innerHeader, { one }), LifterIR.Edge(other, {})))
		builder:finalizeBlock(innerHeader, LifterIR.Terminator.branch(innerDone, LifterIR.Edge(after, {}), LifterIR.Edge(innerBody, {})))
		builder:finalizeBlock(innerBody, LifterIR.Terminator.branch(skipped, toLatch(), LifterIR.Edge(work, {})))
		builder:finalizeBlock(work, LifterIR.Terminator.jump(LifterIR.Edge(innerHeader, { nextJ })))
		builder:finalizeBlock(after, LifterIR.Terminator.jump(toLatch()))
		builder:finalizeBlock(other, LifterIR.Terminator.jump(toLatch()))
	elseif shape == "latch_exit_forwarder" then
		-- for index do local j = 1 repeat observe(j) local nj = j + 1 if m < nj then break end j = nj until false end
		-- (the forwarder has one predecessor, reached by the loop control's branch edge)
		local latchHeader = block("latch_header")
		local latchTail = block("latch_tail")
		local j = builder:addBlockParameter(latchHeader, number, "j")
		call(latchHeader, observe, { j }, "inner_observed")
		local nextJ = binary(latchTail, "add", j, one, number, "next_j")
		local done = binary(latchTail, "less", m, nextJ, boolean, "inner_done")
		builder:finalizeBlock(body, LifterIR.Terminator.jump(LifterIR.Edge(latchHeader, { one })))
		builder:finalizeBlock(latchHeader, LifterIR.Terminator.jump(LifterIR.Edge(latchTail, {})))
		builder:finalizeBlock(latchTail, LifterIR.Terminator.branch(done, toLatch(), LifterIR.Edge(latchHeader, { nextJ })))
	elseif shape == "chain_forwarder" then
		-- latch_diamond with the inner arm entering a first forwarder that jumps to the second
		local inner = block("inner")
		local join = block("join")
		local first = block("first_forwarder")
		local a1 = builder:addBlockParameter(first, stateType, "forwarded_first_control")
		local a2 = builder:addBlockParameter(first, stateType, "forwarded_first_limit")
		local a3 = builder:addBlockParameter(first, stateType, "forwarded_first_step")
		local a4 = builder:addBlockParameter(first, boolean, "forwarded_first_initial")
		local c = call(body, f, { index }, "c")
		local d = call(inner, g, { index }, "d")
		call(join, observe, { index }, "observed")
		builder:finalizeBlock(body, LifterIR.Terminator.branch(c, LifterIR.Edge(inner, {}), LifterIR.Edge(join, {})))
		builder:finalizeBlock(inner, LifterIR.Terminator.branch(d, LifterIR.Edge(first, { back3[1], back3[2], back3[3], laterFlag }), LifterIR.Edge(join, {})))
		builder:finalizeBlock(first, LifterIR.Terminator.jump(LifterIR.Edge(latch, { a1, a2, a3, a4 })))
		builder:finalizeBlock(join, LifterIR.Terminator.jump(toLatch()))
	elseif shape == "branch_expression_join" then
		local join = block("join")
		builder:addBlockParameter(join, dynamic, "x")
		call(body, observe, { index }, "observed")
		local c = call(body, f, { index }, "c")
		builder:finalizeBlock(body, LifterIR.Terminator.branch(c, LifterIR.Edge(join, { one }), LifterIR.Edge(join, { m })))
		builder:finalizeBlock(join, LifterIR.Terminator.jump(LifterIR.Edge(header, { back3[1], back3[2], back3[3], laterFlag })))
	else
		error("unknown shape " .. tostring(shape))
	end

	if not entryFinalized then
		builder:finalizeBlock(entry, LifterIR.Terminator.jump(LifterIR.Edge(header, { p1, p2, p3, entryFlag })))
	end
	builder:finalizeFunction(worker)
	local _, exported = builder:addInstruction(chunkBlock, LifterIR.Operation.functionRef(worker), { { type = functionValue, name_hint = shape .. "_" .. kind } }, { effects = pure, evidence = evidence })
	return exported[1]
end

local exports = {}
for _, shape in SHAPES do
	for _, kind in KINDS do
		table.insert(exports, buildWorker(shape, kind))
	end
end
builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues(exports))
builder:finalizeFunction(chunk)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
