-- Explicit continues inside a native loop that guards its exit copy with a completion local: a continue written
-- after an escape out of a wrapped body region, a continue projected through a shared forwarding latch, and the
-- continue a loop-boundary body writes when its region stops at the loop header. Each worker is
-- worker(first, second, third, marker, m, f, g, observe); the loop runs index over the first three arguments,
-- and its exhaustion edge passes marker to the exit block, which returns it. The chunk returns eight workers:
-- for each shape in the order diamond_continue, latch_diamond, nested_arm_boundary and
-- nested_arm_boundary_work, the numeric and the generic variant.
local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("iteration-continue-completion")
local proof = builder:addEvidence("dynamic_fixture", "fixture:iteration-continue-completion")
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

local function transition(kind, header, h1, h2, h3, hInit)
	if kind == "generic" then
		local _, t = builder:addInstruction(header, LifterIR.Operation.genericForNext(h1, h2, h3, hInit, 1), {
			{ type = boolean, name_hint = "has_value" },
			{ type = dynamic, name_hint = "prepared_iterator" },
			{ type = dynamic, name_hint = "prepared_state" },
			{ type = dynamic, name_hint = "next_index" },
		}, { effects = LifterIR.Effects.genericForNext(), evidence = evidence })
		return t, { t[2], t[3], t[4] }
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
	builder:addParameter(worker, number, "m")
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
	local entryFlag = constant(entry, LifterIR.Literal.boolean(true), boolean, "entry_flag")
	local laterFlag = constant(entry, LifterIR.Literal.boolean(false), boolean, "later_flag")
	local t, back3 = transition(kind, header, h1, h2, h3, hInit)
	local function back()
		return LifterIR.Edge(header, { back3[1], back3[2], back3[3], laterFlag })
	end
	builder:finalizeBlock(header, LifterIR.Terminator.branch(t[1], LifterIR.Edge(body, { t[4] }), LifterIR.Edge(exit, { marker })))
	builder:finalizeBlock(exit, LifterIR.Terminator.returnValues({ found }))

	if shape == "diamond_continue" then
		-- for index do if f(index) then if g(index) then continue end end observe(index) end
		local inner = block("inner")
		local join = block("join")
		local c = call(body, f, { index }, "c")
		local d = call(inner, g, { index }, "d")
		call(join, observe, { index }, "observed")
		builder:finalizeBlock(body, LifterIR.Terminator.branch(c, LifterIR.Edge(inner, {}), LifterIR.Edge(join, {})))
		builder:finalizeBlock(inner, LifterIR.Terminator.branch(d, back(), LifterIR.Edge(join, {})))
		builder:finalizeBlock(join, LifterIR.Terminator.jump(back()))
	elseif shape == "latch_diamond" then
		-- the same diamond, with both back edges through one shared pure forwarding latch l(l1, l2, l3, l4) -> header
		local inner = block("inner")
		local join = block("join")
		local latch = block("latch")
		local l1 = builder:addBlockParameter(latch, stateType, "l1")
		local l2 = builder:addBlockParameter(latch, stateType, "l2")
		local l3 = builder:addBlockParameter(latch, stateType, "l3")
		local l4 = builder:addBlockParameter(latch, boolean, "l4")
		local c = call(body, f, { index }, "c")
		local d = call(inner, g, { index }, "d")
		call(join, observe, { index }, "observed")
		local function toLatch()
			return LifterIR.Edge(latch, { back3[1], back3[2], back3[3], laterFlag })
		end
		builder:finalizeBlock(body, LifterIR.Terminator.branch(c, LifterIR.Edge(inner, {}), LifterIR.Edge(join, {})))
		builder:finalizeBlock(inner, LifterIR.Terminator.branch(d, toLatch(), LifterIR.Edge(join, {})))
		builder:finalizeBlock(join, LifterIR.Terminator.jump(toLatch()))
		builder:finalizeBlock(latch, LifterIR.Terminator.jump(LifterIR.Edge(header, { l1, l2, l3, l4 })))
	elseif shape == "nested_arm_boundary" then
		-- for index do if f(index) then if not g(index) then if observe(index) then continue else found = index
		-- break end end end observe(index) end
		local outer = block("outer")
		local boundary = block("boundary")
		local join = block("join")
		local c = call(body, f, { index }, "c")
		local d = call(outer, g, { index }, "d")
		local e = call(boundary, observe, { index }, "e")
		call(join, observe, { index }, "observed")
		builder:finalizeBlock(body, LifterIR.Terminator.branch(c, LifterIR.Edge(outer, {}), LifterIR.Edge(join, {})))
		builder:finalizeBlock(outer, LifterIR.Terminator.branch(d, LifterIR.Edge(join, {}), LifterIR.Edge(boundary, {})))
		builder:finalizeBlock(boundary, LifterIR.Terminator.branch(e, back(), LifterIR.Edge(exit, { index })))
		builder:finalizeBlock(join, LifterIR.Terminator.jump(back()))
	elseif shape == "nested_arm_boundary_work" then
		-- nested_arm_boundary with observe(1) on the continuing arm before it enters the header
		local outer = block("outer")
		local boundary = block("boundary")
		local work = block("work")
		local join = block("join")
		local c = call(body, f, { index }, "c")
		local d = call(outer, g, { index }, "d")
		local e = call(boundary, observe, { index }, "e")
		call(work, observe, { one }, "worked")
		call(join, observe, { index }, "observed")
		builder:finalizeBlock(body, LifterIR.Terminator.branch(c, LifterIR.Edge(outer, {}), LifterIR.Edge(join, {})))
		builder:finalizeBlock(outer, LifterIR.Terminator.branch(d, LifterIR.Edge(join, {}), LifterIR.Edge(boundary, {})))
		builder:finalizeBlock(boundary, LifterIR.Terminator.branch(e, LifterIR.Edge(work, {}), LifterIR.Edge(exit, { index })))
		builder:finalizeBlock(work, LifterIR.Terminator.jump(back()))
		builder:finalizeBlock(join, LifterIR.Terminator.jump(back()))
	else
		error("unknown shape " .. tostring(shape))
	end

	builder:finalizeBlock(entry, LifterIR.Terminator.jump(LifterIR.Edge(header, { p1, p2, p3, entryFlag })))
	builder:finalizeFunction(worker)
	return worker
end

local exports = {}
for _, shape in { "diamond_continue", "latch_diamond", "nested_arm_boundary", "nested_arm_boundary_work" } do
	for _, kind in { "numeric", "generic" } do
		local worker = addWorker(shape, kind)
		local _, exported = builder:addInstruction(chunkBlock, LifterIR.Operation.functionRef(worker), { { type = functionValue, name_hint = "exported_worker" } }, { effects = pure, evidence = evidence })
		table.insert(exports, exported[1])
	end
end
builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues(exports))
builder:finalizeFunction(chunk)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
