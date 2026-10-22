-- A loop-boundary body region that is written inside its own transfer wrapper and ends in a branch whose two arms
-- are wrapped too. Each arm's escape propagation writes a continue that leaves the region's wrapper, and the
-- continue the body region ends with carries those arms on to the loop header. Each worker is
-- worker(first, second, third, marker, m, f, g, observe, h), whose loop runs index over the first three
-- arguments:
--   if f(index) then if not g(index) then if observe(index) then
--     observe(1); <inner loop z over h(index, j)>
--     if h(index, 0) then <inner loop a over h(index, 20 + j)> else <inner loop b over h(index, 10 + j)> end
--   else found = index break end end end observe(index)
-- where each inner loop is j = 1 while not (m < j) do observe(j) if h(index, key) then <continue the outer loop>
-- end j += 1 end, loop z leaves to the branch and loops a and b leave to the outer loop's header. The outer loop's
-- exhaustion edge passes marker to the exit block. The chunk returns three workers: the outer loop as a native
-- numeric loop, as a native generic loop, and as a plain counter loop.
local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("iteration-boundary-body-continue")
local proof = builder:addEvidence("dynamic_fixture", "fixture:iteration-boundary-body-continue")
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
	end
	local _, t = builder:addInstruction(header, LifterIR.Operation.numericForNext(h1, h2, h3, hInit), {
		{ type = boolean, name_hint = "has_value" },
		{ type = number, name_hint = "next_limit" },
		{ type = number, name_hint = "next_step" },
		{ type = number, name_hint = "next_control" },
	}, { effects = LifterIR.Effects.numericForNext(), evidence = evidence })
	return t, { t[4], t[2], t[3] }
end

local function addWorker(kind)
	local stateType = if kind == "generic" then dynamic else number
	local worker = builder:reserveFunction({ name_hint = "wrapped_body_arms_" .. kind, evidence = evidence })
	local p1 = builder:addParameter(worker, stateType, "first")
	local p2 = builder:addParameter(worker, stateType, "second")
	local p3 = builder:addParameter(worker, stateType, "third")
	local marker = builder:addParameter(worker, dynamic, "marker")
	local m = builder:addParameter(worker, number, "m")
	local f = builder:addParameter(worker, functionValue, "f")
	local g = builder:addParameter(worker, functionValue, "g")
	local observe = builder:addParameter(worker, functionValue, "observe")
	local h = builder:addParameter(worker, functionValue, "h")

	local function block(hint)
		return builder:reserveBlock(worker, { name_hint = hint, evidence = evidence })
	end

	local entry = block("entry")
	local header = block("header")
	local body = block("body")
	local exit = block("exit")
	builder:setFunctionEntry(worker, entry)
	local index = builder:addBlockParameter(body, stateType, "index")
	local found = builder:addBlockParameter(exit, dynamic, "found")
	local zero = constant(entry, LifterIR.Literal.number(0), number, "zero")
	local one = constant(entry, LifterIR.Literal.number(1), number, "one")
	local ten = constant(entry, LifterIR.Literal.number(10), number, "ten")
	local twenty = constant(entry, LifterIR.Literal.number(20), number, "twenty")
	local trueFlag = constant(entry, LifterIR.Literal.boolean(true), boolean, "true_flag")

	local back
	if kind == "while" then
		local i = builder:addBlockParameter(header, number, "i")
		local done = binary(header, "less", p2, i, boolean, "done")
		builder:finalizeBlock(header, LifterIR.Terminator.branch(done, LifterIR.Edge(exit, { marker }), LifterIR.Edge(body, { i })))
		builder:finalizeBlock(entry, LifterIR.Terminator.jump(LifterIR.Edge(header, { p1 })))
		back = function(source)
			local nextI = binary(source, "add", index, p3, number, "next_i")
			return LifterIR.Edge(header, { nextI })
		end
	else
		local h1 = builder:addBlockParameter(header, stateType, "h1")
		local h2 = builder:addBlockParameter(header, stateType, "h2")
		local h3 = builder:addBlockParameter(header, stateType, "h3")
		local hInit = builder:addBlockParameter(header, boolean, "h_initial")
		local laterFlag = constant(entry, LifterIR.Literal.boolean(false), boolean, "later_flag")
		local t, back3 = transition(kind, header, h1, h2, h3, hInit)
		builder:finalizeBlock(header, LifterIR.Terminator.branch(t[1], LifterIR.Edge(body, { t[4] }), LifterIR.Edge(exit, { marker })))
		builder:finalizeBlock(entry, LifterIR.Terminator.jump(LifterIR.Edge(header, { p1, p2, p3, trueFlag })))
		back = function(_source)
			return LifterIR.Edge(header, { back3[1], back3[2], back3[3], laterFlag })
		end
	end
	builder:finalizeBlock(exit, LifterIR.Terminator.returnValues({ found }))

	local outer = block("outer")
	local boundary = block("boundary")
	local join = block("join")
	local work = block("work")
	local c = call(body, f, { index }, "c")
	local d = call(outer, g, { index }, "d")
	local e = call(boundary, observe, { index }, "e")
	call(join, observe, { index }, "observed")
	builder:finalizeBlock(body, LifterIR.Terminator.branch(c, LifterIR.Edge(outer, {}), LifterIR.Edge(join, {})))
	builder:finalizeBlock(outer, LifterIR.Terminator.branch(d, LifterIR.Edge(join, {}), LifterIR.Edge(boundary, {})))
	builder:finalizeBlock(boundary, LifterIR.Terminator.branch(e, LifterIR.Edge(work, {}), LifterIR.Edge(exit, { index })))
	builder:finalizeBlock(join, LifterIR.Terminator.jump(back(join)))
	call(work, observe, { one }, "worked")

	-- The inner loop: header wh(j) leaves when m < j, else enters wb; wb observes j and continues the outer loop
	-- when h(index, offset + j) is truthy, else falls to ws, which steps j and jumps back to wh.
	local function whileLoop(tag, offset, leave)
		local wh = block(tag .. "_while_header")
		local wb = block(tag .. "_while_body")
		local ws = block(tag .. "_while_step")
		local j = builder:addBlockParameter(wh, number, tag .. "_j")
		local doneJ = binary(wh, "less", m, j, boolean, tag .. "_done")
		call(wb, observe, { j }, tag .. "_gated")
		local key = if offset == nil then j else binary(wb, "add", offset, j, number, tag .. "_key")
		local s = call(wb, h, { index, key }, tag .. "_skipped")
		local nextJ = binary(ws, "add", j, one, number, tag .. "_next_j")
		local leaveEdge = if leave == nil then back(wh) else LifterIR.Edge(leave, {})
		builder:finalizeBlock(wh, LifterIR.Terminator.branch(doneJ, leaveEdge, LifterIR.Edge(wb, {})))
		builder:finalizeBlock(wb, LifterIR.Terminator.branch(s, back(wb), LifterIR.Edge(ws, {})))
		builder:finalizeBlock(ws, LifterIR.Terminator.jump(LifterIR.Edge(wh, { nextJ })))
		return wh
	end

	local sel = block("sel")
	local picked = call(sel, h, { index, zero }, "selected")
	local whA = whileLoop("a", twenty, nil)
	local whB = whileLoop("b", ten, nil)
	builder:finalizeBlock(sel, LifterIR.Terminator.branch(picked, LifterIR.Edge(whA, { one }), LifterIR.Edge(whB, { one })))
	local whZ = whileLoop("z", nil, sel)
	builder:finalizeBlock(work, LifterIR.Terminator.jump(LifterIR.Edge(whZ, { one })))

	builder:finalizeFunction(worker)
	return worker
end

local exports = {}
for _, kind in { "numeric", "generic", "while" } do
	local worker = addWorker(kind)
	local _, exported = builder:addInstruction(chunkBlock, LifterIR.Operation.functionRef(worker), { { type = functionValue, name_hint = "exported_worker" } }, { effects = pure, evidence = evidence })
	table.insert(exports, exported[1])
end
builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues(exports))
builder:finalizeFunction(chunk)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
