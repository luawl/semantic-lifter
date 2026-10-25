-- A loop that owns its exit while an escape in its body reaches that exit: an inner loop whose exit is the outer
-- loop's exit, or a loop-boundary exit beside it. The escape is carried by an escape flag through the transfer
-- wrappers of the body, so the owning loop must start every pass with that flag false.
-- Every decision is step(label), whose result the oracle scripts, and every note is step(label) with its result
-- unused. The first four workers are worker(step); in plain Luau:
--   owned_exit_infinite: step("entry") while true do step("H") while step("I") do
--     if step("B") then <next pass of the outer loop> end step("C") end <leave the outer loop> end return "exit"
--   owned_exit_while_reentered: while step("H0") do while not step("Q") do while step("I") do
--     if step("B") then <next pass of the middle loop> end step("C") end <leave the middle loop> end step("E") end
--     return "done"
--   owned_exit_boundary_exit_reentered: while step("H0") do while true do if not step("S") then
--     if not step("R") then <leave the middle loop> end step("P") end while step("I") do
--     if step("B") then <next pass of the middle loop> end if not step("C") then <leave the middle loop> end
--     step("Q") end <leave the middle loop> end step("E") end return "done"
--   owned_exit_latch: step("entry") repeat step("H") while step("I") do if step("B") then <go to the latch>
--     end step("C") end <leave the outer loop> until not step("L") return "exit"
-- The last three are worker(first, second, third, marker, step), a native numeric, generic and semantic-normalized
-- loop over the first three arguments whose exhaustion edge passes marker to the exit block:
--   for index do while step("I") do if step("B") then <next index> end step("C") end return index end
--   return marker
-- The eighth is worker(step) again: a loop boundary in an inner loop whose side escape leaves for the exit the
-- middle loop owns, while its side region continues the middle loop on one arm. That arm is a free target of the
-- side region, so the region is written inside a transfer wrapper, and the side arm sets the exit's flag after it:
--   side_escape_free_target: step("entry") while step("Z") do while true do step("H") while step("I") do
--     if step("B") then if step("L") then <next pass of the middle loop> end <leave the middle loop> end
--     step("C") end step("E") <leave the middle loop> end end return "done"
-- The ninth and tenth are worker(step) again: an inner loop whose `break` is a loop-boundary exit carried by its
-- exit's escape flag (its body is written inside a transfer wrapper for a nested `continue`), entered again by an
-- outer loop, so the flag must start false on every entry of the inner loop:
--   exit_reentered: while step("H0") do while step("I") do if step("A") then if step("B") then step("K")
--     <next pass of the inner loop> end end if step("X") then <leave the inner loop> end step("C") end step("E")
--     end return "done"
--   exit_to_infinite_header: the same inner loop last in the body of an outer infinite loop, so its exit is the
--     outer loop's header and the stop of the region that holds it: while true do step("H") while step("I") do
--     if step("A") then if step("B") then step("K") <next pass of the inner loop> end end
--     if step("X") then <leave the inner loop> end step("C") end end
-- The eleventh is worker(step) again: the eighth worker's loop boundary with a loop last in one arm of its side
-- region. That loop's exit continues the middle loop, a block that is not the side region's own continue target,
-- so the continue is carried by the middle loop's header flag, which the arm sets after the loop:
--   side_escape_loop_exit_continue: step("entry") while step("Z") do while true do step("H") while step("I") do
--     if step("B") then if not step("L") then while step("W") do if step("V") then <leave the middle loop> end
--     end <next pass of the middle loop> end <leave the middle loop> end step("C") end step("E")
--     <leave the middle loop> end end return "done"
-- The chunk returns the eleven workers in this order.
local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("loop-owned-exit-flag")
local proof = builder:addEvidence("dynamic_fixture", "fixture:loop-owned-exit-flag")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local dynamic = LifterIR.Types.dynamic()
local boolean = LifterIR.Types.boolean()
local number = LifterIR.Types.number()
local text = LifterIR.Types.string()
local functionValue = LifterIR.Types.functionValue()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)

local function constant(block, literal, ty, hint)
	local _, results = builder:addInstruction(block, LifterIR.Operation.constant(literal), { { type = ty, name_hint = hint } }, { effects = pure, evidence = evidence })
	return results[1]
end

-- step(label) in `block`: a decision returns the call's result, a note returns nothing.
local function addStep(block, step, kind, label)
	local _, labels = builder:addInstruction(block, LifterIR.Operation.constant(LifterIR.Literal.string(label)), { { type = text } }, { effects = pure, evidence = evidence })
	if kind == "decide" then
		local _, results = builder:addInstruction(block, LifterIR.Operation.call(step, { labels[1] }, LifterIR.ResultArity.fixed(1)), { { type = dynamic, name_hint = "at_" .. string.lower(label) } }, { effects = LifterIR.Effects.dynamicCall(), evidence = evidence })
		return results[1]
	end
	builder:addInstruction(block, LifterIR.Operation.call(step, { labels[1] }, LifterIR.ResultArity.fixed(0)), {}, { effects = LifterIR.Effects.dynamicCall(), evidence = evidence })
	return nil
end

-- Each step shape lists its blocks in block order; each block holds its steps and its terminator: { "jump", target },
-- { "branch", then target, else target } on the block's last decision, or { "return", text }.
local SHAPES = {
	owned_exit_infinite = {
		{ name = "entry", steps = { { "note", "entry" } }, exit = { "jump", "outer_header" } },
		{ name = "outer_header", steps = { { "note", "H" } }, exit = { "jump", "inner_header" } },
		{ name = "inner_header", steps = { { "decide", "I" } }, exit = { "branch", "inner_body", "left" } },
		{ name = "inner_body", steps = { { "decide", "B" } }, exit = { "branch", "outer_header", "inner_latch" } },
		{ name = "left", steps = {}, exit = { "return", "exit" } },
		{ name = "inner_latch", steps = { { "note", "C" } }, exit = { "jump", "inner_header" } },
	},
	owned_exit_while_reentered = {
		{ name = "outer_header", steps = { { "decide", "H0" } }, exit = { "branch", "middle_header", "done" } },
		{ name = "middle_header", steps = { { "decide", "Q" } }, exit = { "branch", "left", "inner_header" } },
		{ name = "inner_header", steps = { { "decide", "I" } }, exit = { "branch", "inner_body", "left" } },
		{ name = "inner_body", steps = { { "decide", "B" } }, exit = { "branch", "middle_header", "inner_latch" } },
		{ name = "left", steps = { { "note", "E" } }, exit = { "jump", "outer_header" } },
		{ name = "inner_latch", steps = { { "note", "C" } }, exit = { "jump", "inner_header" } },
		{ name = "done", steps = {}, exit = { "return", "done" } },
	},
	owned_exit_boundary_exit_reentered = {
		{ name = "outer_header", steps = { { "decide", "H0" } }, exit = { "branch", "middle_header", "done" } },
		{ name = "middle_header", steps = { { "decide", "S" } }, exit = { "branch", "inner_header", "exit_test" } },
		{ name = "inner_header", steps = { { "decide", "I" } }, exit = { "branch", "inner_body", "left" } },
		{ name = "exit_test", steps = { { "decide", "R" } }, exit = { "branch", "exit_continue", "left" } },
		{ name = "inner_body", steps = { { "decide", "B" } }, exit = { "branch", "middle_header", "inner_test" } },
		{ name = "inner_test", steps = { { "decide", "C" } }, exit = { "branch", "inner_continue", "left" } },
		{ name = "left", steps = { { "note", "E" } }, exit = { "jump", "outer_header" } },
		{ name = "done", steps = {}, exit = { "return", "done" } },
		{ name = "exit_continue", steps = { { "note", "P" } }, exit = { "jump", "inner_header" } },
		{ name = "inner_continue", steps = { { "note", "Q" } }, exit = { "jump", "inner_header" } },
	},
	owned_exit_latch = {
		{ name = "entry", steps = { { "note", "entry" } }, exit = { "jump", "outer_header" } },
		{ name = "outer_header", steps = { { "note", "H" } }, exit = { "jump", "inner_header" } },
		{ name = "inner_header", steps = { { "decide", "I" } }, exit = { "branch", "inner_body", "left" } },
		{ name = "inner_body", steps = { { "decide", "B" } }, exit = { "branch", "outer_latch", "inner_latch" } },
		{ name = "left", steps = {}, exit = { "return", "exit" } },
		{ name = "outer_latch", steps = { { "decide", "L" } }, exit = { "branch", "outer_header", "left" } },
		{ name = "inner_latch", steps = { { "note", "C" } }, exit = { "jump", "inner_header" } },
	},
	side_escape_free_target = {
		{ name = "entry", steps = { { "note", "entry" } }, exit = { "jump", "outer_header" } },
		{ name = "outer_header", steps = { { "decide", "Z" } }, exit = { "branch", "middle_header", "done" } },
		{ name = "middle_header", steps = { { "note", "H" } }, exit = { "jump", "inner_header" } },
		{ name = "inner_header", steps = { { "decide", "I" } }, exit = { "branch", "inner_body", "middle_left" } },
		{ name = "inner_body", steps = { { "decide", "B" } }, exit = { "branch", "side", "inner_latch" } },
		{ name = "side", steps = { { "decide", "L" } }, exit = { "branch", "middle_header", "outer_header" } },
		{ name = "inner_latch", steps = { { "note", "C" } }, exit = { "jump", "inner_header" } },
		{ name = "middle_left", steps = { { "note", "E" } }, exit = { "jump", "outer_header" } },
		{ name = "done", steps = {}, exit = { "return", "done" } },
	},
	exit_reentered = {
		{ name = "outer_header", steps = { { "decide", "H0" } }, exit = { "branch", "inner_header", "done" } },
		{ name = "inner_header", steps = { { "decide", "I" } }, exit = { "branch", "a_test", "left" } },
		{ name = "a_test", steps = { { "decide", "A" } }, exit = { "branch", "b_test", "boundary" } },
		{ name = "b_test", steps = { { "decide", "B" } }, exit = { "branch", "cont", "boundary" } },
		{ name = "cont", steps = { { "note", "K" } }, exit = { "jump", "inner_header" } },
		{ name = "boundary", steps = { { "decide", "X" } }, exit = { "branch", "left", "tail" } },
		{ name = "tail", steps = { { "note", "C" } }, exit = { "jump", "inner_header" } },
		{ name = "left", steps = { { "note", "E" } }, exit = { "jump", "outer_header" } },
		{ name = "done", steps = {}, exit = { "return", "done" } },
	},
	exit_to_infinite_header = {
		{ name = "outer_header", steps = { { "note", "H" } }, exit = { "jump", "inner_header" } },
		{ name = "inner_header", steps = { { "decide", "I" } }, exit = { "branch", "a_test", "outer_header" } },
		{ name = "a_test", steps = { { "decide", "A" } }, exit = { "branch", "b_test", "boundary" } },
		{ name = "b_test", steps = { { "decide", "B" } }, exit = { "branch", "cont", "boundary" } },
		{ name = "cont", steps = { { "note", "K" } }, exit = { "jump", "inner_header" } },
		{ name = "boundary", steps = { { "decide", "X" } }, exit = { "branch", "outer_header", "tail" } },
		{ name = "tail", steps = { { "note", "C" } }, exit = { "jump", "inner_header" } },
	},
	side_escape_loop_exit_continue = {
		{ name = "entry", steps = { { "note", "entry" } }, exit = { "jump", "outer_header" } },
		{ name = "outer_header", steps = { { "decide", "Z" } }, exit = { "branch", "middle_header", "done" } },
		{ name = "middle_header", steps = { { "note", "H" } }, exit = { "jump", "inner_header" } },
		{ name = "inner_header", steps = { { "decide", "I" } }, exit = { "branch", "inner_body", "middle_left" } },
		{ name = "inner_body", steps = { { "decide", "B" } }, exit = { "branch", "side", "inner_latch" } },
		{ name = "side", steps = { { "decide", "L" } }, exit = { "branch", "outer_header", "side_loop" } },
		{ name = "side_loop", steps = { { "decide", "W" } }, exit = { "branch", "side_loop_body", "middle_header" } },
		{ name = "side_loop_body", steps = { { "decide", "V" } }, exit = { "branch", "outer_header", "side_loop" } },
		{ name = "inner_latch", steps = { { "note", "C" } }, exit = { "jump", "inner_header" } },
		{ name = "middle_left", steps = { { "note", "E" } }, exit = { "jump", "outer_header" } },
		{ name = "done", steps = {}, exit = { "return", "done" } },
	},
}

-- The order in which each step shape's blocks receive their steps and terminators.
local FILL_ORDER = {
	owned_exit_infinite = { "entry", "outer_header", "inner_header", "inner_body", "inner_latch", "left" },
	owned_exit_while_reentered = { "outer_header", "middle_header", "inner_header", "inner_body", "inner_latch", "left", "done" },
	owned_exit_boundary_exit_reentered = {
		"outer_header",
		"middle_header",
		"exit_test",
		"exit_continue",
		"inner_header",
		"inner_body",
		"inner_test",
		"inner_continue",
		"left",
		"done",
	},
	owned_exit_latch = { "entry", "outer_header", "inner_header", "inner_body", "left", "outer_latch", "inner_latch" },
	side_escape_free_target = {
		"entry",
		"outer_header",
		"middle_header",
		"inner_header",
		"inner_body",
		"side",
		"inner_latch",
		"middle_left",
		"done",
	},
	exit_reentered = {
		"outer_header",
		"inner_header",
		"a_test",
		"b_test",
		"cont",
		"boundary",
		"tail",
		"left",
		"done",
	},
	exit_to_infinite_header = { "outer_header", "inner_header", "a_test", "b_test", "cont", "boundary", "tail" },
	side_escape_loop_exit_continue = {
		"entry",
		"outer_header",
		"middle_header",
		"inner_header",
		"inner_body",
		"side",
		"side_loop",
		"side_loop_body",
		"inner_latch",
		"middle_left",
		"done",
	},
}

local function addStepWorker(shape)
	local blocks = SHAPES[shape]
	assert(blocks ~= nil, "unknown shape " .. tostring(shape))
	local worker = builder:reserveFunction({ name_hint = shape, evidence = evidence })
	local step = builder:addParameter(worker, functionValue, "step")
	local ids = {}
	local specs = {}
	for _, spec in blocks do
		ids[spec.name] = builder:reserveBlock(worker, { name_hint = spec.name, evidence = evidence })
		specs[spec.name] = spec
	end
	builder:setFunctionEntry(worker, ids[blocks[1].name])
	for _, name in FILL_ORDER[shape] do
		local spec = specs[name]
		local block = ids[name]
		local condition = nil
		for _, item in spec.steps do
			local result = addStep(block, step, item[1], item[2])
			if result ~= nil then
				condition = result
			end
		end
		local exit = spec.exit
		if exit[1] == "jump" then
			builder:finalizeBlock(block, LifterIR.Terminator.jump(LifterIR.Edge(ids[exit[2]], {})))
		elseif exit[1] == "branch" then
			assert(condition ~= nil, shape .. ": block " .. name .. " branches without a decision")
			builder:finalizeBlock(block, LifterIR.Terminator.branch(condition, LifterIR.Edge(ids[exit[2]], {}), LifterIR.Edge(ids[exit[3]], {})))
		else
			local _, values = builder:addInstruction(block, LifterIR.Operation.constant(LifterIR.Literal.string(exit[2])), { { type = text } }, { effects = pure, evidence = evidence })
			builder:finalizeBlock(block, LifterIR.Terminator.returnValues(values))
		end
	end
	builder:finalizeFunction(worker)
	return worker
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

local function addNativeWorker(kind)
	local stateType = if kind == "numeric" then number else dynamic
	local worker = builder:reserveFunction({ name_hint = "owned_exit_" .. kind .. "_for", evidence = evidence })
	local p1 = builder:addParameter(worker, stateType, "first")
	local p2 = builder:addParameter(worker, stateType, "second")
	local p3 = builder:addParameter(worker, stateType, "third")
	local marker = builder:addParameter(worker, dynamic, "marker")
	local step = builder:addParameter(worker, functionValue, "step")

	local function block(hint)
		return builder:reserveBlock(worker, { name_hint = hint, evidence = evidence })
	end

	local entry = block("entry")
	local header = block("header")
	local body = block("body")
	local exit = block("exit")
	local innerHeader = block("inner_header")
	local innerBody = block("inner_body")
	local innerLatch = block("inner_latch")
	builder:setFunctionEntry(worker, entry)
	local h1 = builder:addBlockParameter(header, stateType, "h1")
	local h2 = builder:addBlockParameter(header, stateType, "h2")
	local h3 = builder:addBlockParameter(header, stateType, "h3")
	local hInit = builder:addBlockParameter(header, boolean, "h_initial")
	local index = builder:addBlockParameter(body, stateType, "index")
	local found = builder:addBlockParameter(exit, dynamic, "found")
	local entryFlag = constant(entry, LifterIR.Literal.boolean(kind ~= "semantic"), boolean, "entry_flag")
	local laterFlag = constant(entry, LifterIR.Literal.boolean(false), boolean, "later_flag")
	local t, back3 = transition(kind, header, h1, h2, h3, hInit)
	builder:finalizeBlock(header, LifterIR.Terminator.branch(t[1], LifterIR.Edge(body, { t[4] }), LifterIR.Edge(exit, { marker })))
	builder:finalizeBlock(exit, LifterIR.Terminator.returnValues({ found }))
	builder:finalizeBlock(entry, LifterIR.Terminator.jump(LifterIR.Edge(header, { p1, p2, p3, entryFlag })))
	builder:finalizeBlock(body, LifterIR.Terminator.jump(LifterIR.Edge(innerHeader, {})))
	local more = addStep(innerHeader, step, "decide", "I")
	builder:finalizeBlock(innerHeader, LifterIR.Terminator.branch(more, LifterIR.Edge(innerBody, {}), LifterIR.Edge(exit, { index })))
	local nextIndex = addStep(innerBody, step, "decide", "B")
	builder:finalizeBlock(innerBody, LifterIR.Terminator.branch(nextIndex, LifterIR.Edge(header, { back3[1], back3[2], back3[3], laterFlag }), LifterIR.Edge(innerLatch, {})))
	addStep(innerLatch, step, "note", "C")
	builder:finalizeBlock(innerLatch, LifterIR.Terminator.jump(LifterIR.Edge(innerHeader, {})))
	builder:finalizeFunction(worker)
	return worker
end

local exports = {}
local function export(worker)
	local _, exported = builder:addInstruction(chunkBlock, LifterIR.Operation.functionRef(worker), { { type = functionValue, name_hint = "exported_worker" } }, { effects = pure, evidence = evidence })
	table.insert(exports, exported[1])
end
for _, shape in { "owned_exit_infinite", "owned_exit_while_reentered", "owned_exit_boundary_exit_reentered", "owned_exit_latch" } do
	export(addStepWorker(shape))
end
for _, kind in { "numeric", "generic", "semantic" } do
	export(addNativeWorker(kind))
end
export(addStepWorker("side_escape_free_target"))
export(addStepWorker("exit_reentered"))
export(addStepWorker("exit_to_infinite_header"))
export(addStepWorker("side_escape_loop_exit_continue"))
builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues(exports))
builder:finalizeFunction(chunk)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
