-- Author-written chains at the edge of the readable certificates: nested native loops whose `for` frames and
-- completion locals fill the 255-register frame, and an escape chain whose transfer wrappers fill the syntax budget.
-- One worker per document:
--   lune run native_loop_register_conformance.luau <out.json> <shape> <depth>
-- The worker is worker(f, observe, marker, first, last, stride), returned by the chunk; every loop runs over
-- first, last and stride.
--   frame_chain: depth nested native numeric loops whose exhaustion edges pass no value, so no loop declares a
--     completion local: each level holds its `for` frame (limit, step and the index).
--   generic_chain: frame_chain with one-name native generic loops over (first, last, stride).
--   completion_chain: frame_chain whose exhaustion edges pass the outer value to an exit-block parameter that the
--     exit block observes, so each level also declares a completion local before its `for`.
--   acyclic_chain: depth nested one-shot native numeric loops (no latch). Each header is entered by a jump from the
--     outer level's body, so its four parameters are aliases, and each body joins the header's exit target.
--   acyclic_generic_chain: acyclic_chain with one-name native generic loops.
--   escape_chain: if f(1) then if f(2) then ... if f(depth) then observe(0) goto J1 end observe(depth) ... end
--     observe(2) end J1: observe(1), then if f(-1) return marker, else first. The escape from the innermost arm to
--     J1 crosses depth - 1 arms whose stop is their own join; each is written inside a transfer wrapper for J1.
local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
local shape = process.args[2]
local depth = tonumber(process.args[3])
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")
assert(shape ~= nil and depth ~= nil and depth >= 1, "expected a shape and a depth of at least 1")

local builder = LifterIR.Builder.new("native-loop-register-" .. shape)
local proof = builder:addEvidence("dynamic_fixture", "fixture:native-loop-register-" .. shape)
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

local function constant(target, literal, ty, hint)
	local _, results = builder:addInstruction(target, LifterIR.Operation.constant(literal), { { type = ty, name_hint = hint } }, { effects = pure, evidence = evidence })
	return results[1]
end

local function call(target, fn, args, hint)
	local _, results = builder:addInstruction(target, LifterIR.Operation.call(fn, args, LifterIR.ResultArity.fixed(1)), { { type = dynamic, name_hint = hint } }, { effects = LifterIR.Effects.dynamicCall(), evidence = evidence })
	return results[1]
end

local function note(target, fn, args)
	builder:addInstruction(target, LifterIR.Operation.call(fn, args, LifterIR.ResultArity.fixed(0)), {}, { effects = LifterIR.Effects.dynamicCall(), evidence = evidence })
end

local function jump(source, target, args)
	builder:finalizeBlock(source, LifterIR.Terminator.jump(LifterIR.Edge(target, args or {})))
end

local function branch(source, condition, thenTarget, thenArgs, elseTarget, elseArgs)
	builder:finalizeBlock(source, LifterIR.Terminator.branch(condition, LifterIR.Edge(thenTarget, thenArgs or {}), LifterIR.Edge(elseTarget, elseArgs or {})))
end

local function returns(source, values)
	builder:finalizeBlock(source, LifterIR.Terminator.returnValues(values))
end

local worker = builder:reserveFunction({ name_hint = shape, evidence = evidence })
local f = builder:addParameter(worker, functionValue, "f")
local observe = builder:addParameter(worker, functionValue, "observe")
local marker = builder:addParameter(worker, dynamic, "marker")
local first = builder:addParameter(worker, number, "first")
local last = builder:addParameter(worker, number, "last")
local stride = builder:addParameter(worker, number, "stride")

local function block(hint)
	return builder:reserveBlock(worker, { name_hint = hint, evidence = evidence })
end

local entry = block("entry")
builder:setFunctionEntry(worker, entry)

-- A native loop header of one level: its four parameters (control, limit, step and the initial flag, or the
-- iterator, state, control and the initial flag of a generic loop), its body block with the loop variable, and the
-- transition whose first result decides between them.
local function header(hint, generic)
	local headerBlock = block(hint .. "_header")
	local p1 = builder:addBlockParameter(headerBlock, generic and dynamic or number, hint .. (generic and "_iterator" or "_control"))
	local p2 = builder:addBlockParameter(headerBlock, generic and dynamic or number, hint .. (generic and "_state" or "_limit"))
	local p3 = builder:addBlockParameter(headerBlock, generic and dynamic or number, hint .. (generic and "_control" or "_step"))
	local p4 = builder:addBlockParameter(headerBlock, boolean, hint .. "_initial")
	local body = block(hint .. "_body")
	local index = builder:addBlockParameter(body, generic and dynamic or number, hint .. "_index")
	local results
	if generic then
		local _, generated = builder:addInstruction(headerBlock, LifterIR.Operation.genericForNext(p1, p2, p3, p4, 1), {
			{ type = boolean, name_hint = hint .. "_has_value" },
			{ type = dynamic, name_hint = hint .. "_prepared_iterator" },
			{ type = dynamic, name_hint = hint .. "_prepared_state" },
			{ type = dynamic, name_hint = hint .. "_next_index" },
		}, { effects = LifterIR.Effects.genericForNext(), evidence = evidence })
		results = generated
	else
		local _, generated = builder:addInstruction(headerBlock, LifterIR.Operation.numericForNext(p1, p2, p3, p4), {
			{ type = boolean, name_hint = hint .. "_has_value" },
			{ type = number, name_hint = hint .. "_normalized_limit" },
			{ type = number, name_hint = hint .. "_normalized_step" },
			{ type = number, name_hint = hint .. "_next_control" },
		}, { effects = LifterIR.Effects.numericForNext(), evidence = evidence })
		results = generated
	end
	return headerBlock, body, index, results
end

-- frame_chain, generic_chain and completion_chain: level k runs one native loop whose body holds level k + 1 and
-- whose latch passes the transition's state back to the header.
local function cyclicChain(generic, completion)
	local trueValue = constant(entry, LifterIR.Literal.boolean(true), boolean, "initial_transition")
	local falseValue = constant(entry, LifterIR.Literal.boolean(false), boolean, "later_transition")
	local seed = call(entry, f, { marker }, "seed")
	local function level(k, preheader, after, outerValue)
		local holdExit = block("hold_exit" .. k)
		local exitArgs = {}
		local holdMarker = nil
		if completion then
			holdMarker = builder:addBlockParameter(holdExit, dynamic, "hold_marker" .. k)
			exitArgs = { outerValue }
		end
		local loopHeader, body, index, results = header("hold" .. k, generic)
		jump(preheader, loopHeader, { first, last, stride, trueValue })
		branch(loopHeader, results[1], body, { results[4] }, holdExit, exitArgs)
		local latch = block("hold" .. k .. "_latch")
		if generic then
			jump(latch, loopHeader, { results[2], results[3], results[4], falseValue })
		else
			jump(latch, loopHeader, { results[4], results[2], results[3], falseValue })
		end
		if k < depth then
			level(k + 1, body, latch, index)
		else
			note(body, observe, { index })
			jump(body, latch)
		end
		if completion then
			note(holdExit, observe, { holdMarker })
		end
		jump(holdExit, after)
	end
	local done = block("done")
	level(1, entry, done, seed)
	returns(done, { marker })
end

-- acyclic_chain and acyclic_generic_chain: level k's header is entered by a jump from the outer level's body and
-- leaves to the join J_k; its body enters level k + 1, whose join jumps to J_k.
local function acyclicChain(generic)
	local trueValue = constant(entry, LifterIR.Literal.boolean(true), boolean, "initial_transition")
	local seed = call(entry, f, { marker }, "seed")
	note(entry, observe, { seed })
	local function level(k, preheader, join)
		local loopHeader, body, index, results = header("hold" .. k, generic)
		jump(preheader, loopHeader, { first, last, stride, trueValue })
		branch(loopHeader, results[1], body, { results[4] }, join, {})
		if k < depth then
			local innerJoin = block("join" .. (k + 1))
			level(k + 1, body, innerJoin)
			jump(innerJoin, join)
		else
			note(body, observe, { index })
			jump(body, join)
		end
	end
	local done = block("join1")
	level(1, entry, done)
	returns(done, { marker })
end

local function escapeChain()
	local numbers = {}
	local function num(k)
		if numbers[k] == nil then
			local hint = if k < 0 then "cm" .. tostring(-k) else "c" .. tostring(k)
			numbers[k] = constant(entry, LifterIR.Literal.number(k), number, hint)
		end
		return numbers[k]
	end
	for k = -1, depth do
		num(k)
	end
	local arms, joins = {}, {}
	for k = 1, depth do
		arms[k] = block("arm" .. k)
		joins[k] = block("join" .. k)
	end
	local escapeArm = block("escape_arm")
	jump(entry, arms[1])
	for k = 1, depth - 1 do
		local decision = call(arms[k], f, { num(k) }, "d" .. k)
		branch(arms[k], decision, arms[k + 1], {}, joins[k], {})
	end
	local innermost = call(arms[depth], f, { num(depth) }, "d" .. depth)
	branch(arms[depth], innermost, escapeArm, {}, joins[depth], {})
	note(escapeArm, observe, { num(0) })
	jump(escapeArm, joins[1])
	for k = depth, 2, -1 do
		note(joins[k], observe, { num(k) })
		jump(joins[k], joins[k - 1])
	end
	note(joins[1], observe, { num(1) })
	local tail = call(joins[1], f, { num(-1) }, "tail")
	local tailMarker, tailFirst = block("tail_marker"), block("tail_first")
	branch(joins[1], tail, tailMarker, {}, tailFirst, {})
	returns(tailMarker, { marker })
	returns(tailFirst, { first })
end

if shape == "frame_chain" then
	cyclicChain(false, false)
elseif shape == "generic_chain" then
	cyclicChain(true, false)
elseif shape == "completion_chain" then
	cyclicChain(false, true)
elseif shape == "acyclic_chain" then
	acyclicChain(false)
elseif shape == "acyclic_generic_chain" then
	acyclicChain(true)
elseif shape == "escape_chain" then
	escapeChain()
else
	error("unknown shape " .. tostring(shape))
end

builder:finalizeFunction(worker)
local _, exported = builder:addInstruction(chunkBlock, LifterIR.Operation.functionRef(worker), { { type = functionValue, name_hint = "exported_worker" } }, { effects = pure, evidence = evidence })
builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exported[1] }))
builder:finalizeFunction(chunk)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
