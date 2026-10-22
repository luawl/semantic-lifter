-- Lexical continues the structured layout would write where the innermost Luau loop statement is not the loop they
-- continue: a transfer wrapper (`repeat ... until true`) whose stop is another block, or a loop whose header is not
-- the continue's target. Each worker is worker(n, m, marker, f, g, observe) and runs one loop over i1 = 1, 2, ...;
-- in plain Luau (J is the join: observe(100), then return marker when n < i1, else the next pass):
--   final_block_continue: if f(i1) then if f(i1, 1) then observe(300) continue end
--     if g(i1) then if observe(i1) then observe(250) continue end else return i1 end end J
--   continue_after_final_loop: if f(i1) then j = 1 while not (m < j) do if g(j) then goto J end observe(j) j += 1 end
--     continue end J
--   continue_after_final_infinite_loop: if f(i1) then j = 1 while not (m < j) do if g(j) then goto J end j += 1 end
--     k = 1 loop observe(k) if m < k + 1 then continue end observe(250) k += 1 end end J
--   empty_arm_continue: final_block_continue without observe(300)
--   empty_arm_continue_owned_escape: if f(i1) then j = 1 while not (m < j) do if g(j) then goto J end j += 1 end
--     if f(i1, 1) then continue end end J
--   empty_arm_nonlocal_continue: if f(i1) then if g(i1) then if observe(i1) then continue end else return i1 end end J
--   boundary_body_escape_continue: if f(i1) then if g(i1) then observe(i1) j = 1
--     while not (m < j) do if g(j) then goto J end j += 1 end observe(300) else return i1 end end J
--   boundary_body_escape_continue_exit: the same, where J leaves the loop when n < i1 to observe(400) return marker
--   boundary_body_escape_continue_wrapped: if f(i1) then if f(i1, 1) then <the inner branch of
--     boundary_body_escape_continue, its loop leaving to Z> end Z: if g(i1, 1) then if observe(250) then
--     observe(300) continue end else return marker end end J
--   boundary_arm_escape_continue: if f(i1) then if g(i1) then if observe(i1) then j = 1
--     while not (m < j) do if g(j) then goto J end j += 1 end observe(300) end else return i1 end end J
--   boundary_arm_escape_continue_else: the same with else observe(400) on the observe(i1) branch
--   boundary_arm_escape_continue_exit: the _else shape, where J leaves the loop when n < i1 to observe(500) return marker
-- The chunk returns the twelve workers in this order.
local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("wrapped-continue")
local proof = builder:addEvidence("dynamic_fixture", "fixture:wrapped-continue")
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

local function binary(target, op, a, b, ty, hint)
	local _, results = builder:addInstruction(target, LifterIR.Operation.binary(op, a, b, "primitive"), { { type = ty, name_hint = hint } }, { effects = pure, evidence = evidence })
	return results[1]
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

local function addWorker(shape)
	local worker = builder:reserveFunction({ name_hint = shape, evidence = evidence })
	local n = builder:addParameter(worker, number, "n")
	local m = builder:addParameter(worker, number, "m")
	local marker = builder:addParameter(worker, dynamic, "marker")
	local f = builder:addParameter(worker, functionValue, "f")
	local g = builder:addParameter(worker, functionValue, "g")
	local observe = builder:addParameter(worker, functionValue, "observe")

	local function block(hint)
		return builder:reserveBlock(worker, { name_hint = hint, evidence = evidence })
	end

	local entry = block("entry")
	builder:setFunctionEntry(worker, entry)
	local zero = constant(entry, LifterIR.Literal.number(0), number, "zero")
	local one = constant(entry, LifterIR.Literal.number(1), number, "one")
	local hundred = constant(entry, LifterIR.Literal.number(100), number, "hundred")

	if shape == "final_block_continue" or shape == "empty_arm_continue" then
		local c250 = constant(entry, LifterIR.Literal.number(250), number, "c250")
		local c300 = constant(entry, LifterIR.Literal.number(300), number, "c300")
		local H = block("outer_header")
		local i = builder:addBlockParameter(H, number, "i")
		local T = block("test")
		local P = block("pre_test")
		local A = block("arm")
		local K = block("inner_test")
		local KC = block("inner_continue")
		local PC = if shape == "final_block_continue" then block("pre_continue") else nil
		local J = block("join")
		local L = block("back")
		local RET = block("ret")
		local XR = block("exit_return")
		jump(entry, H, { zero })
		local i1 = binary(H, "add", i, one, number, "i1")
		jump(H, T)
		local c = call(T, f, { i1 }, "c")
		branch(T, c, P, {}, J, {})
		local p = call(P, f, { i1, one }, "p")
		if PC then
			branch(P, p, PC, {}, A, {})
			call(PC, observe, { c300 }, "pc")
			jump(PC, H, { i1 })
		else
			branch(P, p, H, { i1 }, A, {})
		end
		local d = call(A, g, { i1 }, "d")
		branch(A, d, K, {}, RET, {})
		local e = call(K, observe, { i1 }, "e")
		branch(K, e, KC, {}, J, {})
		call(KC, observe, { c250 }, "kc")
		jump(KC, H, { i1 })
		call(J, observe, { hundred }, "o")
		local done = binary(J, "less", n, i1, boolean, "done")
		branch(J, done, XR, {}, L, {})
		jump(L, H, { i1 })
		returns(RET, { i1 })
		returns(XR, { marker })
	elseif shape == "empty_arm_continue_owned_escape" then
		constant(entry, LifterIR.Literal.number(250), number, "c250")
		constant(entry, LifterIR.Literal.number(300), number, "c300")
		local H = block("outer_header")
		local i = builder:addBlockParameter(H, number, "i")
		local T = block("test")
		local W = block("inner_header")
		local j = builder:addBlockParameter(W, number, "j")
		local WB = block("inner_body")
		local WL = block("inner_latch")
		local P = block("after_inner")
		local J = block("join")
		local L = block("back")
		local XR = block("exit_return")
		jump(entry, H, { zero })
		local i1 = binary(H, "add", i, one, number, "i1")
		jump(H, T)
		local c = call(T, f, { i1 }, "c")
		branch(T, c, W, { one }, J, {})
		local wdone = binary(W, "less", m, j, boolean, "inner_done")
		branch(W, wdone, P, {}, WB, {})
		local s = call(WB, g, { j }, "s")
		branch(WB, s, J, {}, WL, {})
		local j1 = binary(WL, "add", j, one, number, "next_j")
		jump(WL, W, { j1 })
		local p = call(P, f, { i1, one }, "p")
		branch(P, p, H, { i1 }, J, {})
		call(J, observe, { hundred }, "o")
		local done = binary(J, "less", n, i1, boolean, "done")
		branch(J, done, XR, {}, L, {})
		jump(L, H, { i1 })
		returns(XR, { marker })
	elseif shape == "continue_after_final_loop" then
		constant(entry, LifterIR.Literal.number(250), number, "c250")
		constant(entry, LifterIR.Literal.number(300), number, "c300")
		local H = block("outer_header")
		local i = builder:addBlockParameter(H, number, "i")
		local T = block("test")
		local W = block("inner_header")
		local j = builder:addBlockParameter(W, number, "j")
		local WB = block("inner_body")
		local WL = block("inner_latch")
		local J = block("join")
		local L = block("back")
		local XR = block("exit_return")
		jump(entry, H, { zero })
		local i1 = binary(H, "add", i, one, number, "i1")
		jump(H, T)
		local c = call(T, f, { i1 }, "c")
		branch(T, c, W, { one }, J, {})
		local wdone = binary(W, "less", m, j, boolean, "inner_done")
		branch(W, wdone, H, { i1 }, WB, {})
		local s = call(WB, g, { j }, "s")
		branch(WB, s, J, {}, WL, {})
		call(WL, observe, { j }, "w")
		local j1 = binary(WL, "add", j, one, number, "next_j")
		jump(WL, W, { j1 })
		call(J, observe, { hundred }, "o")
		local done = binary(J, "less", n, i1, boolean, "done")
		branch(J, done, XR, {}, L, {})
		jump(L, H, { i1 })
		returns(XR, { marker })
	elseif shape == "continue_after_final_infinite_loop" then
		local c250 = constant(entry, LifterIR.Literal.number(250), number, "c250")
		constant(entry, LifterIR.Literal.number(300), number, "c300")
		local H = block("outer_header")
		local i = builder:addBlockParameter(H, number, "i")
		local T = block("test")
		local W1 = block("first_header")
		local j = builder:addBlockParameter(W1, number, "j")
		local WB = block("first_body")
		local WL = block("first_latch")
		local W2 = block("second_header")
		local k = builder:addBlockParameter(W2, number, "k")
		local W2T = block("second_exit_test")
		local W2C = block("second_latch")
		local J = block("join")
		local L = block("back")
		local XR = block("exit_return")
		jump(entry, H, { zero })
		local i1 = binary(H, "add", i, one, number, "i1")
		jump(H, T)
		local c = call(T, f, { i1 }, "c")
		branch(T, c, W1, { one }, J, {})
		local wdone = binary(W1, "less", m, j, boolean, "first_done")
		branch(W1, wdone, W2, { one }, WB, {})
		local s = call(WB, g, { j }, "s")
		branch(WB, s, J, {}, WL, {})
		local j1 = binary(WL, "add", j, one, number, "next_j")
		jump(WL, W1, { j1 })
		call(W2, observe, { k }, "w")
		jump(W2, W2T)
		local k1 = binary(W2T, "add", k, one, number, "next_k")
		local kdone = binary(W2T, "less", m, k1, boolean, "second_done")
		branch(W2T, kdone, H, { i1 }, W2C, {})
		call(W2C, observe, { c250 }, "wc")
		jump(W2C, W2, { k1 })
		call(J, observe, { hundred }, "o")
		local done = binary(J, "less", n, i1, boolean, "done")
		branch(J, done, XR, {}, L, {})
		jump(L, H, { i1 })
		returns(XR, { marker })
	elseif shape == "empty_arm_nonlocal_continue" then
		local H = block("outer_header")
		local i = builder:addBlockParameter(H, number, "i")
		local T = block("test")
		local A = block("arm")
		local K = block("inner_test")
		local J = block("join")
		local L = block("back")
		local RET = block("ret")
		local XR = block("exit_return")
		jump(entry, H, { zero })
		local i1 = binary(H, "add", i, one, number, "i1")
		jump(H, T)
		local c = call(T, f, { i1 }, "c")
		branch(T, c, A, {}, J, {})
		local d = call(A, g, { i1 }, "d")
		branch(A, d, K, {}, RET, {})
		local e = call(K, observe, { i1 }, "e")
		branch(K, e, H, { i1 }, J, {})
		call(J, observe, { hundred }, "o")
		local done = binary(J, "less", n, i1, boolean, "done")
		branch(J, done, XR, {}, L, {})
		jump(L, H, { i1 })
		returns(RET, { i1 })
		returns(XR, { marker })
	elseif shape == "boundary_body_escape_continue" or shape == "boundary_body_escape_continue_exit" then
		constant(entry, LifterIR.Literal.number(250), number, "c250")
		local c300 = constant(entry, LifterIR.Literal.number(300), number, "c300")
		local exits = shape == "boundary_body_escape_continue_exit"
		local H = block("outer_header")
		local i = builder:addBlockParameter(H, number, "i")
		local T = block("test")
		local A = block("arm")
		local K = block("body_entry")
		local W = block("inner_header")
		local j = builder:addBlockParameter(W, number, "j")
		local WB = block("inner_body")
		local WL = block("inner_latch")
		local P = block("inner_exit")
		local J = block("join")
		local L = block("back")
		local RET = block("ret")
		local XR = if exits then nil else block("exit_return")
		local X = if exits then block("loop_exit") else nil
		local END = if exits then block("end_return") else nil
		local c400 = if exits then constant(entry, LifterIR.Literal.number(400), number, "c400") else nil
		jump(entry, H, { zero })
		local i1 = binary(H, "add", i, one, number, "i1")
		jump(H, T)
		local c = call(T, f, { i1 }, "c")
		branch(T, c, A, {}, J, {})
		local d = call(A, g, { i1 }, "d")
		branch(A, d, K, {}, RET, {})
		call(K, observe, { i1 }, "k")
		jump(K, W, { one })
		local wdone = binary(W, "less", m, j, boolean, "inner_done")
		branch(W, wdone, P, {}, WB, {})
		local s = call(WB, g, { j }, "s")
		branch(WB, s, J, {}, WL, {})
		local j1 = binary(WL, "add", j, one, number, "next_j")
		jump(WL, W, { j1 })
		call(P, observe, { c300 }, "q")
		jump(P, J)
		call(J, observe, { hundred }, "o")
		local done = binary(J, "less", n, i1, boolean, "done")
		if exits then
			branch(J, done, X, {}, L, {})
			jump(L, H, { i1 })
			returns(RET, { i1 })
			call(X, observe, { c400 }, "x")
			jump(X, END)
			returns(END, { marker })
		else
			branch(J, done, XR, {}, L, {})
			jump(L, H, { i1 })
			returns(RET, { i1 })
			returns(XR, { marker })
		end
	elseif shape == "boundary_body_escape_continue_wrapped" then
		local c250 = constant(entry, LifterIR.Literal.number(250), number, "c250")
		local c300 = constant(entry, LifterIR.Literal.number(300), number, "c300")
		local H = block("outer_header")
		local i = builder:addBlockParameter(H, number, "i")
		local T = block("test")
		local P = block("x_test")
		local A = block("arm")
		local K = block("body_entry")
		local W = block("inner_header")
		local j = builder:addBlockParameter(W, number, "j")
		local WB = block("inner_body")
		local WL = block("inner_latch")
		local Q = block("inner_exit")
		local Z = block("x_join")
		local K2 = block("second_body")
		local KC = block("second_continue")
		local J = block("join")
		local L = block("back")
		local RET = block("ret")
		local RET2 = block("ret_marker")
		local XR = block("exit_return")
		jump(entry, H, { zero })
		local i1 = binary(H, "add", i, one, number, "i1")
		jump(H, T)
		local c = call(T, f, { i1 }, "c")
		branch(T, c, P, {}, J, {})
		local p = call(P, f, { i1, one }, "p")
		branch(P, p, A, {}, Z, {})
		local d = call(A, g, { i1 }, "d")
		branch(A, d, K, {}, RET, {})
		call(K, observe, { i1 }, "k")
		jump(K, W, { one })
		local wdone = binary(W, "less", m, j, boolean, "inner_done")
		branch(W, wdone, Q, {}, WB, {})
		local s = call(WB, g, { j }, "s")
		branch(WB, s, Z, {}, WL, {})
		local j1 = binary(WL, "add", j, one, number, "next_j")
		jump(WL, W, { j1 })
		call(Q, observe, { c300 }, "q")
		jump(Q, Z)
		local z = call(Z, g, { i1, one }, "z")
		branch(Z, z, K2, {}, RET2, {})
		local e2 = call(K2, observe, { c250 }, "e2")
		branch(K2, e2, KC, {}, J, {})
		call(KC, observe, { c300 }, "kc")
		jump(KC, H, { i1 })
		call(J, observe, { hundred }, "o")
		local done = binary(J, "less", n, i1, boolean, "done")
		branch(J, done, XR, {}, L, {})
		jump(L, H, { i1 })
		returns(RET, { i1 })
		returns(RET2, { marker })
		returns(XR, { marker })
	elseif shape == "boundary_arm_escape_continue" or shape == "boundary_arm_escape_continue_else" or shape == "boundary_arm_escape_continue_exit" then
		local c300 = constant(entry, LifterIR.Literal.number(300), number, "c300")
		local c400 = constant(entry, LifterIR.Literal.number(400), number, "c400")
		local c500 = constant(entry, LifterIR.Literal.number(500), number, "c500")
		local H = block("outer_header")
		local i = builder:addBlockParameter(H, number, "i")
		local T = block("test")
		local A = block("arm")
		local K = block("body_test")
		local W = block("inner_header")
		local j = builder:addBlockParameter(W, number, "j")
		local WB = block("inner_body")
		local WL = block("inner_latch")
		local P = block("inner_exit")
		local KE = if shape ~= "boundary_arm_escape_continue" then block("body_else") else nil
		local J = block("join")
		local L = block("back")
		local RET = block("ret")
		local XR = if shape ~= "boundary_arm_escape_continue_exit" then block("exit_return") else nil
		local X = if shape == "boundary_arm_escape_continue_exit" then block("loop_exit") else nil
		local END = if shape == "boundary_arm_escape_continue_exit" then block("end_return") else nil
		jump(entry, H, { zero })
		local i1 = binary(H, "add", i, one, number, "i1")
		jump(H, T)
		local c = call(T, f, { i1 }, "c")
		branch(T, c, A, {}, J, {})
		local d = call(A, g, { i1 }, "d")
		branch(A, d, K, {}, RET, {})
		local e = call(K, observe, { i1 }, "e")
		if KE then
			branch(K, e, W, { one }, KE, {})
			call(KE, observe, { c400 }, "ke")
			jump(KE, J)
		else
			branch(K, e, W, { one }, J, {})
		end
		local wdone = binary(W, "less", m, j, boolean, "inner_done")
		branch(W, wdone, P, {}, WB, {})
		local s = call(WB, g, { j }, "s")
		branch(WB, s, J, {}, WL, {})
		local j1 = binary(WL, "add", j, one, number, "next_j")
		jump(WL, W, { j1 })
		call(P, observe, { c300 }, "q")
		jump(P, J)
		call(J, observe, { hundred }, "o")
		local done = binary(J, "less", n, i1, boolean, "done")
		if X then
			branch(J, done, X, {}, L, {})
			call(X, observe, { c500 }, "x")
			jump(X, END)
			returns(END, { marker })
		else
			branch(J, done, XR, {}, L, {})
			returns(XR, { marker })
		end
		jump(L, H, { i1 })
		returns(RET, { i1 })
	else
		error("unknown shape " .. tostring(shape))
	end

	builder:finalizeFunction(worker)
	return worker
end

local exports = {}
for _, shape in {
	"final_block_continue",
	"continue_after_final_loop",
	"continue_after_final_infinite_loop",
	"empty_arm_continue",
	"empty_arm_continue_owned_escape",
	"empty_arm_nonlocal_continue",
	"boundary_body_escape_continue",
	"boundary_body_escape_continue_exit",
	"boundary_body_escape_continue_wrapped",
	"boundary_arm_escape_continue",
	"boundary_arm_escape_continue_else",
	"boundary_arm_escape_continue_exit",
} do
	local worker = addWorker(shape)
	local _, exported = builder:addInstruction(chunkBlock, LifterIR.Operation.functionRef(worker), { { type = functionValue, name_hint = "exported_worker" } }, { effects = pure, evidence = evidence })
	table.insert(exports, exported[1])
end
builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues(exports))
builder:finalizeFunction(chunk)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
