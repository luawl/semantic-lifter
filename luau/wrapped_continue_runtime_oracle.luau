--!strict
-- Runtime oracle for loops whose structured text would write a lexical continue where the innermost Luau loop
-- statement is not the loop it continues (wrapped-continue). Each worker is worker(n, m, marker, f, g, observe) and
-- runs over 15360 rows (n 0..4, m 0..2, 32 masks for f, 4 for g and 8 for the values observe returns) against a
-- reference written in plain Luau: the result and the order of the callback calls must match. A run that makes more
-- than 400 callback calls stops with the error "call cap", so a loop that never ends fails its row instead of hanging.
-- A passing case prints nothing. A failing case prints one line per failing worker, `<case> <worker> rows=<R>
-- mismatches=<M> first: <row>`, and fails one assertion that counts the failed workers.
local WrappedContinueRuntimeOracle = {}

local MARKER = "marker"
local CALL_CAP = 400
local SHOWN_CALLS = 12

type Reference = (n: number, m: number, marker: any, f: any, g: any, observe: any) -> any

local function bit(mask: number, index: number): boolean
	return bit32.band(mask, bit32.lshift(1, index)) ~= 0
end

-- An error's text without its chunk location (`<chunk>:<line>: `), so a report does not depend on where the
-- generated file lies.
local function errorText(value: any): string
	return (string.gsub(tostring(value), "^.-:%d+: ", ""))
end

local function runRow(worker: any, n: number, m: number, maskF: number, maskG: number, maskO: number): (string, { string })
	local log: { string } = {}
	local calls = 0
	local function tick(entry: string)
		calls += 1
		if calls > CALL_CAP then
			error("call cap", 0)
		end
		table.insert(log, entry)
	end
	local function f(a: number, b: number?): boolean
		tick(string.format("f(%s,%s)", tostring(a), tostring(b)))
		if a > 5 then
			return false
		end
		return bit(maskF, (a + (b or 0)) % 5)
	end
	local function g(a: number): boolean
		tick(string.format("g(%s)", tostring(a)))
		return bit(maskG, a % 2)
	end
	local function observe(value: number): boolean
		tick(string.format("o(%s)", tostring(value)))
		return bit(maskO, value % 3)
	end
	local ok, result = pcall(worker, n, m, MARKER, f, g, observe)
	return (if ok then "ok:" .. tostring(result) else "err:" .. errorText(result)), log
end

local function shown(log: { string }): string
	if #log <= SHOWN_CALLS then
		return table.concat(log, " ")
	end
	return table.concat(log, " ", 1, SHOWN_CALLS) .. ` ... ({#log} calls)`
end

local function sameLog(left: { string }, right: { string }): boolean
	if #left ~= #right then
		return false
	end
	for index = 1, #left do
		if left[index] ~= right[index] then
			return false
		end
	end
	return true
end

-- Returns nil when every row matches, else the worker's report line.
local function compareRows(caseName: string, label: string, worker: any, reference: Reference): string?
	local rows, mismatches = 0, 0
	local first: string? = nil
	for n = 0, 4 do
		for m = 0, 2 do
			for maskF = 0, 31 do
				for maskG = 0, 3 do
					for maskO = 0, 7 do
						local expectedResult, expectedLog = runRow(reference, n, m, maskF, maskG, maskO)
						local actualResult, actualLog = runRow(worker, n, m, maskF, maskG, maskO)
						rows += 1
						if expectedResult ~= actualResult or not sameLog(expectedLog, actualLog) then
							mismatches += 1
							if first == nil then
								first = string.format(
									"n=%d m=%d maskF=%d maskG=%d maskO=%d expected=%s [%s] got=%s [%s]",
									n,
									m,
									maskF,
									maskG,
									maskO,
									expectedResult,
									shown(expectedLog),
									actualResult,
									shown(actualLog)
								)
							end
						end
					end
				end
			end
		end
	end
	if mismatches == 0 then
		return nil
	end
	return `{caseName} {label} rows={rows} mismatches={mismatches} first: {first}`
end

-- The inner loop of several shapes: j = 1 while not (m < j) do if g(j) then <leave to the join> end
-- [observe(j)] j += 1 end. Returns true when the loop left to the join.
local function innerLoopEscapes(m: number, g: any, observe: any, observeEach: boolean): boolean
	local j = 1
	while not (m < j) do
		if g(j) then
			return true
		end
		if observeEach then
			observe(j)
		end
		j += 1
	end
	return false
end

local function finalBlockContinue(n: number, _m: number, marker: any, f: any, g: any, observe: any): any
	local i = 0
	while true do
		local i1 = i + 1
		if f(i1) then
			if f(i1, 1) then
				observe(300)
				i = i1
				continue
			end
			if g(i1) then
				if observe(i1) then
					observe(250)
					i = i1
					continue
				end
			else
				return i1
			end
		end
		observe(100)
		if n < i1 then
			return marker
		end
		i = i1
	end
end

local function continueAfterFinalLoop(n: number, m: number, marker: any, f: any, g: any, observe: any): any
	local i = 0
	while true do
		local i1 = i + 1
		if f(i1) and not innerLoopEscapes(m, g, observe, true) then
			i = i1
			continue
		end
		observe(100)
		if n < i1 then
			return marker
		end
		i = i1
	end
end

local function continueAfterFinalInfiniteLoop(n: number, m: number, marker: any, f: any, g: any, observe: any): any
	local i = 0
	while true do
		local i1 = i + 1
		if f(i1) and not innerLoopEscapes(m, g, observe, false) then
			local k = 1
			while true do
				observe(k)
				local k1 = k + 1
				if m < k1 then
					break
				end
				observe(250)
				k = k1
			end
			i = i1
			continue
		end
		observe(100)
		if n < i1 then
			return marker
		end
		i = i1
	end
end

local function emptyArmContinue(n: number, _m: number, marker: any, f: any, g: any, observe: any): any
	local i = 0
	while true do
		local i1 = i + 1
		if f(i1) then
			if f(i1, 1) then
				i = i1
				continue
			end
			if g(i1) then
				if observe(i1) then
					observe(250)
					i = i1
					continue
				end
			else
				return i1
			end
		end
		observe(100)
		if n < i1 then
			return marker
		end
		i = i1
	end
end

local function emptyArmContinueOwnedEscape(n: number, m: number, marker: any, f: any, g: any, observe: any): any
	local i = 0
	while true do
		local i1 = i + 1
		if f(i1) and not innerLoopEscapes(m, g, observe, false) and f(i1, 1) then
			i = i1
			continue
		end
		observe(100)
		if n < i1 then
			return marker
		end
		i = i1
	end
end

local function emptyArmNonlocalContinue(n: number, _m: number, marker: any, f: any, g: any, observe: any): any
	local i = 0
	while true do
		local i1 = i + 1
		if f(i1) then
			if g(i1) then
				if observe(i1) then
					i = i1
					continue
				end
			else
				return i1
			end
		end
		observe(100)
		if n < i1 then
			return marker
		end
		i = i1
	end
end

-- if g(i1) then observe(i1) <the inner loop> [observe(300) unless it left] else return i1 end, as one step: returns
-- the value to return, or nil to go on to the join.
local function boundaryBody(i1: number, m: number, g: any, observe: any): number?
	if g(i1) then
		observe(i1)
		if not innerLoopEscapes(m, g, observe, false) then
			observe(300)
		end
		return nil
	end
	return i1
end

local function boundaryBodyEscapeContinue(n: number, m: number, marker: any, f: any, g: any, observe: any): any
	local i = 0
	while true do
		local i1 = i + 1
		if f(i1) then
			local returned = boundaryBody(i1, m, g, observe)
			if returned ~= nil then
				return returned
			end
		end
		observe(100)
		if n < i1 then
			return marker
		end
		i = i1
	end
end

local function boundaryBodyEscapeContinueExit(n: number, m: number, marker: any, f: any, g: any, observe: any): any
	local i = 0
	while true do
		local i1 = i + 1
		if f(i1) then
			local returned = boundaryBody(i1, m, g, observe)
			if returned ~= nil then
				return returned
			end
		end
		observe(100)
		if n < i1 then
			break
		end
		i = i1
	end
	observe(400)
	return marker
end

local function boundaryBodyEscapeContinueWrapped(n: number, m: number, marker: any, f: any, g: any, observe: any): any
	local i = 0
	while true do
		local i1 = i + 1
		if f(i1) then
			if f(i1, 1) then
				local returned = boundaryBody(i1, m, g, observe)
				if returned ~= nil then
					return returned
				end
			end
			if g(i1, 1) then
				if observe(250) then
					observe(300)
					i = i1
					continue
				end
			else
				return marker
			end
		end
		observe(100)
		if n < i1 then
			return marker
		end
		i = i1
	end
end

-- if g(i1) then if observe(i1) then <the inner loop> [observe(300) unless it left] [else observe(400)] end else
-- return i1 end, as one step: returns the value to return, or nil to go on to the join.
local function boundaryArm(i1: number, m: number, g: any, observe: any, withElse: boolean): number?
	if g(i1) then
		if observe(i1) then
			if not innerLoopEscapes(m, g, observe, false) then
				observe(300)
			end
		elseif withElse then
			observe(400)
		end
		return nil
	end
	return i1
end

local function boundaryArmEscapeContinueOf(withElse: boolean): Reference
	return function(n: number, m: number, marker: any, f: any, g: any, observe: any): any
		local i = 0
		while true do
			local i1 = i + 1
			if f(i1) then
				local returned = boundaryArm(i1, m, g, observe, withElse)
				if returned ~= nil then
					return returned
				end
			end
			observe(100)
			if n < i1 then
				return marker
			end
			i = i1
		end
	end
end

local function boundaryArmEscapeContinueExit(n: number, m: number, marker: any, f: any, g: any, observe: any): any
	local i = 0
	while true do
		local i1 = i + 1
		if f(i1) then
			local returned = boundaryArm(i1, m, g, observe, true)
			if returned ~= nil then
				return returned
			end
		end
		observe(100)
		if n < i1 then
			break
		end
		i = i1
	end
	observe(500)
	return marker
end

-- The chunk's twelve workers, in the builder's order, each with its reference.
local WORKERS: { { name: string, reference: Reference } } = {
	{ name = "final_block_continue", reference = finalBlockContinue },
	{ name = "continue_after_final_loop", reference = continueAfterFinalLoop },
	{ name = "continue_after_final_infinite_loop", reference = continueAfterFinalInfiniteLoop },
	{ name = "empty_arm_continue", reference = emptyArmContinue },
	{ name = "empty_arm_continue_owned_escape", reference = emptyArmContinueOwnedEscape },
	{ name = "empty_arm_nonlocal_continue", reference = emptyArmNonlocalContinue },
	{ name = "boundary_body_escape_continue", reference = boundaryBodyEscapeContinue },
	{ name = "boundary_body_escape_continue_exit", reference = boundaryBodyEscapeContinueExit },
	{ name = "boundary_body_escape_continue_wrapped", reference = boundaryBodyEscapeContinueWrapped },
	{ name = "boundary_arm_escape_continue", reference = boundaryArmEscapeContinueOf(false) },
	{ name = "boundary_arm_escape_continue_else", reference = boundaryArmEscapeContinueOf(true) },
	{ name = "boundary_arm_escape_continue_exit", reference = boundaryArmEscapeContinueExit },
}

function WrappedContinueRuntimeOracle.run(chunk: any, _source: string, caseName: string): any
	local workers = table.pack(chunk())
	assert(workers.n == #WORKERS, `{caseName}: the chunk returned {workers.n} workers, expected {#WORKERS}`)
	local lines: { string } = {}
	for index, entry in WORKERS do
		assert(type(workers[index]) == "function", `{caseName}: worker {entry.name} is not a function`)
		local line = compareRows(caseName, entry.name, workers[index], entry.reference)
		if line ~= nil then
			table.insert(lines, line)
		end
	end
	if #lines > 0 then
		print(table.concat(lines, "\n"))
	end
	assert(#lines == 0, `{caseName}: {#lines} of {#WORKERS} workers failed`)
	return workers[1]
end

return table.freeze(WrappedContinueRuntimeOracle)
