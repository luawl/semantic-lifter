--!strict
-- Runtime oracle for simple break/exhaustion, escape-to-join, and dominating-exit workers.
local IterationBreakExitTransferRuntimeOracle = {}

local function countMatches(source: string, pattern: string): number
	return select(2, string.gsub(source, pattern, ""))
end

local function summary(name: string, rows: number, mismatches: number, first: string?): string
	local result = `{name} rows={rows} mismatches={mismatches}`
	if mismatches > 0 and first ~= nil then
		result ..= ` first: {first}`
	end
	return result
end

local function checkBreakWorker(name: string, kind: string, worker: any): string
	local rows = 0
	local mismatches = 0
	local first: string? = nil
	local function iterator(state: { number }, control: number): number?
		local nextControl = control + 1
		if nextControl > #state then
			return nil
		end
		return nextControl
	end

	for n = 0, 5 do
		for target = 0, n do
			local function pick(index: number): boolean
				return index == target
			end
			local expected = if target == 0 then "marker" else target
			local ok, actual = pcall(function()
				if kind == "numeric" then
					return worker(1, n, 1, "marker", pick)
				elseif kind == "generic" then
					local items: { number } = {}
					for k = 1, n do
						items[k] = k * 10
					end
					return worker(iterator, items, 0, "marker", pick)
				end
				return worker(0, n, 1, "marker", pick)
			end)
			rows += 1
			if not ok or actual ~= expected then
				mismatches += 1
				if first == nil then
					first = `{kind} break exit transfer lost the break value (n={n} target={target} got={tostring(actual)})`
				end
			end
		end
	end
	return summary(name, rows, mismatches, first)
end

local function checkBreakShape(source: string)
	if string.find(source, "__lifter_pc", 1, true) ~= nil then
		return
	end
	assert(countMatches(source, "for%s+[%a_][%w_]*%s*=") == 1, "break-transfer fixture lost its native numeric loop")
	assert(countMatches(source, "for%s+[%a_][%w_]*%s+in%s+") == 1, "break-transfer fixture lost its native generic loop")
	for _, name in { "numeric", "generic", "semantic" } do
		local copy = `{name}_found%s*=%s*{name}_marker`
		assert(countMatches(source, copy) == 1, `{name}_found copy is not written exactly once`)
	end
end

local function runBreakTransfer(chunk: any, source: string): (...any) -> any
	local numericWorker, genericWorker, semanticWorker = chunk()
	assert(type(numericWorker) == "function", "numeric break exit-transfer worker changed category")
	assert(type(genericWorker) == "function", "generic break exit-transfer worker changed category")
	assert(type(semanticWorker) == "function", "semantic break exit-transfer worker changed category")

	local checks = {
		checkBreakWorker("numeric", "numeric", numericWorker),
		checkBreakWorker("generic", "generic", genericWorker),
		checkBreakWorker("semantic", "semantic", semanticWorker),
	}
	checkBreakShape(source)
	assert(
		checks[1] == "numeric rows=21 mismatches=0" and checks[2] == "generic rows=21 mismatches=0" and checks[3] == "semantic rows=21 mismatches=0",
		table.concat(checks, " | ")
	)
	return numericWorker
end

local function referenceJoin(n: number, rounds: number, gate: number, pick: (number, number) -> boolean): (number, number)
	local acc, round = 0, 0
	while round < rounds do
		local nextRound = round + 1
		local bumped = acc + 100
		local toJoin = true
		if round < gate then
			toJoin = false
			for index = 1, n do
				if pick(index, acc) then
					toJoin = true
					break
				end
			end
			if not toJoin then
				acc, round = bumped, nextRound
			end
		end
		if toJoin then
			acc, round = acc + 1, nextRound
		end
	end
	return acc, round
end

local function checkJoinWorker(name: string, worker: any, generic: boolean): string
	local rows = 0
	local mismatches = 0
	local first: string? = nil
	local function iterator(state: { number }, control: number): number?
		local nextControl = control + 1
		if nextControl > #state then
			return nil
		end
		return nextControl
	end

	for n = 0, 3 do
		for rounds = 0, 3 do
			for gate = 0, 3 do
				for target = 0, n do
					local function expectedPick(index: number, seen: number): boolean
						return index == target
					end
					local referenceLog: { string } = {}
					local expectedValue, expectedRound = referenceJoin(n, rounds, gate, function(index, seen)
						table.insert(referenceLog, `{index}:{seen}`)
						return expectedPick(index, seen)
					end)
					local expectedText = `{expectedValue}/{expectedRound}`
					local expectedLog = table.concat(referenceLog, ",")

					local ok, actualValue, actualRound, actualLog = pcall(function()
						local candidateLog: { string } = {}
						local function pick(index: number, seen: number): boolean
							table.insert(candidateLog, `{index}:{seen}`)
							return index == target
						end
						local value, finalRound
						if generic then
							local items: { number } = {}
							for index = 1, n do
								items[index] = index
							end
							value, finalRound = worker(iterator, items, 0, rounds, gate, pick)
						else
							value, finalRound = worker(n, rounds, gate, pick)
						end
						return value, finalRound, table.concat(candidateLog, ",")
					end)
					rows += 1
					local actualText = if ok then `{tostring(actualValue)}/{tostring(actualRound)}` else `ERROR {tostring(actualValue)}`
					local actualLogText = if ok then tostring(actualLog) else ""
					if not ok or actualText ~= expectedText or actualLogText ~= expectedLog then
						mismatches += 1
						if first == nil then
							first = `MISMATCH n={n} rounds={rounds} gate={gate} target={target} reference={expectedText} [{expectedLog}] candidate={actualText} [{actualLogText}]`
						end
					end
				end
			end
		end
	end
	return summary(name, rows, mismatches, first)
end

local function checkJoinShape(source: string)
	if string.find(source, "__lifter_pc", 1, true) ~= nil then
		return
	end
	assert(countMatches(source, "for%s+[%a_][%w_]*%s*=") == 1, "escape-to-join fixture lost its native numeric loop")
	assert(countMatches(source, "for%s+[%a_][%w_]*%s+in%s+") == 1, "escape-to-join fixture lost its native generic loop")
end

local function runEscapeJoin(chunk: any, source: string): (...any) -> any
	local numericWorker, genericWorker, semanticWorker = chunk()
	assert(type(numericWorker) == "function", "numeric escape-to-join worker changed category")
	assert(type(genericWorker) == "function", "generic escape-to-join worker changed category")
	assert(type(semanticWorker) == "function", "semantic escape-to-join worker changed category")
	local checks = {
		checkJoinWorker("numeric", numericWorker, false),
		checkJoinWorker("generic", genericWorker, true),
		checkJoinWorker("semantic", semanticWorker, false),
	}
	checkJoinShape(source)
	assert(
		checks[1] == "numeric rows=160 mismatches=0" and checks[2] == "generic rows=160 mismatches=0" and checks[3] == "semantic rows=160 mismatches=0",
		table.concat(checks, " | ")
	)
	return numericWorker
end

local function referenceDominating(n: number, rounds: number, pick: (number, number) -> boolean): (number, string)
	local acc, round = 0, 0
	local log: { string } = {}
	while round < rounds do
		local nextRound = round + 1
		local bumped = acc + 100
		local broke = false
		for index = 1, n do
			if pick(index, acc) then
				acc = index
				broke = true
				break
			end
		end
		if not broke then
			acc = bumped
		end
		round = nextRound
	end
	return acc, table.concat(log, ",")
end

local function checkDominatingWorker(name: string, worker: any): string
	local rows = 0
	local mismatches = 0
	local first: string? = nil
	for n = 0, 3 do
		for rounds = 0, 3 do
			for target = 0, n do
				local expectedLog: { string } = {}
				local expectedValue = referenceDominating(n, rounds, function(index, seen)
					table.insert(expectedLog, `{index}:{seen}`)
					return index == target and seen ~= target
				end)
				local expectedText = tostring(expectedValue)
				local expectedLogText = table.concat(expectedLog, ",")
				local ok, actualValue, actualLog = pcall(function()
					local candidateLog: { string } = {}
					local value = worker(n, rounds, function(index: number, seen: number): boolean
						table.insert(candidateLog, `{index}:{seen}`)
						return index == target and seen ~= target
					end)
					return value, table.concat(candidateLog, ",")
				end)
				rows += 1
				local actualText = if ok then tostring(actualValue) else `ERROR {tostring(actualValue)}`
				local actualLogText = if ok then tostring(actualLog) else ""
				if not ok or actualText ~= expectedText or actualLogText ~= expectedLogText then
					mismatches += 1
					if first == nil then
						first = `MISMATCH n={n} rounds={rounds} target={target} reference={expectedText} [{expectedLogText}] candidate={actualText} [{actualLogText}]`
					end
				end
			end
		end
	end
	return summary(name, rows, mismatches, first)
end

local function checkDominatingShape(source: string)
	if string.find(source, "__lifter_pc", 1, true) ~= nil then
		return
	end
	assert(countMatches(source, "for%s+[%a_][%w_]*%s*=") == 1, "dominating-exit fixture lost its native numeric loop")
end

local function runDominatingExit(chunk: any, source: string): (...any) -> any
	local numericWorker, semanticWorker = chunk()
	assert(type(numericWorker) == "function", "numeric dominating-exit worker changed category")
	assert(type(semanticWorker) == "function", "semantic dominating-exit worker changed category")
	local checks = {
		checkDominatingWorker("numeric", numericWorker),
		checkDominatingWorker("semantic", semanticWorker),
	}
	checkDominatingShape(source)
	assert(
		checks[1] == "numeric rows=40 mismatches=0" and checks[2] == "semantic rows=40 mismatches=0",
		table.concat(checks, " | ")
	)
	return numericWorker
end

function IterationBreakExitTransferRuntimeOracle.run(chunk: any, source: string, caseName: string): (...any) -> any
	if caseName == "iteration-break-exit-transfer" then
		return runBreakTransfer(chunk, source)
	elseif caseName == "iteration-escape-join-exit" then
		return runEscapeJoin(chunk, source)
	elseif caseName == "iteration-dominating-break-exit" then
		return runDominatingExit(chunk, source)
	end
	error(`unknown conformance case {caseName}`)
end

return IterationBreakExitTransferRuntimeOracle
