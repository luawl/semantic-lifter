--!strict
--!nolint DeprecatedApi
-- Runtime oracle for native loops whose header is entered from an inner loop, a loop control, a loop-boundary
-- arm or an earlier loop (iteration-header-entry), for the explicit continues of a native loop that guards its
-- exit copy with a completion local (iteration-continue-completion), and for the continue a wrapped
-- loop-boundary body region ends with (iteration-boundary-body-continue). Every worker runs over a grid of rows
-- against a reference written by hand: the result and the order of its callback calls must match. The first and
-- the third case run the chunk under an environment that records, per worker, every global write and every
-- read of a name the real environment does not hold (getfenv and setfenv install it), and both must stay empty.
-- In the structured text (no __lifter_pc) the native loops keep their form, every native loop guards its exit
-- copy, and every continue inside a guarded loop is preceded by the loop's completion write.
-- A passing case prints nothing. A failing case prints one line per worker, `<case> <worker> rows=<R>
-- mismatches=<M>` with the environment counts where they apply and the first differing row, then the line
-- `<case> pins …`, and fails one assertion that counts the failed workers.
local IterationHeaderEntryRuntimeOracle = {}

local MARKER = "marker"

-- An error's text without its chunk location (`<chunk>:<line>: `), so a report does not depend on where the
-- generated file lies.
local function errorText(value: any): string
	return "error " .. (string.gsub(tostring(value), "^.-:%d+: ", ""))
end

type Bucket = {
	writes: number,
	writeNames: { string },
	reads: number,
	readNames: { string },
	seen: { [string]: boolean },
}

type Recorder = {
	env: any,
	active: string,
	buckets: { [string]: Bucket },
}

type Report = {
	caseName: string,
	lines: { string },
	failed: number,
	total: number,
}

local function newRecorder(): Recorder
	local real: any = getfenv(0)
	local written: { [string]: any } = {}
	local recorder: Recorder = { env = nil, active = "chunk", buckets = {} }
	local function bucket(): Bucket
		local found = recorder.buckets[recorder.active]
		if found == nil then
			found = { writes = 0, writeNames = {}, reads = 0, readNames = {}, seen = {} }
			recorder.buckets[recorder.active] = found
		end
		return found
	end
	recorder.env = setmetatable({}, {
		__index = function(_, key: any): any
			local name = tostring(key)
			if written[name] ~= nil then
				return written[name]
			end
			local value = real[key]
			if value == nil then
				local current = bucket()
				current.reads += 1
				if not current.seen["read " .. name] then
					current.seen["read " .. name] = true
					table.insert(current.readNames, name)
				end
			end
			return value
		end,
		__newindex = function(_, key: any, value: any)
			local name = tostring(key)
			local current = bucket()
			current.writes += 1
			if not current.seen["write " .. name] then
				current.seen["write " .. name] = true
				table.insert(current.writeNames, name)
			end
			written[name] = value
		end,
	})
	return recorder
end

local function environmentText(recorder: Recorder, label: string): string
	local found = recorder.buckets[label]
	if found == nil then
		return " global_writes=0[] unknown_reads=0[]"
	end
	return ` global_writes={found.writes}[{table.concat(found.writeNames, ",")}] unknown_reads={found.reads}[{table.concat(found.readNames, ",")}]`
end

local function environmentClean(recorder: Recorder, label: string): boolean
	local found = recorder.buckets[label]
	return found == nil or (found.writes == 0 and found.reads == 0)
end

local function bit(mask: number, index: number): boolean
	return bit32.band(mask, bit32.lshift(1, index)) ~= 0
end

-- The grid of the first two cases: n 0..4, m 0..2, 32 masks for f, 4 for g and 2 for the value observe returns
-- (3840 rows). Each shape's reference is the loop the worker's IR spells, run over index = 1..n.
local function gridReference(shape: string, n: number, m: number, f: any, g: any, observe: any): any
	if shape == "pre_while_boundary_entry" then
		local j = 1
		while not (m < j) do
			if f(j) then
				break
			end
			observe(j)
			j += 1
		end
	end
	for index = 1, n do
		if shape == "arm_inner_loop_exits_to_header" then
			if f(index) then
				local j = 1
				while not (m < j) do
					observe(j)
					j += 1
				end
			else
				observe(index)
			end
		elseif shape == "inner_latch_exit" then
			local j = 1
			while true do
				observe(j)
				local nextJ = j + 1
				if m < nextJ then
					break
				end
				j = nextJ
			end
		elseif shape == "nested_while_continue" then
			local j = 1
			local escaped = false
			while not (m < j) do
				if f(index, j) then
					escaped = true
					break
				end
				j += 1
			end
			if not escaped then
				observe(index)
			end
		elseif shape == "pre_while_boundary_entry" then
			observe(index)
		elseif shape == "diamond_continue" or shape == "latch_diamond" then
			if not (f(index) and g(index)) then
				observe(index)
			end
		elseif shape == "nested_arm_boundary" or shape == "nested_arm_boundary_work" then
			local continued = false
			if f(index) and not g(index) then
				if observe(index) then
					if shape == "nested_arm_boundary_work" then
						observe(1)
					end
					continued = true
				else
					return index
				end
			end
			if not continued then
				observe(index)
			end
		else
			error(`no reference for {shape}`)
		end
	end
	return MARKER
end

local function gridInvoke(worker: any, kind: string, n: number, m: number, f: any, g: any, observe: any): any
	if kind == "numeric" then
		return worker(1, n, 1, MARKER, m, f, g, observe)
	elseif kind == "semantic" then
		return worker(0, n, 1, MARKER, m, f, g, observe)
	end
	local list: { number } = {}
	for index = 1, n do
		list[index] = index
	end
	local iterator, state, control = ipairs(list)
	return worker(iterator, state, control, MARKER, m, f, g, observe)
end

local function checkGridWorker(recorder: Recorder?, shape: string, kind: string, worker: any): (string, boolean)
	local label = `{shape}_{kind}`
	local rows = 0
	local mismatches = 0
	local first: string? = nil
	if recorder ~= nil then
		recorder.active = label
	end
	local twoArgument = shape == "nested_while_continue"
	for n = 0, 4 do
		for m = 0, 2 do
			for mask = 0, 31 do
				for maskG = 0, 3 do
					for maskO = 0, 1 do
						local function f(index: number, j: number?): boolean
							if twoArgument then
								return bit(mask, (index - 1) % 5) and j == 1 + (index % 2)
							end
							return bit(mask, (index - 1) % 5)
						end
						local function g(index: number): boolean
							return bit(maskG, (index - 1) % 2)
						end
						local expectedLog: { number } = {}
						local actualLog: { number } = {}
						local expected = gridReference(shape, n, m, f, g, function(value: number): boolean
							table.insert(expectedLog, value)
							return (value + maskO) % 2 == 0
						end)
						local ok, actual = pcall(gridInvoke, worker, kind, n, m, f, g, function(value: number): boolean
							table.insert(actualLog, value)
							return (value + maskO) % 2 == 0
						end)
						rows += 1
						local same = ok and actual == expected and #actualLog == #expectedLog
						if same then
							for index = 1, #expectedLog do
								if expectedLog[index] ~= actualLog[index] then
									same = false
									break
								end
							end
						end
						if not same then
							mismatches += 1
							if first == nil then
								first = `n={n} m={m} mask={mask} maskG={maskG} maskO={maskO} expected={tostring(expected)} got={if ok then tostring(actual) else errorText(actual)} log={#expectedLog}/{#actualLog}`
							end
						end
					end
				end
			end
		end
	end
	if recorder ~= nil then
		recorder.active = "chunk"
	end
	local line = `{label} rows={rows} mismatches={mismatches}`
	local clean = mismatches == 0
	if recorder ~= nil then
		line ..= environmentText(recorder, label)
		clean = clean and environmentClean(recorder, label)
	end
	if mismatches > 0 and first ~= nil then
		line ..= ` first: {first}`
	end
	return line, clean
end

-- The rows of the third case: 4000 rows drawn from a Park-Miller generator; the log holds every f, g, observe and
-- h call with its arguments.
local H_SLOTS: { [number]: number } = { [0] = 0, [1] = 1, [2] = 2, [11] = 3, [12] = 4, [21] = 5, [22] = 6 }

local function hSlot(a: number, b: number): number
	local slot = H_SLOTS[b]
	if slot == nil or a < 1 or a > 3 then
		return 30
	end
	return (a - 1) * 7 + slot
end

local function innerLoop(index: number, m: number, offset: number, observe: any, h: any): boolean
	local j = 1
	while not (m < j) do
		observe(j)
		if h(index, offset + j) then
			return true
		end
		j += 1
	end
	return false
end

local function wrappedArmsReference(n: number, m: number, f: any, g: any, observe: any, h: any): any
	for index = 1, n do
		if f(index) then
			if not g(index) then
				if not observe(index) then
					return index
				end
				observe(1)
				if innerLoop(index, m, 0, observe, h) then
					continue
				end
				if h(index, 0) then
					innerLoop(index, m, 20, observe, h)
				else
					innerLoop(index, m, 10, observe, h)
				end
				continue
			end
		end
		observe(index)
	end
	return MARKER
end

local function checkWrappedArmsWorker(recorder: Recorder, kind: string, worker: any): (string, boolean)
	local label = `wrapped_body_arms_{kind}`
	local seed = 20261021
	local function random(limit: number): number
		seed = (seed * 16807) % 2147483647
		return seed % limit
	end
	local function iterator(state: { number }, control: number): number?
		local nextControl = control + 1
		if nextControl > #state then
			return nil
		end
		return nextControl
	end
	local rows = 0
	local mismatches = 0
	local first: string? = nil
	recorder.active = label
	for _ = 1, 4000 do
		local n = random(4)
		local m = random(3)
		local fMask, gMask, oMask, hMask = random(16), random(16), random(64), random(2097152)
		local function run(candidate: boolean): string
			local log: { string } = {}
			local function f(index: number): boolean
				table.insert(log, `f{index}`)
				return bit(fMask, index)
			end
			local function g(index: number): boolean
				table.insert(log, `g{index}`)
				return bit(gMask, index)
			end
			local function observe(value: number): boolean
				table.insert(log, `o{value}`)
				return bit(oMask, value)
			end
			local function h(a: number, b: number): boolean
				table.insert(log, `h{a}.{b}`)
				return bit(hMask, hSlot(a, b))
			end
			local ok, result = pcall(function(): any
				if not candidate then
					return wrappedArmsReference(n, m, f, g, observe, h)
				elseif kind == "generic" then
					local items: { number } = {}
					for k = 1, n do
						items[k] = k * 10
					end
					return worker(iterator, items, 0, MARKER, m, f, g, observe, h)
				end
				return worker(1, n, 1, MARKER, m, f, g, observe, h)
			end)
			return `{if ok then tostring(result) else errorText(result)} [{table.concat(log, ",")}]`
		end
		local expected = run(false)
		local actual = run(true)
		rows += 1
		if expected ~= actual then
			mismatches += 1
			if first == nil then
				first = `n={n} m={m} f={fMask} g={gMask} o={oMask} h={hMask} expected={expected} got={actual}`
			end
		end
	end
	recorder.active = "chunk"
	local line = `{label} rows={rows} mismatches={mismatches}{environmentText(recorder, label)}`
	if mismatches > 0 and first ~= nil then
		line ..= ` first: {first}`
	end
	return line, mismatches == 0 and environmentClean(recorder, label)
end

local function countMatches(source: string, pattern: string): number
	return select(2, string.gsub(source, pattern, ""))
end

-- Every native loop that guards its exit copy declares `local <flag> = true` on the line before its `for`; inside
-- the loop (up to the `end` at the `for`'s indent), every `continue` is preceded by `<flag> = true`, directly or
-- through the `do` line of a `do continue end`.
local function guardedContinues(source: string): (number, number, number)
	local lines = string.split(source, "\n")
	local guarded, continues, written = 0, 0, 0
	local index = 1
	while index <= #lines do
		local indent, flag = string.match(lines[index], "^(%s*)local (__lifter_native_iteration_complete_%d+) = true$")
		if indent ~= nil and flag ~= nil and index < #lines and string.match(lines[index + 1], "^" .. indent .. "for .* do$") ~= nil then
			guarded += 1
			local close = indent .. "end"
			local cursor = index + 2
			while cursor <= #lines and lines[cursor] ~= close do
				if string.match(lines[cursor], "^%s*continue$") ~= nil then
					continues += 1
					local previous = cursor - 1
					if string.match(lines[previous], "^%s*do$") ~= nil then
						previous -= 1
					end
					if string.match(lines[previous], "^%s*" .. flag .. " = true$") ~= nil then
						written += 1
					end
				end
				cursor += 1
			end
			index = cursor
		end
		index += 1
	end
	return guarded, continues, written
end

local function checkPins(source: string, numericLoops: number, genericLoops: number, guardedContinueCount: number): (string, boolean)
	if string.find(source, "__lifter_pc", 1, true) ~= nil then
		return "pins skipped (dispatcher form)", true
	end
	local numeric = countMatches(source, "for%s+[%a_][%w_]*%s*=")
	local generic = countMatches(source, "for%s+[%a_][%w_]*%s+in%s+")
	local guarded, continues, written = guardedContinues(source)
	local text = `pins numeric_for={numeric}/{numericLoops} generic_for={generic}/{genericLoops} guarded_for={guarded}/{numericLoops + genericLoops} continue={continues}/{guardedContinueCount} written={written}/{guardedContinueCount}`
	local pass = numeric == numericLoops
		and generic == genericLoops
		and guarded == numericLoops + genericLoops
		and continues == guardedContinueCount
		and written == guardedContinueCount
	return text, pass
end

local function collectWorkers(chunk: any, count: number, caseName: string): { any }
	local workers = table.pack(chunk())
	assert(workers.n == count, `{caseName} fixture returned {workers.n} workers, expected {count}`)
	for index = 1, count do
		assert(type(workers[index]) == "function", `{caseName} worker {index} changed category`)
	end
	return workers
end

local function addLine(report: Report, line: string, clean: boolean)
	report.total += 1
	if not clean then
		report.failed += 1
	end
	table.insert(report.lines, line)
end

local function addChunkLine(report: Report, recorder: Recorder)
	if not environmentClean(recorder, "chunk") then
		addLine(report, `chunk{environmentText(recorder, "chunk")}`, false)
	end
end

local function finish(report: Report, pins: string, pinsPass: boolean)
	if report.failed == 0 and pinsPass then
		return
	end
	for _, line in report.lines do
		print(`{report.caseName} {line}`)
	end
	print(`{report.caseName} {pins}`)
	assert(false, `{report.caseName}: {report.failed} of {report.total} workers failed, pins {if pinsPass then "held" else "failed"}`)
end

local function runHeaderEntry(chunk: any, source: string): any
	local report: Report = { caseName = "iteration-header-entry", lines = {}, failed = 0, total = 0 }
	local recorder = newRecorder()
	setfenv(chunk, recorder.env)
	local workers = collectWorkers(chunk, 12, report.caseName)
	addChunkLine(report, recorder)
	local index = 0
	for _, shape in { "arm_inner_loop_exits_to_header", "inner_latch_exit", "nested_while_continue", "pre_while_boundary_entry" } do
		for _, kind in { "numeric", "generic", "semantic" } do
			index += 1
			local line, clean = checkGridWorker(recorder, shape, kind, workers[index])
			addLine(report, line, clean)
		end
	end
	local pins, pinsPass = checkPins(source, 4, 4, 6)
	finish(report, pins, pinsPass)
	return workers[1]
end

local function runContinueCompletion(chunk: any, source: string): any
	local report: Report = { caseName = "iteration-continue-completion", lines = {}, failed = 0, total = 0 }
	local workers = collectWorkers(chunk, 8, report.caseName)
	local index = 0
	for _, shape in { "diamond_continue", "latch_diamond", "nested_arm_boundary", "nested_arm_boundary_work" } do
		for _, kind in { "numeric", "generic" } do
			index += 1
			local line, clean = checkGridWorker(nil, shape, kind, workers[index])
			addLine(report, line, clean)
		end
	end
	local pins, pinsPass = checkPins(source, 4, 4, 10)
	finish(report, pins, pinsPass)
	return workers[1]
end

local function runBoundaryBodyContinue(chunk: any, source: string): any
	local report: Report = { caseName = "iteration-boundary-body-continue", lines = {}, failed = 0, total = 0 }
	local recorder = newRecorder()
	setfenv(chunk, recorder.env)
	local workers = collectWorkers(chunk, 3, report.caseName)
	addChunkLine(report, recorder)
	for index, kind in { "numeric", "generic", "while" } do
		local line, clean = checkWrappedArmsWorker(recorder, kind, workers[index])
		addLine(report, line, clean)
	end
	local pins, pinsPass = checkPins(source, 1, 1, 8)
	finish(report, pins, pinsPass)
	return workers[1]
end

function IterationHeaderEntryRuntimeOracle.run(chunk: any, source: string, caseName: string): any
	if caseName == "iteration-header-entry" then
		return runHeaderEntry(chunk, source)
	elseif caseName == "iteration-continue-completion" then
		return runContinueCompletion(chunk, source)
	elseif caseName == "iteration-boundary-body-continue" then
		return runBoundaryBodyContinue(chunk, source)
	end
	error(`unknown conformance case {caseName}`)
end

return IterationHeaderEntryRuntimeOracle
