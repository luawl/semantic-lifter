--!strict
--!nolint DeprecatedApi
-- Runtime oracle for loops that own their exit while an escape in their body reaches it (loop-owned-exit-flag).
-- The chunk runs under an environment in which reading an escape flag as a global, or writing any global, raises,
-- so a flag the text never declares fails the row that reaches it. Every worker runs once for each script of twelve
-- step results against a reference written by hand: the result and the order of the step labels must match. A
-- script that runs out raises, which bounds every loop. One row is also checked against its trace written out: the
-- third worker's second entry to its middle loop must not see the flag its first entry left set. The eighth worker
-- leaves its inner loop by a loop boundary's side escape, whose side arm sets the flag of the exit the middle loop
-- owns after the side region: that set must reach the flag the middle loop reads. The ninth and tenth leave an
-- inner loop that an outer loop enters again by a loop-boundary exit carried by its escape flag: a flag one entry
-- left set must not end the next entry's first pass. The eleventh leaves its side region by the exit of a loop last
-- in one of its arms, which continues the middle loop: that arm sets the middle loop's header flag after the loop,
-- and a second row is checked against its trace written out.
-- A passing case prints nothing. A failing case prints one line per failing worker, `<case> <worker> rows=<R>
-- mismatches=<M> trapped=<T>` with the first differing row, a line for each written-out row that differs, and
-- fails one assertion that counts the failed workers.
local LoopOwnedExitFlagRuntimeOracle = {}

local SCRIPT_LENGTH = 12
local PINNED_WORKER = "owned_exit_boundary_exit_reentered"
local PINNED_SCRIPT = "TTFFTTTTFFFF"
local PINNED_EXPECTED = "ok:done [H0,S,I,E,H0,S,I,B,S,R,E,H0]"
local SIDE_LOOP_WORKER = "side_escape_loop_exit_continue"
local SIDE_LOOP_SCRIPT = "FTFTTFFFFFFF"
local SIDE_LOOP_EXPECTED = "ok:done [entry,Z,H,I,B,L,W,H,I,E,Z]"

local function trapEnvironment(): any
	local real: any = getfenv(0)
	return setmetatable({}, {
		__index = function(_, key: any): any
			local name = tostring(key)
			if string.sub(name, 1, 16) == "__lifter_escape_" then
				error(`escape flag read as a global: {name}`, 0)
			end
			return real[key]
		end,
		__newindex = function(_, key: any, _value: any)
			error(`global write: {tostring(key)}`, 0)
		end,
	})
end

local function ownedExitInfinite(step: (string) -> any): any
	step("entry")
	while true do
		step("H")
		local nextPass = false
		while step("I") do
			if step("B") then
				nextPass = true
				break
			end
			step("C")
		end
		if not nextPass then
			return "exit"
		end
	end
end

local function ownedExitWhileReentered(step: (string) -> any): any
	while step("H0") do
		while not step("Q") do
			local nextPass = false
			while step("I") do
				if step("B") then
					nextPass = true
					break
				end
				step("C")
			end
			if not nextPass then
				break
			end
		end
		step("E")
	end
	return "done"
end

local function ownedExitBoundaryExitReentered(step: (string) -> any): any
	while step("H0") do
		while true do
			if not step("S") then
				if not step("R") then
					break
				end
				step("P")
			end
			local nextPass = false
			while step("I") do
				if step("B") then
					nextPass = true
					break
				end
				if not step("C") then
					break
				end
				step("Q")
			end
			if not nextPass then
				break
			end
		end
		step("E")
	end
	return "done"
end

local function ownedExitLatch(step: (string) -> any): any
	step("entry")
	repeat
		step("H")
		local toLatch = false
		while step("I") do
			if step("B") then
				toLatch = true
				break
			end
			step("C")
		end
		if not toLatch then
			return "exit"
		end
	until not step("L")
	return "exit"
end

local function sideEscapeFreeTarget(step: (string) -> any): any
	step("entry")
	while step("Z") do
		while true do
			step("H")
			local outcome: string? = nil
			while step("I") do
				if step("B") then
					if step("L") then
						outcome = "middle"
					else
						outcome = "outer"
					end
					break
				end
				step("C")
			end
			if outcome == "middle" then
				continue
			end
			if outcome == nil then
				step("E")
			end
			break
		end
	end
	return "done"
end

local function exitReentered(step: (string) -> any): any
	while step("H0") do
		while step("I") do
			if step("A") then
				if step("B") then
					step("K")
					continue
				end
			end
			if step("X") then
				break
			end
			step("C")
		end
		step("E")
	end
	return "done"
end

local function exitToInfiniteHeader(step: (string) -> any): any
	while true do
		step("H")
		while step("I") do
			if step("A") then
				if step("B") then
					step("K")
					continue
				end
			end
			if step("X") then
				break
			end
			step("C")
		end
	end
end

local function sideEscapeLoopExitContinue(step: (string) -> any): any
	step("entry")
	while step("Z") do
		while true do
			step("H")
			local outcome: string? = nil
			while step("I") do
				if step("B") then
					if step("L") then
						outcome = "outer"
					else
						while true do
							if not step("W") then
								outcome = "middle"
								break
							end
							if step("V") then
								outcome = "outer"
								break
							end
						end
					end
					break
				end
				step("C")
			end
			if outcome == "middle" then
				continue
			end
			if outcome == nil then
				step("E")
			end
			break
		end
	end
	return "done"
end

-- The native loops run index over 1, 2, 3.
local function ownedExitFor(step: (string) -> any): any
	for index = 1, 3 do
		local nextIndex = false
		while step("I") do
			if step("B") then
				nextIndex = true
				break
			end
			step("C")
		end
		if not nextIndex then
			return index
		end
	end
	return "marker"
end

local function stepInvoke(worker: any, step: (string) -> any): any
	return worker(step)
end

local function numericInvoke(worker: any, step: (string) -> any): any
	return worker(1, 3, 1, "marker", step)
end

local function genericInvoke(worker: any, step: (string) -> any): any
	local iterator, state, control = ipairs({ 1, 2, 3 })
	return worker(iterator, state, control, "marker", step)
end

local function semanticInvoke(worker: any, step: (string) -> any): any
	return worker(0, 3, 1, "marker", step)
end

type WorkerEntry = { name: string, reference: (step: (string) -> any) -> any, invoke: (worker: any, step: (string) -> any) -> any }

local WORKERS: { WorkerEntry } = {
	{ name = "owned_exit_infinite", reference = ownedExitInfinite, invoke = stepInvoke },
	{ name = "owned_exit_while_reentered", reference = ownedExitWhileReentered, invoke = stepInvoke },
	{ name = PINNED_WORKER, reference = ownedExitBoundaryExitReentered, invoke = stepInvoke },
	{ name = "owned_exit_latch", reference = ownedExitLatch, invoke = stepInvoke },
	{ name = "owned_exit_numeric_for", reference = ownedExitFor, invoke = numericInvoke },
	{ name = "owned_exit_generic_for", reference = ownedExitFor, invoke = genericInvoke },
	{ name = "owned_exit_semantic_for", reference = ownedExitFor, invoke = semanticInvoke },
	{ name = "side_escape_free_target", reference = sideEscapeFreeTarget, invoke = stepInvoke },
	{ name = "exit_reentered", reference = exitReentered, invoke = stepInvoke },
	{ name = "exit_to_infinite_header", reference = exitToInfiniteHeader, invoke = stepInvoke },
	{ name = SIDE_LOOP_WORKER, reference = sideEscapeLoopExitContinue, invoke = stepInvoke },
}

local function scriptText(bits: { boolean }): string
	local letters: { string } = {}
	for index, value in bits do
		letters[index] = if value then "T" else "F"
	end
	return table.concat(letters)
end

local function scriptBits(text: string): { boolean }
	local bits: { boolean } = {}
	for index = 1, #text do
		bits[index] = string.sub(text, index, index) == "T"
	end
	return bits
end

-- One run: `ok:<result>` or `error <text>`, then the step labels in order.
local function runScript(fn: any, invoke: (worker: any, step: (string) -> any) -> any, bits: { boolean }): (string, boolean)
	local position = 0
	local trace: { string } = {}
	local function step(label: string): boolean
		position += 1
		table.insert(trace, label)
		if position > #bits then
			error("script exhausted", 0)
		end
		return bits[position]
	end
	local ok, result = pcall(invoke, fn, step)
	local outcome = if ok then "ok:" .. tostring(result) else "error " .. tostring(result)
	local trapped = not ok
		and (string.find(tostring(result), "escape flag read as a global", 1, true) ~= nil or string.find(tostring(result), "global write", 1, true) ~= nil)
	return `{outcome} [{table.concat(trace, ",")}]`, trapped
end

local function checkWorker(entry: WorkerEntry, worker: any): (string, boolean)
	local rows = 0
	local mismatches = 0
	local trappedRows = 0
	local first: string? = nil
	for value = 0, 2 ^ SCRIPT_LENGTH - 1 do
		local bits: { boolean } = {}
		for index = 1, SCRIPT_LENGTH do
			bits[index] = bit32.extract(value, index - 1) == 1
		end
		local expected = runScript(entry.reference, stepInvoke, bits)
		local actual, trapped = runScript(worker, entry.invoke, bits)
		rows += 1
		if trapped then
			trappedRows += 1
		end
		if actual ~= expected then
			mismatches += 1
			if first == nil then
				first = `{scriptText(bits)} expected={expected} got={actual}`
			end
		end
	end
	local line = `{entry.name} rows={rows} mismatches={mismatches} trapped={trappedRows}`
	if first ~= nil then
		line ..= ` first: {first}`
	end
	return line, mismatches == 0
end

function LoopOwnedExitFlagRuntimeOracle.run(chunk: any, _source: string, caseName: string): any
	assert(caseName == "loop-owned-exit-flag", `unknown conformance case {caseName}`)
	setfenv(chunk, trapEnvironment())
	local workers = table.pack(chunk())
	assert(workers.n == #WORKERS, `{caseName} fixture returned {workers.n} workers, expected {#WORKERS}`)
	local lines: { string } = {}
	local failed = 0
	for index, entry in WORKERS do
		local worker = workers[index]
		assert(type(worker) == "function", `{caseName} worker {index} changed category`)
		local line, clean = checkWorker(entry, worker)
		if not clean then
			failed += 1
			table.insert(lines, line)
		end
	end
	local pinnedReference = runScript(ownedExitBoundaryExitReentered, stepInvoke, scriptBits(PINNED_SCRIPT))
	assert(pinnedReference == PINNED_EXPECTED, `{caseName} reference changed its written-out row: {pinnedReference}`)
	local pinnedActual = runScript(workers[3], stepInvoke, scriptBits(PINNED_SCRIPT))
	local pinnedHeld = pinnedActual == PINNED_EXPECTED
	if not pinnedHeld then
		table.insert(lines, `pinned {PINNED_WORKER} {PINNED_SCRIPT} expected={PINNED_EXPECTED} got={pinnedActual}`)
	end
	local sideLoopReference = runScript(sideEscapeLoopExitContinue, stepInvoke, scriptBits(SIDE_LOOP_SCRIPT))
	assert(sideLoopReference == SIDE_LOOP_EXPECTED, `{caseName} reference changed its written-out row: {sideLoopReference}`)
	local sideLoopActual = runScript(workers[11], stepInvoke, scriptBits(SIDE_LOOP_SCRIPT))
	if sideLoopActual ~= SIDE_LOOP_EXPECTED then
		pinnedHeld = false
		table.insert(lines, `pinned {SIDE_LOOP_WORKER} {SIDE_LOOP_SCRIPT} expected={SIDE_LOOP_EXPECTED} got={sideLoopActual}`)
	end
	if failed > 0 or not pinnedHeld then
		for _, line in lines do
			print(`{caseName} {line}`)
		end
		assert(false, `{caseName}: {failed} of {#WORKERS} workers failed, pinned rows {if pinnedHeld then "held" else "failed"}`)
	end
	return workers[1]
end

return LoopOwnedExitFlagRuntimeOracle
