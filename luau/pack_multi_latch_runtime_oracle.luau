--!strict

local PackMultiLatchRuntimeOracle = {}

local function runScenario(worker: any, firstLatchContinues: boolean): { [number]: any, n: number }
	local producerCalls = 0
	local earlyContinueCalls = 0
	local latchChoices = 0
	local firstLatchCalls = 0
	local secondLatchCalls = 0

	local function produce(): ...any
		producerCalls += 1
		local base = producerCalls * 10
		return base + 1, nil, base + 3
	end

	local function earlyContinue(counter: number): boolean
		earlyContinueCalls += 1
		assert(counter == earlyContinueCalls, "early continue received stale loop state")
		return counter == 1
	end

	local function chooseLatch(counter: number): boolean
		latchChoices += 1
		assert(counter == latchChoices + 1, "latch choice received stale loop state")
		return counter == 2
	end

	local function firstLatch(counter: number): boolean
		firstLatchCalls += 1
		assert(counter == 2, "first latch received stale loop state")
		return firstLatchContinues
	end

	local function secondLatch(counter: number): boolean
		secondLatchCalls += 1
		assert(counter == 3, "second latch received stale loop state")
		return false
	end

	local results = table.pack(worker(produce, earlyContinue, chooseLatch, firstLatch, secondLatch))
	assert(results.n == 6, "multiple-latch expanded return changed arity")
	local expectedCounter = if firstLatchContinues then 3 else 2
	local expectedBase = expectedCounter * 10
	assert(results[1] == expectedBase + 1, "multiple-latch fixed result changed")
	assert(results[2] == nil, "multiple-latch fixed nil hole changed")
	assert(results[3] == expectedCounter, "multiple-latch counter changed")
	assert(results[4] == expectedBase + 1, "multiple-latch pack head changed")
	assert(results[5] == nil, "multiple-latch pack nil hole changed")
	assert(results[6] == expectedBase + 3, "multiple-latch pack tail changed")
	assert(producerCalls == expectedCounter, "latch-set producer was duplicated or removed")
	assert(earlyContinueCalls == expectedCounter, "early continue did not run once per producer")
	assert(latchChoices == expectedCounter - 1, "multiple-latch split did not run once per producer")
	assert(firstLatchCalls == 1, "first canonical latch was not executed exactly once")
	assert(secondLatchCalls == (if firstLatchContinues then 1 else 0), "second canonical latch count changed")
	return results
end

function PackMultiLatchRuntimeOracle.run(chunk: any, source: string): any
	local worker = chunk()
	local firstExitResults = runScenario(worker, false)
	local secondExitResults = runScenario(worker, true)
	assert(firstExitResults[1] == 21 and firstExitResults[6] == 23, "first shared exit route changed")
	assert(secondExitResults[1] == 31 and secondExitResults[6] == 33, "second shared exit route changed")
	assert(
		select(2, string.gsub(source, "producer%(%s*%)", "")) == 1,
		"multiple-latch producer expression was duplicated"
	)
	assert(
		select(2, string.gsub(source, "local __lifter_stored_values_", "")) == 1,
		"multiple-latch pack carrier helper count changed"
	)
	return worker
end

return PackMultiLatchRuntimeOracle
