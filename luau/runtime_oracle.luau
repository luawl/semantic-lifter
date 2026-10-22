--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local SourceRuntimeOracle = require("./source_runtime_oracle")
local PackMultiLatchRuntimeOracle = require("./pack_multi_latch_runtime_oracle")
local PackReturnStorageRuntimeOracle = require("./pack_return_storage_runtime_oracle")
local IterationExitTransferRuntimeOracle = require("./iteration_exit_transfer_runtime_oracle")
local IterationBreakExitTransferRuntimeOracle = require("./iteration_break_exit_transfer_runtime_oracle")
local IterationHeaderEntryRuntimeOracle = require("./iteration_header_entry_runtime_oracle")

local caseName = process.args[1]
local sourcePath = process.args[2]
local inspectionPath = process.args[3]
assert(caseName ~= nil and caseName ~= "", "expected a conformance case name")
assert(sourcePath ~= nil and sourcePath ~= "", "expected a generated Luau path")

local executionSource = fs.readFile(sourcePath)
local source = if inspectionPath ~= nil then fs.readFile(inspectionPath) else executionSource
local chunk, compileError = loadstring(executionSource, "=" .. sourcePath)
assert(chunk ~= nil, compileError)
local exported: any
local secondaryExport: any
local tertiaryExport: any
local quaternaryExport: any
if caseName == "source-frontend-chunk-varargs" then
	exported = chunk("alpha", 42)
elseif caseName == "fixed-entry-parameters" then
	exported = chunk("alpha", 42, "ignored")
	secondaryExport = chunk("only")
elseif caseName == "open-pack-projection" then
	local order: { string } = {}
	local observations: { { [any]: any } } = {}
	local latchMarkers: { number } = {}
	local producerCalls = 0
	local consumerCalls = 0
	local afterConsumerCalls = 0
	local function marker(): string
		return "projected"
	end
	local function produce(...: any): ...any
		assert(select("#", ...) == 0, "projected producer acquired arguments")
		producerCalls += 1
		table.insert(order, `produce{producerCalls}`)
		return marker, nil, 9
	end
	local function consume(...: any): { [any]: any }
		consumerCalls += 1
		table.insert(order, `consume{consumerCalls}`)
		local packed = table.pack(...)
		table.insert(observations, packed)
		return packed
	end
	local function afterConsumer(latchMarker: number)
		afterConsumerCalls += 1
		table.insert(order, `after{afterConsumerCalls}`)
		table.insert(latchMarkers, latchMarker)
	end
	local thenResults = chunk(produce, consume, afterConsumer, true)
	local elseResults = chunk(produce, consume, afterConsumer, false)
	exported = thenResults[4]
	secondaryExport = {
		thenResults = thenResults,
		elseResults = elseResults,
		observations = observations,
		latchMarkers = latchMarkers,
		order = order,
		producerCalls = producerCalls,
		consumerCalls = consumerCalls,
		afterConsumerCalls = afterConsumerCalls,
	}
elseif caseName == "closed-pack-discard" then
	local order: { string } = {}
	local producerCalls = 0
	local observerCalls = 0
	local function marker(): string
		return "closed-discard"
	end
	local function produce(): () -> string
		producerCalls += 1
		table.insert(order, "produce")
		return marker
	end
	local function observe()
		observerCalls += 1
		table.insert(order, "observe")
	end
	exported = chunk(produce, observe)
	secondaryExport = { order = order, producerCalls = producerCalls, observerCalls = observerCalls }
elseif caseName == "mixed-entry-varargs" then
	local consumerCalls = 0
	local oracleSelect = select
	local oracleRawget = rawget
	local oracleRawset = rawset
	local oracleError = error
	local activeCell = { 10 }
	local function rawTrap(...: any): ...any
		oracleError("mutated external-cell capability was used", 0)
	end
	local function consume(
		label: string,
		packedTail: any,
		adjustedFirst: any,
		adjustedSecond: any,
		adjustedThird: any,
		capturedFirst: number,
		capturedSecond: number,
		stateBeforeCallback: number,
		...: any
	): () -> string
		consumerCalls += 1
		assert(capturedFirst == 41 and capturedSecond == 41, "aliased external values diverged")
		assert(stateBeforeCallback == 10, "external place was not read before the callback")
		activeCell[1] = 20
		rawget = rawTrap
		rawset = rawTrap
		assert(type(packedTail) == "table" and packedTail[1] == label, "shifted table tail lost its fixed prefix")
		if label == "filled" then
			assert(adjustedFirst == 7 and adjustedSecond == nil and adjustedThird == 9, "fixed vararg adjustment changed values")
			assert(packedTail[2] == 7 and packedTail[3] == nil and packedTail[4] == 9, "table tail changed a nil hole")
		assert(oracleSelect("#", ...) == 3, "invocation tail changed open arity")
			local first, second, third = ...
			assert(first == 7 and second == nil and third == 9, "invocation tail changed values")
		else
			assert(label == "empty", "mixed entry passed an unexpected label")
			assert(adjustedFirst == nil and adjustedSecond == nil and adjustedThird == nil, "empty adjustment did not nil-fill")
			assert(packedTail[2] == nil and oracleSelect("#", ...) == 0, "empty tail acquired values")
		end
		return function(): string
			return label
		end
	end
	local filledCell = { 10 }
	activeCell = filledCell
	local filled = table.pack(chunk(41, filledCell, consume, "filled", 7, nil, 9))
	select = oracleSelect
	rawget = oracleRawget
	rawset = oracleRawset
	local emptyCell = { 10 }
	activeCell = emptyCell
	local empty = table.pack(chunk(41, emptyCell, consume, "empty"))
	select = oracleSelect
	rawget = oracleRawget
	rawset = oracleRawset
	exported = filled[1]
	secondaryExport = {
		filled = filled,
		empty = empty,
		filledCell = filledCell,
		emptyCell = emptyCell,
		consumerCalls = consumerCalls,
	}
elseif caseName == "pack-materialized-adjustment" then
	local order: { string } = {}
	local producerCalls = 0
	local protectedCalls = 0
	local resumeExecutions = 0
	local namecallCalls = 0
	local observerCalls = 0
	local oracleCoroutine = coroutine
	local oraclePcall = pcall
	local oracleXpcall = xpcall
	local oracleError = error
	local oracleRawget = rawget
	local oracleRawset = rawset
	local oracleSelect = select
	local oracleTable = table
	local probeMutations = 0
	local function runtimeTrap(...: any): ...any
		oracleError("mutated runtime capability was used", 0)
	end
	local function oraclePackOrderProbe(): string
		return "original pack-order probe"
	end
	pack_order_probe = oraclePackOrderProbe
	local function restoreRuntimeGlobals()
		coroutine = oracleCoroutine
		pcall = oraclePcall
		xpcall = oracleXpcall
		rawget = oracleRawget
		rawset = oracleRawset
		select = oracleSelect
		table = oracleTable
		pack_order_probe = oraclePackOrderProbe
	end
	local function poisonRuntimeGlobals()
		pcall = runtimeTrap
		local mutableCoroutine: any = table.clone(oracleCoroutine)
		coroutine = mutableCoroutine
		local coroutineAlias: any = coroutine
		coroutineAlias.create = runtimeTrap
		coroutineAlias.resume = runtimeTrap
		coroutineAlias.yield = runtimeTrap
	end
	local function marker(): string
		return "marker"
	end
	local function produce(...: any): ...any
		assert(select("#", ...) == 0, "materialized producer acquired arguments")
		producerCalls += 1
		table.insert(order, `produce{producerCalls}`)
		local phase = (producerCalls - 1) % 3 + 1
		if phase == 1 then
			return marker, nil, 33
		elseif phase == 2 then
			return "discarded", 88
		end
		return 5, nil, 7
	end
	local function protectedProduce(...: any): ...any
		assert(select("#", ...) == 0, "protected producer acquired arguments")
		protectedCalls += 1
		table.insert(order, `protected{protectedCalls}`)
		if protectedCalls == 1 then
			return 41, nil, 43
		end
		error("protected failure", 0)
	end
	local successThread = oracleCoroutine.create(function()
		resumeExecutions += 1
		table.insert(order, `resume{resumeExecutions}`)
		oracleCoroutine.yield(51, nil, 53)
	end)
	local failureThread = oracleCoroutine.create(function()
		resumeExecutions += 1
		table.insert(order, `resume{resumeExecutions}`)
		error("resume failure", 0)
	end)
	local namecallReceiver: any = {}
	function namecallReceiver:produce(...: any): ...any
		assert(self == namecallReceiver, "namecall changed its receiver identity")
		assert(select("#", ...) == 0, "materialized namecall acquired arguments")
		namecallCalls += 1
		table.insert(order, `namecall{namecallCalls}`)
		local base = 60 + namecallCalls * 10
		return base, nil, base + 2
	end
	local function observe()
		observerCalls += 1
		table.insert(order, `observe{observerCalls}`)
		if observerCalls == 1 or observerCalls == 9 then
			poisonRuntimeGlobals()
		end
	end
	local function mutateProbe()
		probeMutations += 1
		pack_order_probe = runtimeTrap
	end
	local function runChunk(selected: boolean, resumeTarget: any, resumeFirst: number, resumeThird: number): any
		restoreRuntimeGlobals()
		local execution = oracleCoroutine.create(function()
			return chunk(produce, observe, selected, protectedProduce, resumeTarget, namecallReceiver, mutateProbe)
		end)
		local yielded = table.pack(oracleCoroutine.resume(execution))
		assert(yielded[1] == true, yielded[2])
		assert(yielded.n == 4, "materialized yield changed outbound arity")
		assert(yielded[2] == marker and yielded[3] == nil and yielded[4] == 33, "materialized yield changed outbound values")
		assert(oracleCoroutine.status(execution) == "suspended", "generated chunk did not suspend at its native yield")

		local completed = table.pack(oracleCoroutine.resume(execution, resumeFirst, nil, resumeThird))
		assert(completed[1] == true, completed[2])
		assert(oracleCoroutine.status(execution) == "dead", "generated chunk did not terminate after resumption")
		local results: any = { n = completed.n - 1 }
		for index = 2, completed.n do
			results[index - 1] = completed[index]
		end
		restoreRuntimeGlobals()
		return results
	end
	local narrowResults = runChunk(true, successThread, 91, 93)
	local wideResults = runChunk(false, failureThread, 101, 103)
	local cyclicWorker = narrowResults[narrowResults.n]
	assert(type(cyclicWorker) == "function", "cyclic pack worker was not exported")
	assert(cyclicWorker == wideResults[wideResults.n], "chunk branches exported different cyclic pack workers")
	local storedWorker = narrowResults[narrowResults.n - 1]
	assert(type(storedWorker) == "function", "stored pack worker was not exported")
	assert(storedWorker == wideResults[wideResults.n - 1], "chunk branches exported different stored pack workers")
	local storedProducerCalls = 0
	local function storedEmpty(): ...any
		storedProducerCalls += 1
		return
	end
	local function storedOne(): ...any
		storedProducerCalls += 1
		return 9
	end
	local function storedMany(): ...any
		storedProducerCalls += 1
		return 5, nil, 7, nil
	end
	rawget = runtimeTrap
	rawset = runtimeTrap
	select = runtimeTrap
	local poisonedTable: any = oracleTable.clone(oracleTable)
	poisonedTable.unpack = runtimeTrap
	table = poisonedTable
	local storedEmptyResults = oracleTable.pack(storedWorker(storedEmpty))
	local storedOneResults = oracleTable.pack(storedWorker(storedOne))
	local storedManyResults = oracleTable.pack(storedWorker(storedMany))
	restoreRuntimeGlobals()
	local cyclicProducerCalls = 0
	local cyclicFailureCalls = 0
	local cyclicSkipCalls = 0
	local cyclicSecondSkipCalls = 0
	local function cyclicProduce(...: any): ...any
		assert(select("#", ...) == 0, "cyclic pack producer acquired arguments")
		cyclicProducerCalls += 1
		local base = cyclicProducerCalls * 10
		return base + 1, nil, base + 3
	end
	local function cyclicFail(...: any): ...any
		assert(select("#", ...) == 0, "cyclic failure acquired arguments")
		cyclicFailureCalls += 1
		error("cyclic failure", 0)
	end
	local function cyclicSkip(counter: number): boolean
		cyclicSkipCalls += 1
		assert(cyclicProducerCalls == cyclicSkipCalls, "cyclic skip decision moved before or away from its producer")
		assert(counter == cyclicSkipCalls - 1, "cyclic skip decision received stale loop state")
		return counter == 0
	end
	local function cyclicSecondSkip(counter: number): boolean
		cyclicSecondSkipCalls += 1
		assert(cyclicProducerCalls == counter + 1, "second cyclic skip moved before or away from its producer")
		assert(counter == cyclicSecondSkipCalls, "second cyclic skip received stale loop state")
		return counter == 1
	end
	xpcall = runtimeTrap
	local cyclicResults = table.pack(cyclicWorker(cyclicProduce, cyclicFail, cyclicSkip, cyclicSecondSkip, 3))
	restoreRuntimeGlobals()
	exported = narrowResults[1]
	secondaryExport = {
		narrowResults = narrowResults,
		wideResults = wideResults,
		cyclicResults = cyclicResults,
		cyclicProducerCalls = cyclicProducerCalls,
		cyclicFailureCalls = cyclicFailureCalls,
		cyclicSkipCalls = cyclicSkipCalls,
		cyclicSecondSkipCalls = cyclicSecondSkipCalls,
		storedProducerCalls = storedProducerCalls,
		storedEmptyResults = storedEmptyResults,
		storedOneResults = storedOneResults,
		storedManyResults = storedManyResults,
		order = order,
		producerCalls = producerCalls,
		protectedCalls = protectedCalls,
		resumeExecutions = resumeExecutions,
		namecallCalls = namecallCalls,
		observerCalls = observerCalls,
		probeMutations = probeMutations,
		packOrderProbe = oraclePackOrderProbe,
	}
elseif caseName == "pack-multi-latch" then
	exported = PackMultiLatchRuntimeOracle.run(chunk, source)
elseif caseName == "pack-return-storage" then
	exported = PackReturnStorageRuntimeOracle.run(chunk, source)
elseif caseName == "iteration-exit-transfer" then
	exported = IterationExitTransferRuntimeOracle.run(chunk, source)
elseif caseName == "iteration-break-exit-transfer" then
	exported = IterationBreakExitTransferRuntimeOracle.run(chunk, source, caseName)
elseif caseName == "iteration-escape-join-exit" then
	exported = IterationBreakExitTransferRuntimeOracle.run(chunk, source, caseName)
elseif caseName == "iteration-dominating-break-exit" then
	exported = IterationBreakExitTransferRuntimeOracle.run(chunk, source, caseName)
elseif caseName == "iteration-header-entry" then
	exported = IterationHeaderEntryRuntimeOracle.run(chunk, source, caseName)
elseif caseName == "iteration-continue-completion" then
	exported = IterationHeaderEntryRuntimeOracle.run(chunk, source, caseName)
elseif caseName == "iteration-boundary-body-continue" then
	exported = IterationHeaderEntryRuntimeOracle.run(chunk, source, caseName)
else
	exported, secondaryExport, tertiaryExport, quaternaryExport = chunk()
end
assert(type(exported) == "function", "generated module did not return a function")

if caseName == "absolute" then
	assert(exported(-7) == 7, "absolute(-7) produced the wrong result")
	assert(exported(4) == 4, "absolute(4) produced the wrong result")
elseif caseName == "function-reference-identity" then
	assert(type(secondaryExport) == "function", "second same-target function reference changed category")
	assert(type(tertiaryExport) == "function", "copied function reference changed category")
	assert(type(quaternaryExport) == "function", "different-target function reference changed category")
	assert(exported == secondaryExport, "same-target function references changed identity")
	assert(exported == tertiaryExport, "copied function reference changed identity")
	assert(exported ~= quaternaryExport, "different declared functions collapsed identity")
elseif caseName == "dynamic-truthiness" then
	assert(type(secondaryExport) == "function", "dynamic truthiness fixture did not return its falsy probe")
	assert(exported() == "truthy", "copied dynamic string took the falsy branch")
	assert(secondaryExport() == "falsy", "copied dynamic false took the truthy branch")
elseif caseName == "choose-max" then
	assert(exported(9, 3) == 9, "choose_max(9, 3) produced the wrong result")
	assert(exported(2, 8) == 8, "choose_max(2, 8) produced the wrong result")
	assert(exported(5, 5) == 5, "choose_max(5, 5) produced the wrong result")
elseif caseName == "loop-control-topologies" then
	assert(exported(9) == 9, "loop topology fixture changed a positive value")
	assert(exported(-4) == -4, "loop topology fixture changed a negative value")
elseif caseName == "bounded-expression-depth" then
	assert(exported(0, 1) == 1100, "bounded expression fusion changed the additive chain")
	assert(exported(5, 2) == 2205, "bounded expression fusion changed a nonzero chain")
elseif caseName == "structured-parser-depth" then
	assert(type(secondaryExport) == "function", "structured depth fixture did not export its composed choice")
	local calls = 0
	local function alwaysTrue(): boolean
		calls += 1
		return true
	end
	assert(exported(alwaysTrue, 7, 3) == 7, "nested true control changed its terminal value")
	assert(calls == 64, "nested true control changed predicate evaluation count")
	calls = 0
	local function alwaysFalse(): boolean
		calls += 1
		return false
	end
	assert(exported(alwaysFalse, 7, 3) == 3, "nested false control changed its terminal value")
	assert(calls == 1, "nested false control evaluated a deeper predicate")
	assert(secondaryExport(true, true, false) == true, "composed true control changed value")
	assert(secondaryExport(false, true, false) == false, "composed false control changed value")

	local _, statementCount = string.gsub(source, "if predicate%(%) then", "")
	assert(statementCount == 64, "structured statement fixture changed depth")
	local maximumIndent = 0
	local maximumLineConditionals = 0
	for line in string.gmatch(source, "[^\n]+") do
		local indent = string.match(line, "^ *") or ""
		maximumIndent = math.max(maximumIndent, #indent)
		local _, conditionals = string.gsub(line, "if ", "")
		maximumLineConditionals = math.max(maximumLineConditionals, conditionals)
	end
	assert(maximumIndent <= 64, "deep source exceeded the bounded indentation policy")
	assert(maximumLineConditionals == 6, "physical region groups did not bound composed branch expressions")
elseif caseName == "u32-numerics" then
	local oracleBit32 = bit32
	local mutableBit32: any = table.clone(oracleBit32)
	bit32 = mutableBit32
	local bit32Alias: any = bit32
	bit32Alias.bnot = function(): number
		return 0
	end
	bit32Alias.band = function(): number
		return 0
	end
	bit32Alias.bor = function(): number
		return 0
	end
	bit32Alias.bxor = function(): number
		return 0
	end
	bit32Alias.lshift = function(): number
		return 0
	end
	bit32Alias.rshift = function(): number
		return 0
	end
	local results = { exported(0x12345678, 0x0f0f0f0f) }
	local boundedShiftResults = { exported(0x12345678, 4) }
	local lowShiftResults = { exported(0x80000001, 31) }
	local widthShiftResults = { exported(0x80000001, 32) }
	local highShiftResults = { exported(0x80000001, 2147483648) }
	local maximumShiftResults = { exported(0x80000001, 4294967295) }
	bit32 = oracleBit32
	local andResult = results[1]
	local orResult = results[2]
	local xorResult = results[3]
	local leftShiftResult = boundedShiftResults[4]
	local rightShiftResult = boundedShiftResults[5]
	local notResult = results[6]
	local negativeZero = results[7]
	local fraction = results[8]
	assert(andResult == 0x02040608, "u32 bit_and produced the wrong result")
	assert(orResult == 0x1f3f5f7f, "u32 bit_or produced the wrong result")
	assert(xorResult == 0x1d3b5977, "u32 bit_xor produced the wrong result")
	assert(leftShiftResult == 0x23456780, "u32 shift_left produced the wrong result")
	assert(rightShiftResult == 0x01234567, "u32 shift_right produced the wrong result")
	assert(lowShiftResults[4] == 0x80000000 and lowShiftResults[37] == 0x80000000, "low-count left shifts disagreed")
	assert(lowShiftResults[5] == 1 and lowShiftResults[38] == 1, "low-count right shifts disagreed")
	assert(widthShiftResults[4] == 0 and widthShiftResults[37] == 0, "width-count left shifts changed zero saturation")
	assert(widthShiftResults[5] == 0 and widthShiftResults[38] == 0, "width-count right shifts changed zero saturation")
	assert(highShiftResults[4] == 0x80000001 and highShiftResults[37] == 0, "high-count left shift behavior was conflated")
	assert(highShiftResults[5] == 0x80000001 and highShiftResults[38] == 0, "high-count right shift behavior was conflated")
	assert(maximumShiftResults[4] == 0x80000001 and maximumShiftResults[37] == 0, "maximum-count left shift behavior was conflated")
	assert(maximumShiftResults[5] == 0x80000001 and maximumShiftResults[38] == 0, "maximum-count right shift behavior was conflated")
	assert(notResult == 0xedcba987, "u32 bit_not produced the wrong result")
	assert(1 / negativeZero == -math.huge, "binary64 signed zero was not preserved")
	assert(fraction == 0.1, "binary64 finite fraction was not preserved")
	assert(results[9] == 3.5, "source division produced the wrong result")
	assert(fraction < results[9], "exact finite numeric ordering operands changed relation")
	assert(results[10] == 2, "source floor division produced the wrong result")
	assert(results[11] == 1, "source modulo produced the wrong result")
	assert(results[12] == 8, "source power produced the wrong result")
	assert(results[13] == -7, "source negation produced the wrong result")
	assert(results[14] == "abcd", "source concatenation produced the wrong result")
	assert(results[15] == 4, "source length produced the wrong result")
	assert(results[16] == true, "source logical-or produced the wrong result")
	assert(results[17] == true, "source inequality produced the wrong result")
	assert(results[18] == true, "source ordering produced the wrong result")
	assert(results[19] == 10, "source addition produced the wrong result")
	assert(results[20] == 4, "source subtraction produced the wrong result")
	assert(results[21] == 21, "source multiplication produced the wrong result")
	assert(results[22] == 1 / 0 and results[23] == 1 / 0, "positive infinity literal changed value")
	assert(results[24] == -1 / 0, "negative infinity literal changed value")
	assert(results[25] ~= results[25], "NaN literal lost self-inequality")
	assert(results[26] == -1 / 0, "exact numeric negation lost infinity identity")
	assert(results[27] ~= results[27], "exact numeric arithmetic lost NaN identity")
	assert(results[28] == true, "equal infinity literals became distinct")
	assert(results[29] == true, "opposite infinity literals became equal")
	assert(results[30] == true, "NaN literal became self-equal")
	assert(results[31] == -1 / 0, "exact numeric division lost signed-zero infinity identity")
	assert(results[32] == 1, "number-domain floor division produced the wrong result")
	assert(results[33] == 1.5, "number-domain modulo produced the wrong result")
	assert(results[34] == true, "concatenated string ordering produced the wrong result")
	assert(results[35] == true, "concatenated string equality produced the wrong result")
	assert(results[36] == true, "exact primitive bitwise identity produced the wrong result")
	assert(string.find(source, ">= 32 then 0 else", 1, true) ~= nil, "zero-saturating shift guard disappeared from source")
	assert(string.find(source, "math.huge", 1, true) == nil, "special numeric emission depends on ambient math")
	assert(string.find(source, "(1 / 0)", 1, true) ~= nil, "positive infinity literal disappeared from source")
	assert(string.find(source, "(0 / 0)", 1, true) ~= nil, "NaN literal disappeared from source")
	assert(string.find(source, "wrong-negated-infinity-arm", 1, true) == nil, "proved numeric negation branch was not rewritten")
	assert(string.find(source, "local __lifter_bit32_band = bit32.band", 1, true) ~= nil, "bit32 capability was not captured at chunk entry")
elseif caseName == "automatic-promotion" then
	assert(exported() == "matched", "automatic solver promotion selected the wrong branch")
elseif caseName == "guarded-promotion" then
	assert(exported(0) == 6, "zero-count guarded promotion produced the wrong shift")
	assert(exported(4) == 96, "bounded guarded promotion produced the wrong shift")
	assert(exported(32) == 0, "range rejection was changed by guarded promotion")
	assert(secondaryExport(1.5) == "numeric-matched", "guarded numeric equality selected the wrong branch")
	assert(tertiaryExport(0 / 0) == "nan", "unguarded numeric equality lost NaN behavior")
	assert(tertiaryExport(4) == "finite", "unguarded numeric equality changed finite behavior")
elseif caseName == "query-promotion" then
	assert(exported() == 1, "unresolved query promotion changed modulo runtime behavior")
elseif caseName == "immutable-closure" then
	local addSeven = exported(7)
	local addTwo = exported(2)
	assert(addSeven(5) == 12, "captured addSeven produced the wrong result")
	assert(addTwo(5) == 7, "captured addTwo produced the wrong result")
	assert(addSeven(-3) == 4, "a later closure creation changed an earlier capture")
elseif caseName == "fixed-entry-parameters" then
	assert(
		string.find(source, "local first, second = ...", 1, true) ~= nil,
		"fixed entry parameters were not bound by native chunk adjustment"
	)
	local first, second = exported()
	assert(first == "alpha" and second == 42, "extra chunk arguments changed fixed parameter adjustment")
	assert(type(secondaryExport) == "function", "missing-argument chunk invocation did not return its closure")
	local missingFirst, missingSecond = secondaryExport()
	assert(missingFirst == "only" and missingSecond == nil, "missing chunk arguments did not adjust to nil")
	local emptyProbe = chunk()
	assert(type(emptyProbe) == "function", "empty chunk invocation did not return its closure")
	local emptyFirst, emptySecond = emptyProbe()
	assert(emptyFirst == nil and emptySecond == nil, "empty chunk arguments did not adjust to nil")
elseif caseName == "open-pack-projection" then
	assert(type(secondaryExport) == "table", "open-pack projection audit was not retained")
	local thenResults = secondaryExport.thenResults
	local elseResults = secondaryExport.elseResults
	assert(thenResults.n == 6 and elseResults.n == 6, "open-pack projection changed result arity")
	assert(#secondaryExport.observations == 4, "cyclic open-pack projection changed the iteration count")
	assert(
		#secondaryExport.latchMarkers == 4
			and secondaryExport.latchMarkers[1] == 31
			and secondaryExport.latchMarkers[2] == 31
			and secondaryExport.latchMarkers[3] == 32
			and secondaryExport.latchMarkers[4] == 32,
		"branched indirect latch changed its selected path"
	)
	for index, results in secondaryExport.observations do
		assert(results.n == 6, "cyclic open-pack projection changed an intermediate result arity")
		local expectedPath = if index <= 2 then 11 else 22
		assert(
			results[1] == 1 and results[2] == expectedPath and results[3] == 7,
			"cyclic open-pack projection changed an intermediate path"
		)
		assert(results[4] == exported and results[5] == nil and results[6] == 9, "cyclic open tail changed")
	end
	assert(
		thenResults[1] == 1 and thenResults[2] == 11 and thenResults[3] == 7,
		"then-path values changed during open-pack projection"
	)
	assert(
		elseResults[1] == 1 and elseResults[2] == 22 and elseResults[3] == 7,
		"else-path values changed during open-pack projection"
	)
	assert(
		thenResults[4] == exported and thenResults[5] == nil and thenResults[6] == 9,
		"then-path open tail changed values or nil holes"
	)
	assert(
		elseResults[4] == exported and elseResults[5] == nil and elseResults[6] == 9,
		"else-path open tail changed values or nil holes"
	)
	assert(exported() == "projected", "projected function result changed")
	assert(secondaryExport.producerCalls == 4, "multiple-entry open-pack producer was duplicated or removed")
	assert(secondaryExport.consumerCalls == 4, "open-pack consumer was duplicated or removed")
	assert(secondaryExport.afterConsumerCalls == 4, "post-consumer effect was duplicated or removed")
	assert(
		table.concat(secondaryExport.order, ",")
			== "produce1,consume1,after1,produce2,consume2,after2,produce3,consume3,after3,produce4,consume4,after4",
		"multiple-entry open-pack projection changed observable call order"
	)
	assert(string.find(source, "if choose_then then", 1, true) ~= nil, "open-pack projection lost runtime path selection")
	assert(select(2, string.gsub(source, "producer%(%s*%)", "")) == 1, "open-pack producer was not emitted exactly once")
	assert(select(2, string.gsub(source, "consumer%(1,", "")) == 1, "open-pack consumer was not emitted exactly once")
	assert(select(2, string.gsub(source, "after_consumer%(", "")) == 1, "post-consumer effect was not emitted exactly once")
	assert(string.find(source, "table.pack", 1, true) == nil, "open-pack projection introduced a table helper")
	assert(string.find(source, "__lifter_pack", 1, true) == nil, "open-pack projection introduced a backend pack helper")
elseif caseName == "closed-pack-discard" then
	assert(exported() == "closed-discard", "closed-pack return changed the packed value")
	assert(secondaryExport.producerCalls == 1, "discarded closed-pack producer was duplicated or removed")
	assert(secondaryExport.observerCalls == 1, "closed-pack observer was duplicated or removed")
	assert(table.concat(secondaryExport.order, ",") == "produce,observe", "zero-width adjustment changed effect order")
	local producerPosition = string.find(source, "producer()", 1, true)
	local observerPosition = string.find(source, "observe()", 1, true)
	assert(producerPosition ~= nil and observerPosition ~= nil and producerPosition < observerPosition, "packed producer moved past the observer")
	assert(select(2, string.gsub(source, "producer%(%s*%)", "")) == 1, "packed producer was not emitted exactly once")
	assert(string.find(source, "table.pack", 1, true) == nil, "closed-pack discard introduced a table helper")
	assert(string.find(source, "__lifter_pack", 1, true) == nil, "closed-pack discard introduced a backend pack helper")
	assert(string.find(source, "adjust_pack", 1, true) == nil, "closed-pack adjustment leaked into source")
elseif caseName == "mixed-entry-varargs" then
	local shiftedCount = 0
	for _ in string.gmatch(source, "__lifter_select%(5, %.%.%.%)") do
		shiftedCount += 1
	end
	assert(shiftedCount == 4, "mixed entry did not shift every direct vararg-pack context")
	assert(string.find(source, "local __lifter_select = select", 1, true) ~= nil, "select capability was not captured before ambient mutation")
	assert(string.find(source, "local __lifter_rawget = rawget", 1, true) ~= nil, "external place reads did not capture rawget")
	assert(string.find(source, "local __lifter_rawset = rawset", 1, true) ~= nil, "external place writes did not capture rawset")
	assert(
		string.find(
			source,
			"local __lifter_external_value_0, __lifter_external_place_1, consumer, label = ...",
			1,
			true
		) ~= nil,
		"external slots did not precede ordinary entry arguments"
	)
	assert(string.find(source, "select = consumer", 1, true) ~= nil, "select mutation counterexample was not emitted")
	assert(string.find(source, "function(consumer", 1, true) == nil, "mixed entry introduced a wrapper function")
	assert(type(secondaryExport) == "table", "mixed entry runtime audit was not retained")
	local filled = secondaryExport.filled
	local empty = secondaryExport.empty
	assert(secondaryExport.consumerCalls == 2, "mixed entry changed invocation count")
	assert(filled.n == 13, "expanded return changed filled-tail arity")
	assert(filled[1]() == "filled", "filled callback result changed")
	assert(type(filled[2]) == "table" and filled[2][1] == "filled", "filled table result changed")
	assert(filled[3] == 7 and filled[4] == nil and filled[5] == 9, "filled adjusted results changed")
	assert(filled[6] == 41 and filled[7] == 41, "filled immutable external aliases changed")
	assert(filled[8] == 10 and filled[9] == 20 and filled[10] == 41, "filled external place transitions changed")
	assert(filled[11] == 7 and filled[12] == nil and filled[13] == 9, "filled expanded tail changed")
	assert(secondaryExport.filledCell[1] == 41, "filled external place write was not host-visible")
	assert(empty.n == 10, "expanded return changed empty-tail arity")
	assert(empty[1]() == "empty", "empty callback result changed")
	assert(type(empty[2]) == "table" and empty[2][1] == "empty", "empty table result changed")
	assert(empty[3] == nil and empty[4] == nil and empty[5] == nil, "empty adjusted results did not nil-fill")
	assert(empty[6] == 41 and empty[7] == 41, "empty immutable external aliases changed")
	assert(empty[8] == 10 and empty[9] == 20 and empty[10] == 41, "empty external place transitions changed")
	assert(secondaryExport.emptyCell[1] == 41, "empty external place write was not host-visible")
elseif caseName == "pack-multi-latch" then
	assert(type(exported) == "function", "multiple-latch runtime oracle did not retain its worker")
elseif caseName == "pack-return-storage" then
	assert(type(exported) == "function", "return-only pack storage runtime oracle did not retain its results")
elseif caseName == "iteration-exit-transfer" then
	assert(type(exported) == "function", "iteration exit-transfer runtime oracle did not retain its worker")
elseif caseName == "iteration-break-exit-transfer" then
	assert(type(exported) == "function", "iteration break exit-transfer runtime oracle did not retain its worker")
elseif caseName == "iteration-escape-join-exit" then
	assert(type(exported) == "function", "iteration escape-to-join runtime oracle did not retain its worker")
elseif caseName == "iteration-dominating-break-exit" then
	assert(type(exported) == "function", "iteration dominating-exit runtime oracle did not retain its worker")
elseif caseName == "iteration-header-entry" then
	assert(type(exported) == "function", "iteration header-entry runtime oracle did not retain its worker")
elseif caseName == "iteration-continue-completion" then
	assert(type(exported) == "function", "iteration continue-completion runtime oracle did not retain its worker")
elseif caseName == "iteration-boundary-body-continue" then
	assert(type(exported) == "function", "iteration boundary-body continue runtime oracle did not retain its worker")
elseif caseName == "pack-materialized-adjustment" then
	assert(type(secondaryExport) == "table", "pack materialization audit was not retained")
	local narrowResults = secondaryExport.narrowResults
	local wideResults = secondaryExport.wideResults
	assert(narrowResults.n == 25, "narrow branch pack adjustment changed result arity")
	assert(wideResults.n == 26, "wide branch pack adjustment changed result arity")
	assert(exported() == "marker", "first adjusted pack result changed")
	assert(narrowResults[2] == nil and narrowResults[3] == 33 and narrowResults[4] == nil, "narrow branch changed fixed nil fill")
	assert(wideResults[2] == nil and wideResults[3] == 33 and wideResults[4] == nil, "wide branch changed fixed nil fill")
	assert(
		narrowResults[5] == true and narrowResults[6] == 41 and narrowResults[7] == nil and narrowResults[8] == 43,
		"successful protected pack changed status, payload, or nil holes"
	)
	assert(
		wideResults[5] == false
			and wideResults[6] == "protected failure"
			and wideResults[7] == nil
			and wideResults[8] == nil,
		"failing protected pack changed status, error, or nil fill"
	)
	assert(
		narrowResults[9] == true and narrowResults[10] == 51 and narrowResults[11] == nil and narrowResults[12] == 53,
		"successful resume pack changed status, yielded payload, or nil holes"
	)
	assert(
		wideResults[9] == false
			and type(wideResults[10]) == "string"
			and string.find(wideResults[10], "resume failure", 1, true) ~= nil
			and wideResults[11] == nil
			and wideResults[12] == nil,
		"failing resume pack changed status, error, or nil fill"
	)
	assert(
		narrowResults[13] == 70 and narrowResults[14] == nil and narrowResults[15] == 72 and narrowResults[16] == nil,
		"first native namecall pack changed values or nil fill"
	)
	assert(
		wideResults[13] == 80 and wideResults[14] == nil and wideResults[15] == 82 and wideResults[16] == nil,
		"second native namecall pack changed values or nil fill"
	)
	assert(
		narrowResults[17] == 91 and narrowResults[18] == nil and narrowResults[19] == 93 and narrowResults[20] == nil,
		"first yielded result pack changed resumed values or nil fill"
	)
	assert(
		wideResults[17] == 101 and wideResults[18] == nil and wideResults[19] == 103 and wideResults[20] == nil,
		"second yielded result pack changed resumed values or nil fill"
	)
	assert(narrowResults[21] == 5 and narrowResults[22] == nil, "branch-local prefix copy changed values or nil holes")
	assert(wideResults[21] == 5 and wideResults[22] == nil and wideResults[23] == 7, "wide canonical values changed")
	assert(narrowResults[23] == secondaryExport.packOrderProbe, "narrow nonadjacent closed pack moved its environment read past mutation")
	assert(wideResults[24] == secondaryExport.packOrderProbe, "wide nonadjacent closed pack moved its environment read past mutation")
	local cyclicResults = secondaryExport.cyclicResults
	assert(cyclicResults.n == 10, "cyclic pack worker changed result arity")
	assert(cyclicResults[1] == 31 and cyclicResults[2] == nil, "cyclic pack worker changed its final fixed prefix")
	assert(cyclicResults[3] == 3, "cyclic pack worker changed its final counter")
	assert(cyclicResults[4] == 31, "capture-free closure changed the final produced value")
	assert(cyclicResults[5] == 15, "stable closure changed its value or shared-place capture")
	assert(cyclicResults[6] == 186, "direct/protected iteration-local closure calls changed the final produced value")
	assert(cyclicResults[7] == false, "iteration-local error-handler call lost its failure status")
	assert(
		cyclicResults[8] == 31 and cyclicResults[9] == nil and cyclicResults[10] == 33,
		"cyclic pack worker replayed stale or malformed final-iteration results"
	)
	assert(secondaryExport.cyclicProducerCalls == 3, "cyclic pack producer was duplicated or removed")
	assert(secondaryExport.cyclicSkipCalls == 3, "cyclic skip decision was duplicated or removed")
	assert(secondaryExport.cyclicSecondSkipCalls == 2, "second cyclic skip decision was duplicated or removed")
	assert(secondaryExport.cyclicFailureCalls == 1, "two early continues did not each skip one cyclic consumer execution")
	assert(secondaryExport.storedProducerCalls == 3, "a stored open-pack producer was duplicated or removed")
	local storedEmptyResults = secondaryExport.storedEmptyResults
	local storedOneResults = secondaryExport.storedOneResults
	local storedManyResults = secondaryExport.storedManyResults
	assert(storedEmptyResults.n == 6 and storedEmptyResults[1] == nil and storedEmptyResults[6] == nil, "stored empty pack changed fixed nil fill or expanded arity")
	assert(
		storedOneResults.n == 7
			and storedOneResults[1] == 9
			and storedOneResults[2] == nil
			and storedOneResults[3] == 9
			and storedOneResults[4] == nil
			and storedOneResults[5] == nil
			and storedOneResults[6] == nil
			and storedOneResults[7] == 9,
		"stored one-result pack changed fixed or expanded values"
	)
	assert(
		storedManyResults.n == 10
			and storedManyResults[1] == 5
			and storedManyResults[2] == nil
			and storedManyResults[3] == 5
			and storedManyResults[4] == nil
			and storedManyResults[5] == 7
			and storedManyResults[6] == nil
			and storedManyResults[7] == 5
			and storedManyResults[8] == nil
			and storedManyResults[9] == 7
			and storedManyResults[10] == nil,
		"stored many-result pack changed interior or trailing nils"
	)
	assert(secondaryExport.producerCalls == 6, "an open-pack producer was duplicated or removed")
	assert(secondaryExport.protectedCalls == 2, "a protected producer was duplicated or removed")
	assert(secondaryExport.resumeExecutions == 2, "a resume target was duplicated or removed")
	assert(secondaryExport.namecallCalls == 2, "a native namecall was duplicated or removed")
	assert(secondaryExport.observerCalls == 16, "an intervening observable call was duplicated or removed")
	assert(secondaryExport.probeMutations == 2, "the nonadjacent pack gap was duplicated or removed")
	assert(
		table.concat(secondaryExport.order, ",")
			== "produce1,observe1,protected1,observe2,resume1,observe3,namecall1,observe4,observe5,produce2,observe6,produce3,observe7,observe8,produce4,observe9,protected2,observe10,resume2,observe11,namecall2,observe12,observe13,produce5,observe14,produce6,observe15,observe16",
		"pack materialization changed observable instruction order"
	)
	assert(select(2, string.gsub(source, "%f[%w_]producer%(%s*%)", "")) == 3, "producer calls were not emitted exactly once")
	assert(select(2, string.gsub(source, "cyclic_producer%(%s*%)", "")) == 1, "cyclic pack producer was not emitted exactly once")
	assert(select(2, string.gsub(source, "local __lifter_stored_values_", "")) == 2, "stored pack carrier helper count changed")
	assert(string.find(source, "__lifter_table_unpack", 1, true) ~= nil, "stored pack expansion did not use the captured unpack capability")
	assert(string.find(source, "local capture_free = function(value)", 1, true) ~= nil, "capture-free closure was not constructed in the cyclic worker")
	assert(select(2, string.gsub(source, "capture_free%(%s*cyclic_first%s*%)", "")) == 1, "capture-free closure call was not emitted exactly once")
	assert(select(2, string.gsub(source, "local%s+stable_root%f[%W]", "")) == 1, "stable-root closure declaration changed in the cyclic worker")
	assert(select(2, string.gsub(source, "%f[%w_]stable_root%s*=%s*function%(%s*%)", "")) == 1, "stable-root closure was not constructed in the cyclic worker")
	assert(select(2, string.gsub(source, "stable_root%(%s*%)", "")) == 1, "stable-root closure call was not emitted exactly once")
	assert(string.find(source, "local iteration_capture = function()", 1, true) ~= nil, "iteration-local closure was not constructed in the cyclic worker")
	assert(select(2, string.gsub(source, "local iteration_state = cyclic_first", "")) == 1, "iteration-local place was not allocated exactly once in source")
	assert(string.find(source, "return cyclic_first + iteration_state", 1, true) ~= nil, "iteration-local place was not read by the leaf closure")
	assert(select(2, string.gsub(source, "iteration_capture%(%s*%)", "")) == 2, "iteration-local closure calls were not emitted exactly twice")
	assert(select(2, string.gsub(source, "__lifter_pcall%(pcall_2%)", "")) == 1, "protected-call target shadowed the captured pcall capability")
	assert(select(2, string.gsub(source, "__lifter_xpcall%(xpcall_2,%s*iteration_capture%)", "")) == 1, "error target shadowed the captured xpcall capability")
	assert(select(2, string.gsub(source, "%f[%a]pcall%(", "")) == 1, "ordinary protected call was not emitted exactly once")
	assert(select(2, string.gsub(source, "%f[%a]xpcall%(", "")) == 1, "handled protected call was not emitted exactly once")
	assert(string.find(source, "iteration_capture_alias", 1, true) == nil, "closure copy alias leaked into readable source")
	assert(string.find(source, "iteration_capture_parameter", 1, true) == nil, "closure parameter alias leaked into readable source")
	assert(select(2, string.gsub(source, "__lifter_coroutine_resume%(", "")) == 1, "coroutine resume was not emitted exactly once")
	assert(select(2, string.gsub(source, ":produce%(%s*%)", "")) == 1, "native namecall was not emitted exactly once")
	assert(select(2, string.gsub(source, "__lifter_coroutine_yield%(", "")) == 1, "coroutine yield was not emitted exactly once")
	assert(string.find(source, "if selector then", 1, true) ~= nil, "pack fanout did not retain branch control")
	local nonadjacentRead = string.find(source, "local nonadjacent_probe = pack_order_probe", 1, true)
	local nonadjacentMutation = string.find(source, "mutate_probe()", 1, true)
	assert(nonadjacentRead ~= nil and nonadjacentMutation ~= nil and nonadjacentRead < nonadjacentMutation, "nonadjacent closed pack changed environment-read order")
	assert(string.find(source, "local narrow_snapshotted_probe = nonadjacent_probe", 1, true) ~= nil, "narrow closed-pack fanout was not emitted")
	assert(string.find(source, "local wide_snapshotted_probe = nonadjacent_probe", 1, true) ~= nil, "wide closed-pack fanout was not emitted")
	assert(string.find(source, "table.pack", 1, true) == nil, "pack materialization introduced a table helper")
elseif caseName == "loop-local-lexical-transfer" then
	local iteration = 0
	local snapshots: { () -> number } = {}
	local function nextValue(): (boolean, number)
		iteration += 1
		return iteration < 3, iteration
	end
	local function record(snapshot: () -> number)
		table.insert(snapshots, snapshot)
	end
	local observedFinal: number? = nil
	local function recordFinal(value: number)
		observedFinal = value
	end
	local finalIteration = exported(nextValue, record, recordFinal)
	assert(finalIteration == 3, "loop-local transfer changed the final escaped value")
	assert(observedFinal == 3, "outside-loop operation did not consume the transferred value")
	assert(#snapshots == 3, "loop-local transfer changed the loop trip count")
	assert(snapshots[1]() == 1, "first loop closure lost its iteration snapshot")
	assert(snapshots[2]() == 2, "second loop closure shared another iteration cell")
	assert(snapshots[3]() == 3, "final loop closure lost its iteration snapshot")
elseif caseName == "shared-place-closure" or caseName == "luau-shared-place-closure" then
	local first = exported(10)
	local second = exported(0)
	assert(first(2) == 12, "first counter did not update its shared place")
	assert(first(-5) == 7, "first counter did not retain its shared place")
	assert(second(3) == 3, "second counter did not retain independent state")
	assert(first(1) == 8, "second counter changed the first counter state")
elseif caseName == "table-access-modes" then
	local oracleRawget = rawget
	local oracleRawset = rawset
	local oracleGetfenv = getfenv
	local oracleSetfenv = setfenv
	local oracleSetmetatable = setmetatable
	local oracleError = error
	local environmentEffects = ""
	local environmentStore = {}
	local originalEnvironment = oracleGetfenv(exported)
	local customEnvironment = oracleSetmetatable({ setmetatable = oracleSetmetatable }, {
		__index = function(_, key)
			if key == "not a source identifier" then
				environmentEffects ..= "r"
				return environmentStore[key]
			end
			return originalEnvironment[key]
		end,
		__newindex = function(_, key, value)
			assert(key == "not a source identifier", "generated source wrote an unexpected ambient key")
			environmentEffects ..= "w"
			environmentStore[key] = value
		end,
	})
	local function rawTrap(...: any): ...any
		oracleError("mutated raw capability was used", 0)
	end
	oracleSetfenv(exported, customEnvironment)
	getfenv = rawTrap
	rawget = rawTrap
	rawset = rawTrap
	local passed = exported()
	getfenv = oracleGetfenv
	rawget = oracleRawget
	rawset = oracleRawset
	oracleSetfenv(exported, originalEnvironment)
	assert(passed == true, "raw and semantic table access modes were not preserved")
	assert(environmentEffects == "wr", "ambient environment callback order changed")
	assert(environmentStore["not a source identifier"] == 99, "ambient environment write did not round-trip")
	assert(string.find(source, "local __lifter_getfenv = getfenv", 1, true) ~= nil, "getfenv capability was not captured")
	assert(
		string.find(source, '__lifter_getfenv()["not a source identifier"] = ', 1, true) ~= nil,
		"ambient environment write did not use bracketed current-environment syntax"
	)
	assert(string.find(source, "local __lifter_rawget = rawget", 1, true) ~= nil, "rawget capability was not captured")
	assert(string.find(source, "local __lifter_rawset = rawset", 1, true) ~= nil, "rawset capability was not captured")
elseif caseName == "control-boundaries" then
	local oracleError = error
	local oraclePcall = pcall
	local oracleCoroutine = coroutine
	local function controlTrap(...: any): ...any
		oracleError("mutated control capability was used", 0)
	end
	local mutableCoroutine: any = table.clone(oracleCoroutine)
	coroutine = mutableCoroutine
	local coroutineAlias: any = coroutine
	coroutineAlias.create = controlTrap
	coroutineAlias.resume = controlTrap
	coroutineAlias.yield = controlTrap
	error = controlTrap
	pcall = controlTrap
	local passed = exported()
	error = oracleError
	pcall = oraclePcall
	coroutine = oracleCoroutine
	assert(passed == true, "protected call and coroutine boundaries were not preserved")
	assert(string.find(source, "local __lifter_error = error", 1, true) ~= nil, "error capability was not captured")
	assert(string.find(source, "local __lifter_pcall = pcall", 1, true) ~= nil, "pcall capability was not captured")
	assert(string.find(source, "local __lifter_coroutine_resume = coroutine.resume", 1, true) ~= nil, "coroutine capability was not captured")
	assert(type(secondaryExport) == "function", "effectful terminal projection was not exported")
	local function runProjected(outerCondition: boolean, innerCondition: boolean, expected: string)
		local observerCalls = 0
		local result = secondaryExport(outerCondition, innerCondition, "early", "fallback", function(value: string): string
			observerCalls += 1
			assert(value == expected, "projected terminal received the wrong edge value")
			return "observed:" .. value
		end)
		assert(result == "observed:" .. expected, "projected terminal changed its returned call result")
		assert(observerCalls == 1, "projected terminal effect did not execute exactly once")
	end
	runProjected(true, true, "early")
	runProjected(true, false, "fallback")
	runProjected(false, true, "fallback")
elseif caseName == "edge-scoped-control" then
	assert(exported(true) == "left", "left edge fact selected the wrong dispatcher successor")
	assert(exported(false) == "right", "right edge fact leaked or selected the wrong dispatcher successor")
elseif caseName == "relational-edge-control" then
	assert(exported(true) == "matched", "numeric equality edge fact selected the wrong dispatcher successor")
	assert(exported(false) == "other", "numeric inequality edge fact selected the wrong dispatcher successor")
elseif caseName == "chained-edge-control" then
	assert(exported(true) == "left-chain", "left path lost its authenticated second-hop fact")
	assert(exported(false) == "right-chain", "right path leaked or lost its authenticated second-hop fact")
elseif caseName == "finite-irreducible-control" then
	assert(exported(true) == 3, "secondary irreducible entry changed finite-loop behavior")
	assert(exported(false) == 3, "primary irreducible entry changed finite-loop behavior")
	assert(type(secondaryExport) == "function", "semantic irreducible function was not exported")
	assert(type(tertiaryExport) == "function", "self-loop irreducible function was not exported")
	assert(tertiaryExport(true, 0) == 3, "self-loop secondary entry changed finite-loop behavior")
	assert(tertiaryExport(false, 0) == 3, "self-loop primary entry changed finite-loop behavior")
	local function runSemantic(startSecondary: boolean): any
		local readCalls = 0
		local namecallCalls = 0
		local protectedSuccessCalls = 0
		local protectedCalls = 0
		local handlerCalls = 0
		local invocationCalls = 0
		local forwardingCalls = 0
		local tableWrites = 0
		local environmentWrites = 0
		local proxy = setmetatable({}, {
			__index = function(_self, key)
				assert(key == "counter", "semantic table read changed its key")
				readCalls += 1
				return 3
			end,
			__newindex = function(_self, key, value)
				assert(value == 3, "semantic write changed its value")
				if key == "counter" then
					tableWrites += 1
				elseif key == "mirror" then
					environmentWrites += 1
				else
					error("semantic write changed its key")
				end
			end,
		})
		local expectedForwarded = if startSecondary then 0 else 1
		local function assertSemanticVarargs(label: string, ...: any)
			local marker, hole, trailing = ...
			assert(select("#", ...) == 3, `{label} changed direct function-vararg arity`)
			assert(marker == "vararg-head" and hole == nil and trailing == 17, `{label} changed direct function varargs`)
		end
		local namecallReceiver = {}
		function namecallReceiver.observe(self: any, forwarded: number, ...: any): number
			assert(self == namecallReceiver, "native namecall changed its receiver")
			assert(forwarded == expectedForwarded, "native namecall changed its block-parameter argument")
			assertSemanticVarargs("native namecall", ...)
			namecallCalls += 1
			return 3
		end
		local function protectedSuccessCallee(forwarded: number, ...: any): number
			assert(forwarded == expectedForwarded, "successful protected call changed its block-parameter argument")
			assertSemanticVarargs("successful protected call", ...)
			protectedSuccessCalls += 1
			return forwarded + 20
		end
		local function protectedCallee(forwarded: number, ...: any)
			assert(forwarded == expectedForwarded, "protected call changed its block-parameter argument")
			assertSemanticVarargs("protected call", ...)
			protectedCalls += 1
			error(`protected:{forwarded}`, 0)
		end
		local function errorHandler(message: any): string
			handlerCalls += 1
			return `handled:{tostring(message)}`
		end
		local function observer(
			forwarded: number,
			value: number,
			protectedSuccessOk: boolean,
			protectedSuccessValue: number,
			protectedOk: boolean,
			protectedMessage: string,
			...: any
		): (number, nil, number)
			assert(forwarded == expectedForwarded, "cloned call changed its block-parameter argument")
			assert(value == 3, "cloned call changed its namecall-result argument")
			assert(protectedSuccessOk == true, "successful protected call changed status")
			assert(
				protectedSuccessValue == expectedForwarded + 20,
				"successful protected call changed its payload"
			)
			assert(protectedOk == false, "protected call changed failure status")
			assert(protectedMessage == `handled:protected:{expectedForwarded}`, "protected call changed handled error payload")
			assertSemanticVarargs("cloned call", ...)
			invocationCalls += 1
			return value, nil, value
		end
		local function forwarder(forwarded: number, first: number, hole: any, last: number): (number, number)
			assert(forwarded == expectedForwarded, "argument-pack consumer changed its fixed prefix")
			assert(first == 3 and hole == nil and last == 3, "argument-pack consumer changed its open tail")
			forwardingCalls += 1
			return first, last
		end
		local result = secondaryExport(
			startSecondary,
			proxy,
			"counter",
			observer,
			forwarder,
			namecallReceiver,
			protectedSuccessCallee,
			protectedCallee,
			errorHandler,
			"vararg-head",
			nil,
			17
		)
		assert(readCalls == 2, "ordered semantic reads did not each execute exactly once")
		assert(namecallCalls == 1, "native namecall did not execute exactly once")
		assert(protectedSuccessCalls == 1, "successful protected callee did not execute exactly once")
		assert(protectedCalls == 1, "protected callee did not execute exactly once")
		assert(handlerCalls == 1, "protected error handler did not execute exactly once")
		assert(invocationCalls == 1, "open cloned producer did not execute exactly once")
		assert(forwardingCalls == 1, "argument-pack forwarding call did not execute exactly once")
		assert(tableWrites == 1, "semantic table write did not execute exactly once")
		assert(environmentWrites == 1, "semantic environment write did not execute exactly once")
		return result
	end
	assert(runSemantic(true) == 4, "effectful semantic secondary entry changed finite-loop behavior")
	assert(runSemantic(false) == 4, "effectful semantic primary entry changed finite-loop behavior")
elseif caseName == "irreducible-coroutine-control" then
	local function runProbe(probeStartSecondary: boolean, workerStartSecondary: boolean)
		local verifierCalls = 0
		local function verifier(
			firstOk: boolean,
			yieldedCounter: number,
			yieldedHead: string,
			yieldedHole: any,
			yieldedTail: number,
			secondOk: boolean,
			finalCounter: number
		): number
			verifierCalls += 1
			assert(firstOk == true, "first admitted coroutine resume changed status")
			assert(
				yieldedCounter == (if workerStartSecondary then 0 else 1),
				"coroutine split changed the yielded counter"
			)
			assert(
				yieldedHead == "vararg-head" and yieldedHole == nil and yieldedTail == 17,
				"coroutine yield changed direct varargs"
			)
			assert(secondOk == true and finalCounter == 3, "second admitted coroutine resume changed completion")
			return finalCounter
		end
		local result = exported(
			probeStartSecondary,
			workerStartSecondary,
			2,
			verifier,
			"vararg-head",
			nil,
			17
		)
		assert(result == 3, "admitted coroutine probe changed its final result")
		assert(verifierCalls == 1, "admitted coroutine chain did not execute exactly once")
	end
	runProbe(true, true)
	runProbe(true, false)
	runProbe(false, true)
	runProbe(false, false)
elseif caseName == "irreducible-table-construction" then
	local function runWorker(startSecondary: boolean)
		local producerCalls = 0
		local sink: { [any]: any } = {}
		local expectedCounter = if startSecondary then 0 else 1
		local function producer(counter: number): (number, nil, number)
			assert(counter == expectedCounter, "table tail producer received the wrong split parameter")
			producerCalls += 1
			return counter + 10, nil, counter + 20
		end
		local result = exported(startSecondary, sink, producer, "vararg-head", nil, 17)
		assert(result == 3, "table construction changed finite-loop continuation")
		assert(producerCalls == 1, "table tail producer did not execute exactly once")
		local constructed = sink.result
		assert(type(constructed) == "table", "split table was not published")
		assert(constructed[1] == expectedCounter and constructed[2] == expectedCounter + 10, "table list prefix changed")
		assert(constructed[3] == nil and constructed[4] == expectedCounter + 20, "table tail lost its nil hole or trailing value")
		local nested = constructed.nested
		assert(type(nested) == "table" and nested ~= constructed, "nested table identity collapsed")
		assert(nested[1] == expectedCounter and nested[2] == "vararg-head", "direct-vararg table prefix changed")
		assert(nested[3] == nil and nested[4] == 17, "direct-vararg table lost its nil hole or trailing value")
		assert(type(constructed.empty) == "table" and constructed.empty ~= nested, "empty table identity collapsed")
		assert(next(constructed.empty) == nil, "empty table allocation acquired fields")
	end
	runWorker(true)
	runWorker(false)
elseif caseName == "irreducible-string-interpolation" then
	local oracleString = string
	local oracleError = error
	local mutableString: any = table.clone(oracleString)
	string = mutableString
	local stringAlias: any = string
	stringAlias.format = function(...: any): ...any
		oracleError("mutated string.format capability was used", 0)
	end
	local function runWorker(startSecondary: boolean)
		local conversionCalls = 0
		local dynamicObject: any = setmetatable({}, {
			__tostring = function(_: any): string
				conversionCalls += 1
				return "box"
			end,
		})
		local sink: { [any]: any } = {}
		local result = exported(startSecondary, dynamicObject, sink)
		local expectedCounter = if startSecondary then 0 else 1
		assert(result == 3, "string interpolation changed finite-loop continuation")
		assert(conversionCalls == 1, "string interpolation changed dynamic conversion dispatch count")
		assert(
			sink.result == oracleString.format("prefix:box:counter:%d:suffix", expectedCounter),
			"string interpolation changed segment or value order"
		)
	end
	runWorker(true)
	runWorker(false)
	string = oracleString
	assert(string.find(source, "local __lifter_string_format = string.format", 1, true) ~= nil, "string.format capability was not captured")
elseif caseName == "irreducible-closure-captures" then
	local function makeCounter(startSecondary: boolean, seed: number, initialState: number): (number, (...number) -> ...number)
		local sink: { [any]: any } = {}
		local finalCounter = exported(startSecondary, seed, initialState, sink)
		assert(finalCounter == 1, "closure fixture changed finite-loop continuation")
		assert(type(sink.closure) == "function", "closure fixture did not publish its closure")
		return finalCounter, sink.closure
	end

	local _, sourceClosure = makeCounter(false, 10, 100)
	local _, cloneClosure = makeCounter(true, 10, 100)
	assert(sourceClosure ~= cloneClosure, "closure replay collapsed independent factory instances")

	local sourceSnapshot, sourceState = sourceClosure(2)
	assert(sourceSnapshot == 11 and sourceState == 102, "source-path closure changed its snapshot or initial mutation")
	sourceSnapshot, sourceState = sourceClosure(3)
	assert(sourceSnapshot == 11 and sourceState == 105, "source-path closure lost snapshot stability or shared mutation")

	local cloneSnapshot, cloneState = cloneClosure(7)
	assert(cloneSnapshot == 11 and cloneState == 107, "clone-path closure changed its snapshot or initial mutation")
	cloneSnapshot, cloneState = cloneClosure(-2)
	assert(cloneSnapshot == 11 and cloneState == 105, "clone-path closure lost snapshot stability or shared mutation")

	sourceSnapshot, sourceState = sourceClosure(1)
	assert(sourceSnapshot == 11 and sourceState == 106, "clone-path mutation leaked into the source factory instance")
elseif caseName == "irreducible-iteration-convergence" then
	assert(type(secondaryExport) == "function", "iteration fixture did not export its generic worker")

	local function runNumeric(startLatch: boolean)
		local observed: { number } = {}
		local selectorCalls = 0
		local normalizedLimit, normalizedStep = exported(startLatch, 1, 3, 1, function(index: number)
			table.insert(observed, index)
		end, function(selected: boolean): boolean
			selectorCalls += 1
			return selected
		end)
		assert(selectorCalls == 1, "numeric iteration changed selector effects")
		assert(normalizedLimit == 3 and normalizedStep == 1, "numeric iteration changed normalized state escape")
		assert(#observed == 3, "numeric iteration changed its trip count")
		assert(observed[1] == 1 and observed[2] == 2 and observed[3] == 3, "numeric iteration changed its sequence")
	end
	runNumeric(false)
	runNumeric(true)

	local function runGeneric(startLatch: boolean)
		local observed: { { number } } = {}
		local selectorCalls = 0
		secondaryExport(startLatch, next, { 10, 20, 30 }, nil, function(index: number, value: number)
			table.insert(observed, { index, value })
		end, function(selected: boolean): boolean
			selectorCalls += 1
			return selected
		end)
		assert(selectorCalls == 1, "generic iteration changed selector effects")
		assert(#observed == 3, "generic iteration changed its trip count")
		assert(observed[1][1] == 1 and observed[1][2] == 10, "generic iteration changed its first tuple")
		assert(observed[2][1] == 2 and observed[2][2] == 20, "generic iteration changed its second tuple")
		assert(observed[3][1] == 3 and observed[3][2] == 30, "generic iteration changed its third tuple")
	end
	runGeneric(false)
	runGeneric(true)
elseif SourceRuntimeOracle.run(caseName, source, exported) then
	-- Checked by the focused source-runtime oracle.
else
	error(`unknown conformance case {caseName}`)
end
