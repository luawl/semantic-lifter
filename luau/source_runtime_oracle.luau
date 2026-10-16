--!strict

local SourceRuntimeOracle = {}

local function assertPrimitiveOperators(values: any)
	assert(type(values) == "table", "source frontend lost the primitive operator result table")
	assert(values.add == 2.5 and values.subtract == 3 and values.multiply == 2, "source frontend changed primitive additive behavior")
	assert(values.divide == 2.5 and values.floorDivide == 2 and values.modulo == 1, "source frontend changed primitive division behavior")
	assert(values.power == 8 and values.concat == "value=2", "source frontend changed primitive power or concat behavior")
	assert(values.equal == false and values.notEqual == true, "source frontend changed primitive equality behavior")
	assert(
		values.less == true and values.lessEqual == true and values.greater == true and values.greaterEqual == true,
		"source frontend changed primitive ordering behavior"
	)
	assert(values.logicalNot == false and values.negate == -0.5 and values.length == 5, "source frontend changed primitive unary behavior")
	assert(values.dynamicLength == 7 and values.dynamicUnaryTag == "unary-result", "source frontend changed dynamic unary dispatch")
	assert(
		values.dynamicAdd == 11
			and values.dynamicSubtract == 12
			and values.dynamicMultiply == 13
			and values.dynamicDivide == 14
			and values.dynamicFloorDivide == 15
			and values.dynamicModulo == 16
			and values.dynamicPower == 17
			and values.dynamicConcat == "joined",
		"source frontend changed dynamic arithmetic or concatenation dispatch"
	)
	assert(
		values.dynamicEqual == true
			and values.dynamicNotEqual == false
			and values.dynamicOrdered == false
			and values.dynamicLessEqual == true
			and values.dynamicGreater == false
			and values.dynamicGreaterEqual == true,
		"source frontend changed dynamic comparison coercion or operand order"
	)
	assert(
		values.dynamicEffects == "luasmdirpceeoLRqLRoRLqRL",
		"source frontend changed dynamic operator dispatch order or count"
	)
end

function SourceRuntimeOracle.run(caseName: string, source: string, exported: any): boolean
	if caseName == "source-frontend-straight-line" then
		assert(
			string.find(source, "__lifter_value_storage%b[]%(%s*%)%s+%+%s+%-%s*__lifter_value_storage%b[]%(%s*%)") ~= nil,
			"ordered unary and binary producers did not remain one expression"
		)
		local positive, positiveOrdered, positiveOrder, positiveOperators, positiveTransitive = exported(3, 4)
		assert(positive == 14 and positiveOrdered == -1, "source frontend changed nested-call arithmetic")
		assert(positiveOrder == 12, "source frontend reordered a nested effectful chain")
		assertPrimitiveOperators(positiveOperators)
		assert(positiveTransitive == 4.5, "source frontend changed transitive place/operator domains")
		local signed, signedOrdered, signedOrder, signedOperators, signedTransitive = exported(-8, 3)
		assert(signed == -10 and signedOrdered == -11, "source frontend changed signed arithmetic")
		assert(signedOrder == 12, "source frontend duplicated a nested effectful chain")
		assertPrimitiveOperators(signedOperators)
		assert(signedTransitive == 4.5, "source frontend made transitive domain refinement input-dependent")
	elseif caseName == "source-frontend-effectful-assignment" then
		local value, calls, fixed, leaked = exported(7)
		assert(value == 12, "source frontend changed effectful assignment value selection")
		assert(calls == 2, "source frontend duplicated or skipped an effectful assignment call")
		assert(fixed == 18 and leaked == nil, "source frontend reopened a fixed one-result call")
	elseif caseName == "source-frontend-structured-if" then
		assert(string.find(source, "unreachable-dynamic-not", 1, true) == nil, "source-bound dynamic logical not branch was not eliminated")
		assert(string.find(source, "unreachable-dynamic-equal", 1, true) == nil, "source-bound dynamic equality branch was not eliminated")
		assert(string.find(source, "unreachable-dynamic-not-equal", 1, true) == nil, "source-bound dynamic inequality branch was not eliminated")
		assert(string.find(source, "do%s+end") == nil, "emitter retained an empty structural scope")
		assert(exported(9, 3) == 18, "source frontend changed the then branch or join")
		assert(exported(2, 8) == 16, "source frontend changed the else branch or join")
		assert(exported(5, 5) == 10, "source frontend changed equal-value branch behavior")
	elseif caseName == "source-frontend-captured-mutation" then
		local first = exported(10)
		local second = exported(-2)
		assert(first(3) == 13, "source frontend lost the first captured write")
		assert(first(-5) == 8, "source frontend lost captured place persistence")
		assert(second(7) == 5, "source frontend aliased independent closure instances")
		assert(first(1) == 9, "source frontend shared distinct captured places")
	elseif caseName == "source-frontend-variadic-forward" then
		local results = { exported(4, "five", false) }
		assert(#results == 4, "source frontend changed forwarded result arity")
		assert(results[1] == "head", "source frontend changed the fixed result prefix")
		assert(results[2] == 4 and results[3] == "five" and results[4] == false, "source frontend changed the open result tail")
	elseif caseName == "source-frontend-chunk-varargs" then
		local first, second = exported()
		assert(first == "alpha", "source frontend changed the first chunk vararg")
		assert(second == 42, "source frontend changed the second chunk vararg")
	elseif caseName == "source-frontend-table-access" then
		assert(string.find(source, "local nested = (leftRecord())[rightKey()]", 1, true) ~= nil, "ordered sibling producers did not fuse into one table address")
		assert(string.find(source, "proxy.slot = proxyValue()", 1, true) ~= nil, "semantic table write did not remain readable source")
		assert(string.find(source, "local proxyRead = proxy.slot", 1, true) ~= nil, "semantic table read did not remain readable source")
		local dynamicSum, dynamicNested, dynamicOrder, dynamicProxyRead, dynamicMetamethodEffects, dynamicEnvironmentRead, dynamicEnvironmentMatches =
			exported("dynamic", 9)
		assert(dynamicSum == 12 and dynamicNested == 9, "source frontend changed dynamic table mutation or lookup")
		assert(dynamicOrder == 12, "source frontend changed table-before-key evaluation order")
		assert(dynamicProxyRead == 10 and dynamicMetamethodEffects == "vwre", "source frontend changed table or environment metamethod effects")
		assert(dynamicEnvironmentRead == 29 and dynamicEnvironmentMatches == true, "source frontend changed dynamic function-environment identity")
		local fixedSum, fixedNested, fixedOrder, fixedProxyRead, fixedMetamethodEffects, fixedEnvironmentRead, fixedEnvironmentMatches =
			exported("fixed", 4)
		assert(fixedSum == 8 and fixedNested == 4, "source frontend changed same-key overwrite behavior")
		assert(fixedOrder == 12, "source frontend duplicated or reordered a nested table address")
		assert(fixedProxyRead == 5 and fixedMetamethodEffects == "vwre", "source frontend changed repeated table or environment metamethod effects")
		assert(fixedEnvironmentRead == 24 and fixedEnvironmentMatches == true, "source frontend changed repeated function-environment identity")
	elseif caseName == "source-frontend-while-loop" then
		local total, earlyTag, earlyValue, exitTag, exitValue, nilTag, nilValue,
			nestedEarlyTag, nestedEarlyValue, nestedDoneTag, nestedDoneValue, nestedFallbackTag, nestedFallbackValue,
			nestedForwardedThreeTag, nestedForwardedThreeValue, nestedForwardedFourTag, nestedForwardedFourValue = exported(6)
		assert(total == 12, "source frontend changed repeated loop updates")
		assert(earlyTag == "early" and earlyValue == 2, "source frontend changed a terminal loop arm")
		assert(exitTag == "exit" and exitValue == 6, "source frontend changed a short-circuit loop exit")
		assert(nilTag == "nil" and nilValue == -1, "source frontend changed a nil short-circuit loop exit")
		assert(nestedEarlyTag == "nested-done" and nestedEarlyValue == 0, "source frontend changed a nested terminal arm")
		assert(nestedDoneTag == "nested-done" and nestedDoneValue == 7, "source frontend changed a nested loop continue")
		assert(nestedFallbackTag == "nested-done" and nestedFallbackValue == 6, "source frontend changed a shared loop tail")
		assert(
			nestedForwardedThreeTag == "nested-done"
				and nestedForwardedThreeValue == 13
				and nestedForwardedFourTag == "nested-done"
				and nestedForwardedFourValue == 14,
			"source frontend changed an effectful arm entering a shared continue suffix"
		)
		local oddTotal = exported(5)
		assert(oddTotal == 6, "source frontend changed loop exit behavior")
		local zeroTotal, zeroTag, zeroValue = exported(0)
		assert(zeroTotal == 0 and zeroTag == "exit" and zeroValue == 0, "source frontend changed zero-iteration behavior")
	elseif caseName == "source-frontend-loop-control" then
		assert(exported(10) == 12, "source frontend changed break or continue behavior")
		assert(exported(4) == 7, "source frontend changed continue with natural exit")
		assert(exported(0) == 0, "source frontend changed zero-iteration loop control")
	elseif caseName == "source-frontend-short-circuit" then
		assert(
			string.find(source, 'placed = if condition() then arm("t") else arm("f")', 1, true) ~= nil,
			"an immediate lexical-place consumer retained a structured-result temporary"
		)
		assert(
			string.find(source, '.selected or "missing"', 1, true) ~= nil
				and string.find(source, "\n  local field", 1, true) == nil,
			"a short-circuit condition producer stayed materialized"
		)
		local truthy, skipped, truthyCalls, truthyPlaced, truthyOrder, truthySelected, truthyReads, truthyAnd, truthyOr = exported("present")
		assert(truthy == "present" and skipped == false and truthyCalls == 0, "source frontend eagerly evaluated a short-circuit operand")
		assert(truthyPlaced == "t" and truthyOrder == "ct", "structured place deferral changed true-path effect order")
		assert(truthySelected == "present" and truthyReads == 1, "condition absorption duplicated or changed a truthy semantic get")
		assert(truthyAnd == true and truthyOr == false, "typed short-circuit joins changed truthy behavior")
		local fallback, stillSkipped, fallbackCalls, fallbackPlaced, fallbackOrder, fallbackSelected, fallbackReads, fallbackAnd, fallbackOr = exported(nil)
		assert(fallback == "fallback" and stillSkipped == false and fallbackCalls == 1, "source frontend changed short-circuit fallback behavior")
		assert(fallbackPlaced == "f" and fallbackOrder == "cf", "structured place deferral changed false-path effect order")
		assert(fallbackSelected == "missing" and fallbackReads == 1, "condition absorption duplicated or changed a falsey semantic get")
		assert(fallbackAnd == false and fallbackOr == true, "typed short-circuit joins changed falsey behavior")
	elseif caseName == "source-frontend-multi-assignment" then
		local left, right, first, second, slot, order, index, firstSlot, secondSlot = exported("first", "second")
		assert(left == 5 and right == 4, "source frontend changed simultaneous assignment")
		assert(first == "first" and second == "second", "source frontend changed vararg adjustment")
		assert(slot == 7 and order == "tkr", "source frontend changed assignment address, RHS, or write order")
		assert(index == 2 and firstSlot == 30 and secondSlot == 20, "source frontend changed old-index assignment addressing")
		local _, _, only, missing = exported("only")
		assert(only == "only" and missing == nil, "source frontend changed missing-value nil adjustment")
	elseif caseName == "source-frontend-method-call" then
		assert(
			string.find(source, "local result = (get()):add(argument())", 1, true) ~= nil,
			"ordered receiver and argument-pack producers did not remain one direct namecall"
		)
		assert(
			string.find(source, "(getCallable())(firstCallableArgument(), secondCallableArgument())", 1, true) ~= nil,
			"ordered callable-table producers did not remain one direct call"
		)
		local result, calls, order, missingOk, missingError, missingOrder, fixedFirst, fixedSecond, fixedThird, fixedFourth, packed, callableOrder = exported(7)
		assert(result == 12, "source frontend changed method receiver or argument order")
		assert(calls == 1, "source frontend evaluated the method receiver more than once")
		assert(order == ":argumentresolve", "source frontend changed Luau NAMECALL argument-before-lookup order")
		assert(missingOk == false, "source frontend changed missing-method failure behavior")
		assert(missingOrder == ":argumentresolve", "source frontend changed missing NAMECALL argument-before-lookup order")
		assert(
			type(missingError) == "string"
				and string.find(missingError, "attempt to call missing method 'missing' of table", 1, true) ~= nil,
			"source frontend replaced native NAMECALL missing-method semantics"
		)
		assert(
			fixedFirst == 27 and fixedSecond == 8 and fixedThird == nil and fixedFourth == 20,
			"source frontend changed callable-table implicit self or fixed results"
		)
		assert(
			type(packed) == "table" and packed[1] == 27 and packed[2] == 8 and packed[3] == nil and packed[4] == 20,
			"source frontend changed callable-table open results or nil holes"
		)
		assert(callableOrder == "c12ic12i", "source frontend changed callable-table callee, argument, or dispatch order")
	elseif caseName == "source-frontend-recursive-local" then
		assert(exported(0) == 1, "source frontend changed the recursive base case")
		assert(exported(5) == 120, "source frontend changed recursive self-capture")
	elseif caseName == "source-frontend-repeat-loop" then
		assert(exported(0) == 1, "source frontend changed mandatory first repeat iteration")
		local continuedValue, continuedCaptures = exported(2)
		assert(continuedValue == 2, "source frontend changed repeat continue-to-latch behavior")
		assert(continuedCaptures[2]() == 2, "source frontend changed repeat continue capture identity")
		local ordinaryValue, ordinaryCaptures = exported(4)
		assert(ordinaryValue == 4, "source frontend changed repeat condition behavior")
		for index = 1, 4 do
			assert(ordinaryCaptures[index]() == index, "source frontend merged repeat-local capture identity")
		end
		assert(exported(10) == 5, "source frontend changed repeat break behavior")
	elseif caseName == "source-frontend-compound-assignment" then
		assert(string.find(source, "calls += 1", 1, true) ~= nil, "source frontend did not recover a lexical compound update")
		assert(string.find(source, "object[call_result] += right()", 1, true) ~= nil, "source frontend did not recover ordered table compound syntax")
		assert(string.find(source, "state += ", 1, true) ~= nil, "source frontend did not recover an ordered compound RHS")
		assert(
			string.find(source, "semantic_lifter_compound_global_probe += globalRight()", 1, true) ~= nil,
			"source frontend did not recover ordered ambient-global compound syntax"
		)
		assert(
			string.find(source, "redirected += right()", 1, true) ~= nil,
			"source frontend did not recover ordered function-environment compound syntax"
		)
		assert(string.find(source, "local concatState_3 = concatState", 1, true) ~= nil, "source frontend lost pre-RHS local concat capture")
		assert(string.find(source, "\n  do\n", 1, true) == nil, "fused straight-line IR was split by the raw-instruction segment bound")
		assert(string.find(source, "return object.value, calls, state, globalResult, concatState", 1, true) ~= nil, "ordered return snapshots blocked a preceding scalar read from fusing")
		local value, calls, state, globalValue, concatState, environmentValue, environmentEffects, storedEnvironmentValue, environmentMatches = exported(10, 4)
		assert(value == 14, "source frontend changed Luau's table-read-before-RHS compound order")
		assert(calls == 1, "source frontend evaluated a compound target address more than once")
		assert(state == 104, "source frontend changed Luau's RHS-before-target-read compound order")
		assert(globalValue == 14, "source frontend changed Luau's global-read-before-RHS compound order")
		assert(concatState == "oldrhs", "source frontend changed Luau's local concat-read-before-RHS order")
		assert(environmentValue == 14 and storedEnvironmentValue == 14, "source frontend changed function-environment compound mutation")
		assert(environmentEffects == "rvwr", "source frontend changed function-environment callback order")
		assert(environmentMatches == true, "source frontend changed function-environment identity after mutation")
	elseif caseName == "source-frontend-if-expression" then
		assert(
			string.find(source, 'consume(if condition() then arm("t") else arm("f"))', 1, true) ~= nil,
			"an immediate call consumer retained a structured-result temporary"
		)
		assert(
			string.find(source, 'flag or "return-fallback"', 1, true) ~= nil
				and string.find(source, "\n  local logical_result", 1, true) == nil,
			"an immediate return consumer retained a logical-result temporary"
		)
		local yes, yesCalls, nestedYes, immediateYes, yesOrder, returnedYes, typedYes, transitiveYes = exported(true)
		assert(yes == "yes" and yesCalls == 3, "source frontend changed the true if-expression arm or evaluation count")
		assert(nestedYes == "nested-yes", "source frontend changed nested true conditional behavior")
		assert(immediateYes == "t" and yesOrder == "ctu", "structured call deferral changed true-path effect order")
		assert(returnedYes == true, "structured return deferral changed a truthy result")
		assert(typedYes == "typed-yes", "typed if-expression join changed true-path behavior")
		assert(transitiveYes == 3.5, "transitive if-expression domain changed true-path behavior")
		local no, noCalls, nestedNo, immediateNo, noOrder, returnedNo, typedNo, transitiveNo = exported(false)
		assert(no == "no" and noCalls == 3, "source frontend changed the false if-expression arm or evaluation count")
		assert(nestedNo == "nested-no", "source frontend changed nested false conditional behavior")
		assert(immediateNo == "f" and noOrder == "cfu", "structured call deferral changed false-path effect order")
		assert(returnedNo == "return-fallback", "structured return deferral changed a falsey result")
		assert(typedNo == "typed-no", "typed if-expression join changed false-path behavior")
		assert(transitiveNo == 4.5, "transitive if-expression domain changed false-path behavior")
	elseif caseName == "source-frontend-per-iteration-capture" then
		local first, second = exported()
		assert(type(first) == "function" and type(second) == "function", "source frontend lost loop-created closures")
		assert(first() == 1 and first() == 2, "source frontend lost the first iteration cell")
		assert(second() == 1, "source frontend aliased the second iteration cell")
		assert(first() == 3, "source frontend shared independent iteration cells")
	elseif caseName == "source-frontend-per-iteration-capture-branch" then
		local getters, setters = exported(3)
		assert(type(getters[1]) == "function" and type(setters[3]) == "function", "source frontend lost loop-created closures written across blocks")
		assert(getters[1]() == 20, "source frontend lost the first iteration cell written across blocks")
		assert(getters[2]() == 42, "source frontend lost the arm write of the second iteration cell")
		assert(getters[3]() == 60, "source frontend lost the third iteration cell")
		setters[1](5)
		assert(getters[1]() == 25, "source frontend split the cell of one iteration between its closures")
		assert(getters[2]() == 42 and getters[3]() == 60, "source frontend shared cells written across blocks between iterations")
		local emptyGetters = exported(0)
		assert(next(emptyGetters) == nil, "source frontend created a closure for an empty loop")
	elseif caseName == "source-frontend-always-return-iteration" then
		local forLines = 0
		for line in string.gmatch(source, "[^\n]+") do
			if string.match(line, "^%s*for .+ do%s*$") ~= nil then
				forLines += 1
			end
		end
		assert(forLines == 5, "source frontend lost an always-returning native for loop")
		assert(string.find(source, "break", 1, true) == nil, "an always-returning loop kept a break after its return")
		local function check(initial: any, limit: any, expected: { any })
			local results = table.pack(exported(initial, limit))
			assert(results.n == 7, "always-returning loops changed the result count")
			for index = 1, 7 do
				assert(results[index] == expected[index], "always-returning loops changed a result")
			end
		end
		check(1, 3, { 1, true, false, 2, 1, 6, 1 })
		check(3, 1, { 0, true, false, 1, 1, 6, 1 })
		check(3, 3, { 3, true, false, 4, 1, 6, 3 })
		check(10, 3, { 0, true, false, 6, 1, 6, 0 })
	elseif caseName == "source-frontend-always-return-iteration-in-loop" then
		local forLines = 0
		for line in string.gmatch(source, "[^\n]+") do
			if string.match(line, "^%s*for .+ do%s*$") ~= nil then
				forLines += 1
			end
		end
		assert(forLines == 7, "an always-returning loop inside a loop body lost its native for loop")
		local function check(initial: any, limit: any, expected: { any })
			local results = table.pack(exported(initial, limit))
			assert(results.n == 7, "always-returning loops inside loop bodies changed the result count")
			for index = 1, 7 do
				assert(results[index] == expected[index], "always-returning loops inside loop bodies changed a result")
			end
		end
		check(1, 3, { 1, 2, -1, 1, 3, 1, 2 })
		check(3, 1, { 3, 6, 3, 1, 3, 3, 2 })
		check(3, 3, { 3, 4, 3, 1, 3, 3, 4 })
		check(10, 3, { 3, 6, 3, 1, 3, 3, 4 })
		check(1, 7, { 1, 2, -1, 1, 3, 1, 2 })
		check(10, 7, { 3, 6, 3, 1, 3, 3, 5 })
	elseif caseName == "source-frontend-typed-block" then
		assert(exported(7) == 7, "source frontend changed typed block runtime behavior")
	elseif caseName == "source-frontend-numeric-for" then
		assert(string.find(source, "for index = initial, limit, step do", 1, true) ~= nil, "numeric-for emission lost the source binder")
		assert(string.find(source, "local index =", 1, true) == nil, "numeric-for emission restored a binder snapshot")
		assert(string.find(source, "local capture\n    capture = function", 1, true) == nil, "numeric-for closure declaration stayed split")
		local ascending, ascendingFirst, ascendingLast, ascendingFirstOnly, ascendingEmptyFirstOnly = exported("1", "3", "1")
		assert(ascending == 6, "source frontend changed numeric-for coercion or ascending induction")
		assert(ascendingFirst() == 1 and ascendingLast() == 3, "source frontend changed ascending iteration captures")
		assert(ascendingFirstOnly == 1 and ascendingEmptyFirstOnly == 0, "source frontend changed acyclic ascending or empty iteration")
		local descending, descendingFirst, descendingLast, descendingFirstOnly, descendingEmptyFirstOnly = exported(3, 1, -1)
		assert(descending == 6, "source frontend changed descending numeric-for induction")
		assert(descendingFirst() == 3 and descendingLast() == 1, "source frontend changed descending iteration captures")
		assert(descendingFirstOnly == 3 and descendingEmptyFirstOnly == 0, "source frontend changed acyclic descending or empty iteration")
		local empty, emptyFirst, emptyLast, emptyFirstOnly, emptyEmptyFirstOnly = exported(1, 0, 1)
		assert(empty == 0 and emptyFirst == nil and emptyLast == nil, "source frontend changed zero-iteration numeric-for behavior")
		assert(emptyFirstOnly == 0 and emptyEmptyFirstOnly == 0, "source frontend entered an empty acyclic numeric loop")
		local nanTotal, nanFirst, nanLast, nanFirstOnly, nanEmptyFirstOnly = exported(0 / 0, 3, 1)
		assert(nanTotal == 0 and nanFirst == nil and nanLast == nil, "source frontend changed numeric-for NaN behavior")
		assert(nanFirstOnly == 0 and nanEmptyFirstOnly == 0, "source frontend entered an acyclic NaN numeric loop")
	elseif caseName == "source-frontend-generic-for" then
		assert(string.find(source, "local index_2 = index", 1, true) == nil, "generic-for emission restored an index snapshot")
		assert(string.find(source, "local value_2 = value", 1, true) == nil, "generic-for emission restored a value snapshot")
		assert(string.find(source, ", nil, nil do", 1, true) == nil, "generic-for emission retained exact nil suffixes")
		assert(string.find(source, " in (", 1, true) ~= nil, "generic-for emission lost scalar-call grouping")
		local modeChainPreserved = string.find(source, "elseif mode == \"iter\" then", 1, true) ~= nil or
			string.match(source, "else\n%s*if mode == \"iter\" then") ~= nil
		assert(modeChainPreserved, "generic-for branch chain did not preserve its mode tests")
		local tableTotal, tableFirst, tableLast = exported("table")
		local tableFirstIndex, tableFirstValue = tableFirst()
		local tableLastIndex, tableLastValue = tableLast()
		assert(tableTotal == 69, "source frontend changed builtin-table iteration")
		assert(tableFirstIndex == 1 and tableFirstValue == 2, "source frontend changed the first builtin-table capture")
		assert(tableLastIndex == 3 and tableLastValue == 4, "source frontend changed the last builtin-table capture")
		local iterTotal, iterFirst, iterLast = exported("iter")
		local iterFirstIndex, iterFirstValue = iterFirst()
		local iterLastIndex, iterLastValue = iterLast()
		assert(iterTotal == 69, "source frontend changed __iter preparation")
		assert(iterFirstIndex == 1 and iterFirstValue == 2, "source frontend changed the first __iter capture")
		assert(iterLastIndex == 3 and iterLastValue == 4, "source frontend changed the last __iter capture")
		local callableTotal, callableFirst, callableLast = exported("callable")
		local callableFirstIndex, callableFirstValue = callableFirst()
		local callableLastIndex, callableLastValue = callableLast()
		assert(callableTotal == 72, "source frontend changed callable-object iteration")
		assert(callableFirstIndex == 1 and callableFirstValue == 2, "source frontend changed the first callable capture")
		assert(callableLastIndex == 3 and callableLastValue == 6, "source frontend changed the last callable capture")
		local factoryTotal, factoryFirst, factoryLast = exported("factory")
		local factoryFirstIndex, factoryFirstValue = factoryFirst()
		local factoryLastIndex, factoryLastValue = factoryLast()
		assert(factoryTotal == 1045, "source frontend changed final-call iterator tuple expansion or factory evaluation count")
		assert(factoryFirstIndex == 1 and factoryFirstValue == 7, "source frontend changed the first factory iterator capture")
		assert(factoryLastIndex == 2 and factoryLastValue == 8, "source frontend changed the last factory iterator capture")
		local singleTotal, singleFirst, singleLast = exported("single")
		local singleFirstIndex, singleFirstValue = singleFirst()
		local singleLastIndex, singleLastValue = singleLast()
		assert(singleTotal == 1012, "source frontend repeated an acyclic generalized iteration")
		assert(singleFirstIndex == 1 and singleFirstValue == 2, "source frontend changed the acyclic iterator value")
		assert(singleLastIndex == 1 and singleLastValue == 2, "source frontend changed the acyclic iterator capture")
		local segmentedTotal, segmentedFirst, segmentedLast = exported("segmented")
		local segmentedFirstIndex, segmentedFirstValue = segmentedFirst()
		local segmentedLastIndex, segmentedLastValue = segmentedLast()
		assert(segmentedTotal == 475, "source frontend lost native-loop initializer scope")
		assert(segmentedFirstIndex == 1 and segmentedFirstValue == 2, "source frontend changed the first grouped capture")
		assert(segmentedLastIndex == 3 and segmentedLastValue == 4, "source frontend changed the last grouped capture")
		local scalarTotal, scalarFirst, scalarLast = exported("scalar")
		local scalarFirstIndex, scalarFirstValue = scalarFirst()
		local scalarLastIndex, scalarLastValue = scalarLast()
		assert(scalarTotal == 45, "source frontend reopened a scalar iterator factory")
		assert(scalarFirstIndex == 1 and scalarFirstValue == 7, "source frontend changed the first scalar-factory capture")
		assert(scalarLastIndex == 2 and scalarLastValue == 8, "source frontend changed the last scalar-factory capture")
		local tripleTotal, tripleFirst, tripleLast = exported("triple")
		local tripleFirstIndex, tripleFirstValue = tripleFirst()
		local tripleLastIndex, tripleLastValue = tripleLast()
		assert(tripleTotal == 41, "source frontend changed explicit iterator-triple behavior")
		assert(tripleFirstIndex == 1 and tripleFirstValue == 5, "source frontend changed the first iterator-triple capture")
		assert(tripleLastIndex == 2 and tripleLastValue == 6, "source frontend changed the last iterator-triple capture")
	elseif caseName == "source-frontend-table-pack" then
		assert(string.find(source, "__lifter_pack_table_", 1, true) ~= nil, "source frontend did not preserve the ordered table pack write")
		local results = { exported("slot", 7, nil, 9) }
		assert(results[1] == 1 and results[2] == 2 and results[3] == 3, "source frontend changed fixed or expanded call fields")
		assert(results[4] == nil and results[5] == 5, "source frontend lost a call-pack nil hole or trailing value")
		assert(results[6] == "head" and results[7] == 7, "source frontend changed the vararg table prefix")
		assert(results[8] == nil and results[9] == 9, "source frontend lost a vararg nil hole or trailing value")
		assert(results[10] == "ok" and results[11] == 10, "source frontend changed mixed keyed/list fields")
		assert(results[12] == 3 and results[13] == nil and results[14] == 5, "source frontend changed mixed tail-pack overwrite or arity")
		assert(results[15] == "dynamic" and results[16] == "prefix", "source frontend changed ordered dynamic-key fields")
		assert(results[17] == 3 and results[18] == nil and results[19] == 5, "source frontend changed the ordered call pack")
	elseif caseName == "source-frontend-function-statement" then
		local doubled, added, tripled, originalOffset, mutableOffset = exported(3)
		assert(doubled == 6, "source frontend changed dotted function assignment")
		assert(added == 7, "source frontend changed method self binding")
		assert(tripled == 9, "source frontend changed nested function target evaluation")
		assert(originalOffset == 4, "source frontend changed the pre-reassignment function snapshot")
		assert(mutableOffset == 5, "source frontend changed the reassigned local function")
	elseif caseName == "source-frontend-interpolation" then
		local rendered, calls = exported(7)
		assert(string.byte(rendered, 1) == 0xff and string.byte(rendered, 2) == 0xfe, "source frontend changed string byte transport")
		assert(string.sub(rendered, 3) == "prefix %7 box:7 nil false suffix", "source frontend changed interpolation conversion or percent escaping")
		assert(calls == 1, "source frontend changed interpolation __tostring dispatch count")
	elseif caseName == "source-frontend-target-resolution" then
		assert(string.find(source, "local __lifter_pcall = pcall", 1, true) ~= nil, "target recovery did not emit the protected-call capability")
		assert(select(2, string.gsub(source, "__lifter_pcall%(", "")) == 3, "target recovery changed the resolved call count")
		local localStatus, localValue, groupedStatus, groupedValue, globalStatus, globalValue = exported(7)
		assert(localStatus == true and localValue == 14, "target recovery changed the local-alias call")
		assert(groupedStatus == true and groupedValue == 16, "target recovery changed the grouped-expression call")
		assert(globalStatus == true and globalValue == 18, "target recovery changed the direct-global call")
	elseif caseName == "source-frontend-opaque-result-target" then
		assert(
			string.find(source, "unresolvedResultTarget(", 1, true) == nil,
			"opaque-result recovery retained the unresolved local callee"
		)
		local positiveStatus, positiveValue, positiveProviderCalls = exported(7)
		assert(positiveStatus == true and positiveValue == 14, "opaque-result recovery changed protected-call behavior")
		assert(positiveProviderCalls == 1, "opaque-result recovery skipped or duplicated its producer call")
		local negativeStatus, negativeValue, negativeProviderCalls = exported(-3)
		assert(negativeStatus == true and negativeValue == -6, "opaque-result recovery changed repeated target behavior")
		assert(negativeProviderCalls == 1, "opaque-result recovery re-evaluated its producer call")
	elseif caseName == "source-frontend-nonintrinsic-target-origin" then
		assert(string.find(source, "unresolvedValue(", 1, true) == nil, "value-origin recovery retained the unresolved call target")
		assert(string.find(source, "unresolvedPlace(", 1, true) == nil, "place-origin recovery retained the unresolved call target")
		assert(string.find(source, "unresolvedEnvironment(", 1, true) == nil, "environment-origin recovery retained the unresolved call target")
		assert(string.find(source, "unresolvedLocalFunction(", 1, true) == nil, "local-function recovery retained the unresolved call target")
		assert(string.find(source, "unresolvedConditional(", 1, true) == nil, "conditional recovery retained the unresolved call target")
		assert(string.find(source, "unresolvedConditionalExpression(", 1, true) == nil, "conditional-expression recovery retained the unresolved call target")
		assert(select(2, string.gsub(source, "not useFirst", "")) == 2, "logical-not recovery erased a source condition")
		local valueTag, valueResult, placeTag, placeResult, environmentTag, environmentResult,
			localFunctionTag, localFunctionResult, conditionalTag, conditionalResult,
			conditionalExpressionTag, conditionalExpressionResult = exported(10)
		assert(valueTag == "value" and valueResult == 11, "target recovery changed the immutable local value origin")
		assert(placeTag == "place" and placeResult == 12, "target recovery changed the current local place origin")
		assert(environmentTag == "environment" and environmentResult == 13, "target recovery changed the environment origin")
		assert(localFunctionTag == "local-function" and localFunctionResult == 14, "target recovery changed the local-function allocation origin")
		assert(conditionalTag == "conditional-true" and conditionalResult == 15, "target recovery changed the logical-not conditional origin")
		assert(conditionalExpressionTag == "conditional-expression-false" and conditionalExpressionResult == 18, "target recovery changed the logical-not conditional-expression origin")
		local _, negativeValue, _, negativePlace, _, negativeEnvironment,
			negativeLocalFunctionTag, negativeLocalFunction, negativeConditionalTag, negativeConditional,
			negativeConditionalExpressionTag, negativeConditionalExpression = exported(-2)
		assert(
			negativeValue == -1
				and negativePlace == 0
				and negativeEnvironment == 1
				and negativeLocalFunctionTag == "local-function"
				and negativeLocalFunction == 2
				and negativeConditionalTag == "conditional-true"
				and negativeConditional == 3
				and negativeConditionalExpressionTag == "conditional-expression-false"
				and negativeConditionalExpression == 6,
			"target recovery changed repeated origin reads"
		)
	elseif caseName == "source-frontend-access-path-target-origin" then
		assert(string.find(source, "unresolvedValue(", 1, true) == nil, "table-value recovery retained the unresolved call target")
		assert(string.find(source, "unresolvedPlace(", 1, true) == nil, "table-place recovery retained the unresolved call target")
		assert(string.find(source, "unresolvedEnvironment(", 1, true) == nil, "environment-table recovery retained the unresolved call target")
		local valueTag, valueResult, placeTag, placeResult, environmentTag, environmentResult = exported(10)
		assert(valueTag == "value" and valueResult == 11, "target recovery changed the immutable table access origin")
		assert(placeTag == "place" and placeResult == 12, "target recovery changed the current table-place access origin")
		assert(environmentTag == "environment" and environmentResult == 13, "target recovery changed the environment-table access origin")
		local _, negativeValue, _, negativePlace, _, negativeEnvironment = exported(-2)
		assert(negativeValue == -1 and negativePlace == 0 and negativeEnvironment == 1, "target recovery changed repeated table access reads")
	elseif caseName == "source-frontend-dynamic-key-target-origin" then
		assert(string.find(source, "unresolvedValue(", 1, true) == nil, "dynamic value-key recovery retained the unresolved call target")
		assert(string.find(source, "unresolvedPlace(", 1, true) == nil, "dynamic place-key recovery retained the unresolved call target")
		assert(string.find(source, "unresolvedEnvironment(", 1, true) == nil, "dynamic environment-key recovery retained the unresolved call target")
		assert(string.find(source, "unresolvedExpression(", 1, true) == nil, "computed-key recovery retained the unresolved call target")
		local valueTag, valueResult, placeTag, placeResult, environmentTag, environmentResult, expressionTag, expressionResult = exported(10)
		assert(valueTag == "value-key" and valueResult == 11, "target recovery changed the immutable dynamic key origin")
		assert(placeTag == "place-key" and placeResult == 12, "target recovery changed the current dynamic place key origin")
		assert(environmentTag == "environment-key" and environmentResult == 13, "target recovery changed the environment dynamic key origin")
		assert(expressionTag == "expression-key" and expressionResult == 14, "target recovery changed the computed dynamic key origin")
		local _, negativeValue, _, negativePlace, _, negativeEnvironment, negativeExpressionTag, negativeExpression = exported(-2)
		assert(negativeValue == -1 and negativePlace == 0 and negativeEnvironment == 1, "target recovery changed repeated dynamic key reads")
		assert(negativeExpressionTag == "expression-key" and negativeExpression == 2, "target recovery changed repeated computed key reads")
	elseif caseName == "source-frontend-namecall-target-origin" then
		assert(string.find(source, "unresolvedValue:dispatch(", 1, true) == nil, "namecall value recovery retained the unresolved receiver")
		assert(string.find(source, "unresolvedPlace:dispatch(", 1, true) == nil, "namecall place recovery retained the unresolved receiver")
		assert(string.find(source, "unresolvedEnvironment:dispatch(", 1, true) == nil, "namecall environment recovery retained the unresolved receiver")
		local valueTag, valueResult, placeTag, placeResult, environmentTag, environmentResult, order = exported(10)
		assert(valueTag == "value-receiver" and valueResult == 11, "target recovery changed the immutable namecall receiver")
		assert(placeTag == "place-receiver" and placeResult == 12, "target recovery changed the current namecall receiver place")
		assert(environmentTag == "environment-receiver" and environmentResult == 13, "target recovery changed the environment namecall receiver")
		assert(order == "amcamcamc", "target recovery changed argument, method-resolution, call order, or self identity")
		local _, negativeValue, _, negativePlace, _, negativeEnvironment, negativeOrder = exported(-2)
		assert(negativeValue == -1 and negativePlace == 0 and negativeEnvironment == 1, "target recovery changed repeated namecall receiver reads")
		assert(negativeOrder == "amcamcamc", "target recovery duplicated a receiver or changed repeated NAMECALL order")
	elseif caseName == "source-frontend-compositional-access-path" then
		assert(string.find(source, "unresolvedValue(", 1, true) == nil, "compositional value path retained the unresolved callee")
		assert(string.find(source, "unresolvedPlace(", 1, true) == nil, "compositional place path retained the unresolved callee")
		assert(string.find(source, "unresolvedEnvironment(", 1, true) == nil, "compositional environment path retained the unresolved callee")
		assert(string.find(source, "unresolvedLiteral(", 1, true) == nil, "compositional literal path retained the unresolved callee")
		assert(string.find(source, "unresolvedReceiver:dispatch(", 1, true) == nil, "compositional receiver path retained the unresolved receiver")
		local valueTag, valueResult, placeTag, placeResult, environmentTag, environmentResult, literalTag, literalResult,
			receiverTag, receiverResult, receiverOrder, directTag, directResult, directOrder,
			directReceiverTag, directReceiverResult, directReceiverOrder = exported(10)
		assert(valueTag == "value-path" and valueResult == 11, "target recovery changed the immutable compositional path")
		assert(placeTag == "place-path" and placeResult == 12, "target recovery changed the mutable compositional path")
		assert(environmentTag == "environment-path" and environmentResult == 13, "target recovery changed the environment compositional path")
		assert(literalTag == "literal-path" and literalResult == 15, "target recovery changed the literal-key compositional path")
		assert(receiverTag == "receiver-path" and receiverResult == 14, "target recovery changed the compositional namecall receiver")
		assert(receiverOrder == "amc", "target recovery changed alias-backed receiver, argument, method resolution, or self order")
		assert(directTag == "direct-path" and directResult == 16, "target recovery changed the direct table-get callee")
		assert(directOrder == "tad", "target recovery duplicated a direct callee read or changed its argument order")
		assert(
			directReceiverTag == "direct-receiver-path" and directReceiverResult == 17,
			"target recovery changed the direct access-path namecall receiver"
		)
		assert(directReceiverOrder == "ramc", "target recovery duplicated a direct receiver or changed NAMECALL order")
		local _, negativeValue, _, negativePlace, _, negativeEnvironment, _, negativeLiteral, _, negativeReceiver,
			negativeReceiverOrder, _, negativeDirect, negativeDirectOrder, _, negativeDirectReceiver,
			negativeDirectReceiverOrder = exported(-2)
		assert(
			negativeValue == -1
				and negativePlace == 0
				and negativeEnvironment == 1
				and negativeLiteral == 3
				and negativeReceiver == 2
				and negativeDirect == 4
				and negativeDirectReceiver == 5,
			"target recovery changed repeated compositional path reads"
		)
		assert(negativeReceiverOrder == "amc", "target recovery duplicated an alias-backed namecall receiver")
		assert(negativeDirectOrder == "tad", "target recovery duplicated a repeated direct callee read")
		assert(negativeDirectReceiverOrder == "ramc", "target recovery duplicated a repeated direct namecall receiver")
	elseif caseName == "source-frontend-temporal-target-identity" then
		assert(string.find(source, "unresolvedJoined(", 1, true) == nil, "temporal alias join retained the unresolved callee")
		assert(string.find(source, "unresolvedPrecommit(", 1, true) == nil, "temporal assignment commit retained the unresolved callee")
		assert(string.find(source, "unresolvedForHeader(", 1, true) == nil, "temporal for header retained the unresolved callee")
		assert(string.find(source, "unresolvedGuard(", 1, true) == nil, "temporal guard retained the unresolved callee")
		assert(string.find(source, "unresolvedLoopFixed(", 1, true) == nil, "temporal loop fixed point retained the unresolved callee")
		assert(string.find(source, "unresolvedBreakFixed(", 1, true) == nil, "temporal break exit retained the unresolved callee")
		assert(string.find(source, "unresolvedContinueFixed(", 1, true) == nil, "temporal continue backedge retained the unresolved callee")
		assert(string.find(source, "unresolvedImmediate(", 1, true) == nil, "temporal immediate invocation retained the unresolved callee")
		assert(string.find(source, "unresolvedInnerFuture(", 1, true) == nil, "temporal invocation-local future write retained the unresolved callee")
		assert(string.find(source, "unresolvedNestedWrite(", 1, true) == nil, "temporal nested direct invocation retained the unresolved callee")
		assert(string.find(source, "unresolvedReadChain(", 1, true) == nil, "temporal nested invocation read chain retained the unresolved callee")
		assert(string.find(source, "unresolvedLocalInvoke(", 1, true) == nil, "temporal single-use local invocation retained the unresolved callee")
		assert(string.find(source, "unresolvedLocalFunction(", 1, true) == nil, "temporal single-use local function retained the unresolved callee")
		assert(string.find(source, "unresolvedAssignedInvoke(", 1, true) == nil, "temporal assigned closure retained the unresolved callee")
		assert(string.find(source, "unresolvedAliasedInvoke(", 1, true) == nil, "temporal aliased closure retained the unresolved callee")
		assert(string.find(source, "unresolvedCapturedInvoke(", 1, true) == nil, "temporal captured closure retained the unresolved callee")
		local snapshotTag, snapshotValue, mutableTag, mutableValue, joinedTag, joinedValue, precommitTag, precommitValue, headerTotal,
			guardResult, reads, loopTag, loopValue, breakTag, breakValue, continueTag, continueValue, transferSteps, loopPhaseCalls,
			immediateTag, immediateValue, innerFutureTag, innerFutureValue, nestedWriteTag, nestedWriteValue, readChainTag,
			readChainValue, localInvokeTag, localInvokeValue, localFunctionTag, localFunctionValue,
			assignedInvokeTag, assignedInvokeValue, aliasedInvokeTag, aliasedInvokeValue, capturedInvokeTag, capturedInvokeValue = exported(10)
		assert(snapshotTag == "snapshot" and snapshotValue == 11, "temporal recovery re-evaluated or changed the immutable target snapshot")
		assert(mutableTag == "mutable" and mutableValue == 12, "temporal recovery changed the uniquely reaching mutable target")
		assert(joinedTag == "joined" and joinedValue == 13, "temporal recovery changed the compositional alias identity")
		assert(precommitTag == "precommit" and precommitValue == 14, "temporal recovery changed assignment pre-commit identity")
		assert(headerTotal == 10, "temporal recovery changed one-time numeric for header identity")
		assert(guardResult == "positive", "temporal recovery changed positive structured guard identity")
		assert(reads == 1, "temporal recovery duplicated the effectful target lookup")
		assert(loopTag == "loop-fixed" and loopValue == 15, "temporal recovery changed the convergent loop-carried identity")
		assert(breakTag == "transfer-fixed" and breakValue == 16, "temporal recovery changed the break-exit identity")
		assert(continueTag == "transfer-fixed" and continueValue == 16, "temporal recovery changed the continue-backedge identity")
		assert(transferSteps == 3, "temporal recovery changed break or continue execution")
		assert(loopPhaseCalls == 3, "temporal recovery changed first or later while-condition target evaluation")
		assert(immediateTag == "immediate" and immediateValue == 17, "temporal recovery changed synchronous invocation identity")
		assert(innerFutureTag == "inner-future" and innerFutureValue == 18, "temporal recovery changed invocation-local future-write identity")
		assert(nestedWriteTag == "nested-write" and nestedWriteValue == 19, "temporal recovery changed nested direct-invocation identity")
		assert(readChainTag == "read-chain" and readChainValue == 20, "temporal recovery changed nested direct-invocation read identity")
		assert(localInvokeTag == "local-invoke" and localInvokeValue == 21, "temporal recovery changed single-use local invocation identity")
		assert(localFunctionTag == "local-function" and localFunctionValue == 22, "temporal recovery changed single-use local function identity")
		assert(assignedInvokeTag == "assigned-invoke" and assignedInvokeValue == 23, "temporal recovery changed assigned closure identity")
		assert(aliasedInvokeTag == "alias-invoke" and aliasedInvokeValue == 24, "temporal recovery changed aliased closure identity")
		assert(capturedInvokeTag == "capture-invoke" and capturedInvokeValue == 25, "temporal recovery changed captured closure identity")
		local negativeSnapshotTag, negativeSnapshotValue, negativeMutableTag, negativeMutableValue, negativeJoinedTag, negativeJoinedValue,
			negativePrecommitTag, negativePrecommitValue, negativeHeaderTotal, negativeGuardResult, negativeReads, negativeLoopTag,
			negativeLoopValue, negativeBreakTag, negativeBreakValue, negativeContinueTag, negativeContinueValue, negativeTransferSteps,
			negativeLoopPhaseCalls, negativeImmediateTag, negativeImmediateValue, negativeInnerFutureTag, negativeInnerFutureValue,
			negativeNestedWriteTag, negativeNestedWriteValue, negativeReadChainTag, negativeReadChainValue,
			negativeLocalInvokeTag, negativeLocalInvokeValue, negativeLocalFunctionTag, negativeLocalFunctionValue,
			negativeAssignedInvokeTag, negativeAssignedInvokeValue, negativeAliasedInvokeTag, negativeAliasedInvokeValue,
			negativeCapturedInvokeTag, negativeCapturedInvokeValue = exported(-2)
		assert(
			negativeSnapshotTag == "snapshot" and negativeSnapshotValue == -1,
			"temporal recovery changed repeated immutable snapshot behavior"
		)
		assert(
			negativeMutableTag == "mutable" and negativeMutableValue == 0 and negativeReads == 1,
			"temporal recovery changed repeated mutable target behavior"
		)
		assert(
			negativeJoinedTag == "joined" and negativeJoinedValue == 1,
			"temporal recovery changed the alternate compositional alias identity"
		)
		assert(
			negativePrecommitTag == "precommit" and negativePrecommitValue == 2,
			"temporal recovery changed repeated assignment pre-commit identity"
		)
		assert(negativeHeaderTotal == -2, "temporal recovery changed repeated numeric for header identity")
		assert(negativeGuardResult == "negative", "temporal recovery changed alternate structured guard identity")
		assert(
			negativeLoopTag == "loop-fixed" and negativeLoopValue == 3,
			"temporal recovery changed the zero-iteration loop-carried identity"
		)
		assert(
			negativeBreakTag == "transfer-fixed" and negativeBreakValue == 4,
			"temporal recovery changed the repeated break-exit identity"
		)
		assert(
			negativeContinueTag == "transfer-fixed" and negativeContinueValue == 4,
			"temporal recovery changed the zero-iteration continue identity"
		)
		assert(negativeTransferSteps == 1, "temporal recovery changed alternate break or continue execution")
		assert(negativeLoopPhaseCalls == 1, "temporal recovery changed zero-iteration while-condition target evaluation")
		assert(
			negativeImmediateTag == "immediate" and negativeImmediateValue == 5,
			"temporal recovery changed repeated synchronous invocation identity"
		)
		assert(
			negativeInnerFutureTag == "inner-future" and negativeInnerFutureValue == 6,
			"temporal recovery changed repeated invocation-local future-write identity"
		)
		assert(
			negativeNestedWriteTag == "nested-write" and negativeNestedWriteValue == 7,
			"temporal recovery changed repeated nested direct-invocation identity"
		)
		assert(
			negativeReadChainTag == "read-chain" and negativeReadChainValue == 8,
			"temporal recovery changed repeated nested direct-invocation read identity"
		)
		assert(
			negativeLocalInvokeTag == "local-invoke" and negativeLocalInvokeValue == 9,
			"temporal recovery changed repeated single-use local invocation identity"
		)
		assert(
			negativeLocalFunctionTag == "local-function" and negativeLocalFunctionValue == 10,
			"temporal recovery changed repeated single-use local function identity"
		)
		assert(
			negativeAssignedInvokeTag == "assigned-invoke" and negativeAssignedInvokeValue == 11,
			"temporal recovery changed repeated assigned closure identity"
		)
		assert(
			negativeAliasedInvokeTag == "alias-invoke" and negativeAliasedInvokeValue == 12,
			"temporal recovery changed repeated aliased closure identity"
		)
		assert(
			negativeCapturedInvokeTag == "capture-invoke" and negativeCapturedInvokeValue == 13,
			"temporal recovery changed repeated captured closure identity"
		)
	elseif caseName == "source-frontend-intrinsic-invocation" then
		assert(string.find(source, "local __lifter_pcall = pcall", 1, true) ~= nil, "intrinsic frontend did not capture pcall")
		assert(string.find(source, "local __lifter_xpcall = xpcall", 1, true) ~= nil, "intrinsic frontend did not capture xpcall")
		assert(string.find(source, "local __lifter_coroutine_create = coroutine.create", 1, true) ~= nil, "intrinsic frontend did not capture coroutine.create")
		assert(string.find(source, "local __lifter_coroutine_resume = coroutine.resume", 1, true) ~= nil, "intrinsic frontend did not capture coroutine.resume")
		assert(string.find(source, "local __lifter_coroutine_yield = coroutine.yield", 1, true) ~= nil, "intrinsic frontend did not capture coroutine.yield")
		assert(string.find(source, "local __lifter_error = error", 1, true) ~= nil, "intrinsic frontend did not capture error")
		assert(string.find(source, "local __lifter_rawset = rawset", 1, true) ~= nil, "ordered table packs did not capture rawset")
		assert(string.find(source, "local __lifter_select = select", 1, true) ~= nil, "ordered table packs did not capture select")
		assert(string.find(source, "local constructorTailPack_", 1, true) == nil, "ordered table pack retained a projected producer alias")
		assert(select(2, string.gsub(source, "__lifter_pcall%(", "")) == 19, "intrinsic frontend changed native pcall count")
		assert(select(2, string.gsub(source, "__lifter_xpcall%(", "")) == 2, "intrinsic frontend changed native xpcall count")
		assert(select(2, string.gsub(source, "__lifter_coroutine_create%(", "")) == 9, "intrinsic frontend changed native create count")
		assert(select(2, string.gsub(source, "__lifter_coroutine_resume%(", "")) == 5, "intrinsic frontend changed native resume count")
		assert(select(2, string.gsub(source, "__lifter_coroutine_yield%(", "")) == 3, "intrinsic frontend changed native yield count")
		assert(select(2, string.gsub(source, "__lifter_error%(", "")) == 25, "intrinsic frontend changed promoted error count")
		assert(string.find(source, "dead-dynamic-error", 1, true) == nil, "dead dynamic-level error reached readable output")
		assert(string.find(source, "nonpositive-dynamic-error", 1, true) ~= nil, "proved nonpositive error was lost")
		assert(string.match(source, "\n([ \t]*)else\n%1end\n") == nil, "loop-terminal emission retained an empty else arm")
		assert(select(2, string.gsub(source, "coroutine%.create%(worker%)", "")) == 0, "proven coroutine.create retained a mutable lookup")
	
		local result = exported()
		assert(type(result) == "table", "intrinsic source fixture did not return its result table")
		assert(result.discarded_calls == 1, "discarded protected call did not execute exactly once")
		assert(result.ordered_error_status == false and result.ordered_error_identity == true, "promoted error changed protected object identity")
		assert(result.ordered_error_effects == "mx", "promoted error changed argument effect order")
		assert(result.omitted_error_status == false and result.omitted_error_identity == true, "omitted error level changed object identity")
		assert(result.dynamic_level_status == false and result.dynamic_level_identity == true, "numeric dynamic error level changed object identity")
		assert(
			result.nonpositive_level_status == false and result.nonpositive_level_value == "nonpositive-dynamic-error",
			"proved nonpositive dynamic error level changed its exact message"
		)
		assert(result.return_termination_status == false and result.return_termination_identity == true, "return-list error lost nonreturning identity")
		assert(result.return_termination_effects == "am", "return-list error did not stop later values")
		assert(result.argument_termination_status == false and result.argument_termination_identity == true, "argument error lost nonreturning identity")
		assert(result.argument_termination_effects == "!bn", "argument error changed callee/argument order or called the outer value")
		assert(result.aggregate_termination_status == false and result.aggregate_termination_identity == true, "aggregate error lost nonreturning identity")
		assert(result.aggregate_termination_effects == "tie", "table or interpolation error did not stop later fields")
		local constructorKeys = result.constructor_key
		assert(type(constructorKeys) == "table", "constructor-key observations were not grouped")
		local nilKey = constructorKeys.nil_key
		local nanKey = constructorKeys.nan_key
		assert(type(nilKey) == "table" and type(nanKey) == "table", "constructor-key domains were not grouped")
		assert(nilKey.status == false and nilKey.identity == false, "nil constructor key lost its own error identity")
		assert(nilKey.effects == "kv", "nil constructor key changed its value evaluation or evaluated a later field")
		assert(nanKey.status == false and nanKey.identity == false, "NaN constructor key lost its own error identity")
		assert(nanKey.effects == "nv", "NaN constructor key changed its value evaluation or evaluated a later field")
		local constructorTail = constructorKeys.tail
		assert(type(constructorTail) == "table", "ordered constructor-tail observations were not grouped")
		local nilTail = constructorTail.nil_key
		local zeroTail = constructorTail.zero
		local oneTail = constructorTail.one
		local manyTail = constructorTail.many
		assert(
			type(nilTail) == "table" and type(zeroTail) == "table" and type(oneTail) == "table" and type(manyTail) == "table",
			"ordered constructor-tail domains were not grouped"
		)
		assert(nilTail.status == false and nilTail.identity == false, "nil key before an open tail lost its own error identity")
		assert(nilTail.effects == "kv", "nil key evaluated the final open tail")
		assert(zeroTail.status == true and zeroTail.effects == "kvt", "zero-result constructor tail changed evaluation order")
		assert(
			type(zeroTail.value) == "table" and zeroTail.value[1] == "prefix" and zeroTail.value[2] == "keyed",
			"zero-result constructor tail performed a synthetic nil write"
		)
		assert(oneTail.status == true and oneTail.effects == "kvt", "one-result constructor tail changed evaluation order")
		assert(
			type(oneTail.value) == "table" and oneTail.value[1] == "prefix" and oneTail.value[2] == "one" and oneTail.value[3] == "keyed",
			"one-result constructor tail changed its exact write count"
		)
		assert(manyTail.status == true and manyTail.effects == "kvt", "many-result constructor tail changed evaluation order")
		assert(
			type(manyTail.value) == "table"
				and manyTail.value[1] == "prefix"
				and manyTail.value[2] == "many-a"
				and manyTail.value[3] == nil
				and manyTail.value[4] == "many-c",
			"many-result constructor tail changed its interior nil hole"
		)
		local constructorVarargs = constructorKeys.varargs
		assert(type(constructorVarargs) == "table" and constructorVarargs.effects == "kv", "ordered vararg constructor changed key/value order")
		local varargValue = constructorVarargs.value
		assert(
			type(varargValue) == "table"
				and varargValue[1] == "vararg-prefix"
				and varargValue[2] == "vararg-a"
				and varargValue[3] == nil
				and varargValue[4] == "vararg-c",
			"ordered vararg constructor changed its open pack or nil hole"
		)
		assert(result.arithmetic_termination_status == false and result.arithmetic_termination_identity == true, "arithmetic error lost nonreturning identity")
		assert(result.arithmetic_termination_effects == "lr", "binary or unary error changed operand order")
		assert(result.assignment_target_status == false and result.assignment_target_identity == true, "assignment-target error lost nonreturning identity")
		assert(result.assignment_target_effects == "p", "assignment-target error evaluated its key or right side")
		assert(result.assignment_value_status == false and result.assignment_value_identity == true, "assignment-value error lost nonreturning identity")
		assert(result.assignment_value_effects == "vm", "assignment-value error evaluated later values or writes")
		assert(result.numeric_loop_status == false and result.numeric_loop_identity == true, "numeric-bound error lost nonreturning identity")
		assert(result.numeric_loop_effects == "fl", "numeric-bound error evaluated its step, body, or continuation")
		assert(result.generic_loop_status == false and result.generic_loop_identity == true, "generic-source error lost nonreturning identity")
		assert(result.generic_loop_effects == "gh", "generic-source error evaluated later iterator values or its body")
		assert(result.short_throw_status == false and result.short_throw_identity == true and result.short_throw_effects == "c", "short-circuit throw branch changed control or identity")
		assert(result.short_survive_status == true and result.short_survive_effects == "s", "short-circuit surviving branch did not reach its join")
		local repeats = result.repeat_reachability
		assert(type(repeats) == "table", "repeat reachability observations were not grouped")
		assert(repeats.break_status == true and repeats.break_effects == "", "repeat break evaluated an unreachable terminating latch")
		assert(repeats.no_break_status == false and repeats.no_break_identity == true and repeats.no_break_effects == "ru", "terminating no-break repeat retained later effects")
		assert(repeats.conditional_exit_status == true and repeats.conditional_exit_effects == "ba", "conditional break did not preserve the repeat exit")
		assert(repeats.conditional_throw_status == false and repeats.conditional_throw_identity == true and repeats.conditional_throw_effects == "bu", "conditional non-break path changed latch termination")
		assert(repeats.nested_status == false and repeats.nested_identity == true and repeats.nested_effects == "nu", "nested break incorrectly preserved the outer repeat exit")
		assert(repeats.continue_exit_status == true and repeats.continue_exit_effects == "cla", "conditional continue did not preserve the reachable latch and exit")
		assert(repeats.continue_throw_status == false and repeats.continue_throw_identity == true and repeats.continue_throw_effects == "ct", "conditional non-continue path changed body termination")
		assert(repeats.nested_continue_status == false and repeats.nested_continue_identity == true and repeats.nested_continue_effects == "nt", "nested continue incorrectly preserved the outer repeat latch")
		assert(result.exact_open_status == false and result.exact_open_value_type == "thread", "exact-one open error lost its producer value or termination")
		assert(result.unresolved_open_status == false and result.unresolved_open_value == true, "variable-result open error was specialized without exact shape")
		assert(result.alias_pcall_status == true and result.alias_pcall_label == "alias" and result.alias_pcall_value == 9, "immutable protected-call alias lost results")
		assert(result.alias_thread_type == "thread" and result.alias_extra == nil, "immutable exact-one alias lost result shape")
		assert(result.alias_error_status == false and result.alias_error_identity == true, "captured error alias lost object identity")
		assert(result.alias_exact_status == false and result.alias_exact_value_type == "thread", "error alias lost exact open-tail termination")
		assert(result.mutable_alias_result == "replacement:ok", "mutable intrinsic alias retained stale identity")
		assert(result.if_join_status == true and result.if_join_label == "if-join" and result.if_join_value == 10, "matching if-expression identity was lost")
		assert(result.short_join_status == true and result.short_join_label == "short-join" and result.short_join_value == 11, "matching short-circuit identity was lost")
		assert(result.surviving_join_status == true and result.surviving_join_label == "surviving-join" and result.surviving_join_value == 12, "sole surviving join identity was lost")
		assert(result.joined_throw_status == false and result.joined_throw_identity == true, "terminating join branch lost error identity")
		assert(result.mismatch_pcall_status == true and result.mismatch_pcall_label == "mismatch" and result.mismatch_pcall_value == 13, "mismatched pcall branch changed behavior")
		assert(result.mismatch_xpcall_status == false and result.mismatch_xpcall_message == "handled:mismatch-error", "mismatched xpcall branch changed behavior")
		assert(result.fixed_pcall_status == true, "fixed pcall lost its status")
		assert(result.open_pcall_status == true, "open pcall lost its status")
		assert(result.open_pcall_label == "open" and result.open_pcall_value == 7, "open pcall changed fixed results")
		assert(result.open_pcall_hole == nil and result.open_pcall_tail == "tail:open", "open pcall changed a nil hole or tail")
		assert(result.fixed_xpcall_status == false, "fixed xpcall lost its failure status")
		assert(result.open_xpcall_status == false and result.open_xpcall_message == "handled:open-error", "open xpcall changed handler semantics")
		assert(result.open_thread_type == "thread" and result.open_extra == nil, "open coroutine.create changed fixed arity")
		assert(result.returned_thread_type == "thread", "pack-values return changed coroutine.create")
		assert(result.argument_thread_type == "thread", "pack-values invocation argument changed coroutine.create")
		assert(result.table_thread_type == "thread", "pack-values table tail changed coroutine.create")
		assert(result.fixed_resume_status == true, "fixed coroutine.resume lost its status")
		assert(result.second_status == true and result.second_tag == "open-yield", "open resume changed the second suspension")
		assert(result.second_reply == "reply-one" and result.second_tail_a == "tail-a", "open yield changed its fixed or open arguments")
		assert(result.second_tail_hole == nil and result.second_tail_c == "tail-c", "open yield changed its nil hole or tail")
		assert(result.final_status == true and result.final_tag == "done", "final resume changed coroutine completion")
		assert(result.final_first == "resume-a" and result.final_hole == nil and result.final_third == "resume-c", "final resume changed its result pack")
		local protectedYield = result.protected_yield
		assert(type(protectedYield) == "table", "protected suspension observations were not grouped")
		local protectedSuccess = protectedYield.success
		local protectedFailure = protectedYield.failure
		assert(type(protectedSuccess) == "table" and type(protectedFailure) == "table", "protected suspension paths were not grouped")
		assert(protectedSuccess.first_status == true and protectedSuccess.first_tag == "protected-yield", "protected call did not suspend through coroutine.yield")
		assert(
			protectedSuccess.first_head == "protected-head"
				and protectedSuccess.first_hole == nil
				and protectedSuccess.first_tail == 31,
			"protected suspension changed its initial open argument pack"
		)
		assert(
			protectedSuccess.final_status == true
				and protectedSuccess.call_status == true
				and protectedSuccess.return_tag == "protected-return",
			"protected invocation did not complete after resumption"
		)
		assert(
			protectedSuccess.reply == "protected-reply"
				and protectedSuccess.reply_hole == nil
				and protectedSuccess.reply_tail == 37,
			"protected resumption changed its open result pack"
		)
		assert(protectedFailure.first_status == true and protectedFailure.first_tag == "protected-yield", "failing protected call did not reach its suspension")
		assert(
			protectedFailure.final_status == true
				and protectedFailure.call_status == false
				and protectedFailure.failure_identity == true,
			"protected error escaped after coroutine resumption"
		)
	elseif caseName == "source-frontend-coroutine-wrap" then
		assert(string.find(source, "__lifter_coroutine_wrap", 1, true) == nil, "generic coroutine.wrap became a synthetic capability")
		local wrapped = exported()
		assert(type(wrapped) == "table", "wrapped coroutine observations were not grouped")
		assert(wrapped.effects == "sr", "wrapped coroutine changed suspension effect order")
		assert(
			wrapped.first_tag == "wrapped-yield"
				and wrapped.first_head == "wrapped-head"
				and wrapped.first_hole == nil
				and wrapped.first_tail == 41,
			"wrapped coroutine changed its initial open argument or yield pack"
		)
		assert(
			wrapped.final_tag == "wrapped-done"
				and wrapped.final_reply == "wrapped-reply"
				and wrapped.final_hole == nil
				and wrapped.final_tail == 43,
			"wrapped coroutine changed its resumed result pack"
		)
		assert(wrapped.dead_status == false and wrapped.dead_error_type == "string", "wrapped dead coroutine did not rethrow")
		assert(
			wrapped.failure_tag == "wrapped-failure-yield"
				and wrapped.failure_status == false
				and wrapped.failure_error_type == "string",
			"wrapped coroutine did not convert its worker failure into a thrown string"
		)
	else
		return false
	end
	return true
end

return table.freeze(SourceRuntimeOracle)
