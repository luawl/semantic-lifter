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
	elseif caseName == "source-frontend-binary-operand-read-order" or caseName == "source-frontend-binary-operand-read-order-direct-locals" then
		local sum, grouped, equal, ordered, steps, loopFirst, loopSecond, parameter, metamethod, first, second, joined, snapshot =
			exported(10, 4)
		assert(sum == 104, "source frontend read a register local arithmetic operand before the right operand ran")
		assert(grouped == 500, "source frontend read a grouped register local operand before the right operand ran")
		assert(equal == true and ordered == false, "source frontend read a register local comparison operand before the right operand ran")
		assert(steps == 1, "source frontend read a loop-condition register local before the right operand ran")
		assert(loopFirst == 100 and loopSecond == 100, "source frontend read a per-iteration register local before the right operand ran")
		assert(parameter == 100, "source frontend read a register parameter operand before the right operand ran")
		assert(metamethod == 104, "source frontend read a register local before a metamethod in the right operand ran")
		assert(first == 10 and second == 4, "source frontend changed Luau's in-order copy of generic call arguments")
		assert(joined == "104", "source frontend changed Luau's in-order copy of concatenation operands")
		assert(snapshot == 14, "source frontend changed Luau's upvalue snapshot in a child function")
	elseif caseName == "source-frontend-index-base-read-order" or caseName == "source-frontend-index-base-read-order-direct-locals" then
		local plain, arithmetic, grouped, metamethod, loopFirst, loopSecond, parameter, snapshot, constantKey, fieldTable =
			exported(3, 4)
		assert(plain == 100 and arithmetic == 200, "source frontend read a register local index table before the key ran")
		assert(grouped == 100, "source frontend read a grouped register local index table before the key ran")
		assert(metamethod == 100, "source frontend read a register local index table before a metamethod in the key ran")
		assert(loopFirst == 100 and loopSecond == 200, "source frontend read a per-iteration register local index table before the key ran")
		assert(parameter == 7, "source frontend read a register parameter index table before the key ran")
		assert(snapshot == 3, "source frontend changed Luau's upvalue snapshot of an index table in a child function")
		assert(constantKey == 4 and fieldTable == 3, "source frontend changed Luau's in-order index with a constant key or a field-read table")
	elseif caseName == "source-frontend-assignment-target-read-order" or caseName == "source-frontend-assignment-target-read-order-direct-locals" then
		local byName, byNumber, multiple, byKey, tableAndKey, ownTableWrite, ownKeyWrite, snapshot, fieldTable = exported("v")
		assert(byName == "nil/v" and byNumber == "nil/v", "source frontend read a register local assignment table before the value ran")
		assert(multiple == "nil/v,v!", "source frontend read a register local assignment table before a multiple assignment's values ran")
		assert(byKey == "nil/v", "source frontend read a register local assignment key before the value ran")
		assert(tableAndKey == "nil/nil,nil/v", "source frontend read a register local assignment table and key before the value ran")
		assert(ownTableWrite == "v/nil" and ownKeyWrite == "v/nil", "source frontend read an assignment table or key after the statement wrote it")
		assert(snapshot == "v/nil", "source frontend changed Luau's upvalue snapshot of an assignment table in a child function")
		assert(fieldTable == "v/nil", "source frontend changed Luau's in-order field-read assignment table")
	elseif caseName == "source-frontend-compound-table-target-read-order" or caseName == "source-frontend-compound-table-target-read-order-direct-locals" then
		local byName, byNumber, byKey, concat, metamethod, snapshot, plain = exported(1, 2)
		assert(byName == "1/3" and byNumber == "1/3", "source frontend stored a compound table target through a table read taken before the right-hand side ran")
		assert(byKey == "1/3", "source frontend stored a compound table target through a key read taken before the right-hand side ran")
		assert(concat == "p/pq", "source frontend stored a compound concatenation target through a table read taken before the right-hand side ran")
		assert(metamethod == "nil/3", "source frontend stored a compound table target through a table read taken before its current-value metamethod ran")
		assert(snapshot == "3/50", "source frontend changed Luau's single upvalue read of a compound table target in a child function")
		assert(plain == 3, "source frontend changed a compound table assignment")
	elseif caseName == "source-frontend-multiple-assignment-value-read-order" or caseName == "source-frontend-multiple-assignment-value-read-order-direct-locals" then
		local fieldLocal, twoFields, keyed, parameter, localTarget, snapshot, single, ownWrite = exported("old")
		assert(fieldLocal == "new/5" and twoFields == "new/5", "source frontend read a register local multiple-assignment table value before a later value ran")
		assert(keyed == "new/5", "source frontend read a register local multiple-assignment value of a keyed target before a later value ran")
		assert(parameter == "new/5", "source frontend read a register parameter multiple-assignment table value before a later value ran")
		assert(localTarget == "old/5", "source frontend changed Luau's in-order copy of a local target's value")
		assert(snapshot == "old/5", "source frontend changed Luau's upvalue snapshot of a multiple-assignment value in a child function")
		assert(single == "old", "source frontend changed a single table assignment")
		assert(ownWrite == "new/old", "source frontend read a table target's value after the statement wrote its own local")
	elseif caseName == "source-frontend-multiple-assignment-store-order" or caseName == "source-frontend-multiple-assignment-store-order-direct-locals" then
		local storeOperands, environment, upvalueStore, localTiming, controls, valueObservers, conflicts, orders, raisingStore, typeLevel, combined =
			exported("old")
		assert(storeOperands == "nil/2/nil/3/new", "source frontend read a later table store's register-local table, key or value before an earlier store ran")
		assert(environment == "GLOBAL_A=new;GLOBAL_B=new;new/nil/2/new", "source frontend misordered global and upvalue stores against the environment's __newindex")
		assert(upvalueStore == "new", "source frontend read an upvalue store's register-local value before an earlier store ran")
		assert(localTiming == "x=new;hook/last", "source frontend wrote a multiple assignment's local target at the wrong point")
		assert(controls == "old/nil/old", "source frontend changed Luau's value-time copy of a spread value or an upvalue store's place")
		assert(valueObservers == "new/new", "source frontend wrote a local target after a later value ran")
		assert(conflicts == "x=old/old;old=old/1;new", "source frontend wrote a conflicting local target before the stores")
		assert(orders == "x=old;old/new/new", "source frontend misordered a spread-covered local target or Luau's marking order")
		assert(raisingStore == "false/new/last/false/nil", "source frontend misordered local writes around a raising store")
		assert(typeLevel == "new/new/new/new/new/x=new;y=new;old", "source frontend counted a type-level name as a conflicting use")
		assert(combined == "x=new;new", "source frontend misordered an early local write against a later store's operand read")
	elseif caseName == "source-frontend-table-constructor-key-read-order" or caseName == "source-frontend-table-constructor-key-read-order-direct-locals" then
		local literal, ordered, grouped, parameter, snapshot, earlierItem, listItem = exported("a")
		assert(literal == "nil/1", "source frontend read a register local table constructor key before the item value ran")
		assert(ordered == "nil/1,2", "source frontend read a register local key of an ordered table constructor before the item value ran")
		assert(grouped == "nil/1", "source frontend read a grouped register local table constructor key before the item value ran")
		assert(parameter == "nil/1", "source frontend read a register parameter table constructor key before the item value ran")
		assert(snapshot == "1/nil", "source frontend changed Luau's upvalue snapshot of a table constructor key in a child function")
		assert(earlierItem == "1/2", "source frontend changed Luau's key read after an earlier item's call")
		assert(listItem == "old/new", "source frontend changed Luau's in-order copy of a table constructor list item")
	elseif caseName == "source-frontend-method-receiver-read-order" or caseName == "source-frontend-method-receiver-read-order-direct-locals" then
		local grouped, leading, wrapped, statement, repeated, loopFirst, loopSecond, fieldReceiver, snapshot = exported(2)
		assert(grouped == "new" and leading == "new" and wrapped == "new", "source frontend read a register local method receiver before the arguments ran")
		assert(statement == "0/1", "source frontend read a register local method receiver before a statement call's arguments ran")
		assert(repeated == "xyzxyz", "source frontend read a register local string receiver before the arguments ran")
		assert(loopFirst == "new1" and loopSecond == "new2", "source frontend read a per-iteration register local receiver before the arguments ran")
		assert(fieldReceiver == "old", "source frontend changed Luau's in-order field-read method receiver")
		assert(snapshot == "old", "source frontend changed Luau's upvalue snapshot of a method receiver in a child function")
	elseif caseName == "source-frontend-builtin-fastcall-read-order" or caseName == "source-frontend-builtin-fastcall-read-order-direct-locals" then
		local maximum, arithmetic, clamped, same, inserted, sub, aliased, openLast, generic, fourArguments, fieldCallee = exported(1)
		assert(maximum == 10 and arithmetic == 10 and clamped == 10, "source frontend read a register local builtin fast-call argument before a later argument ran")
		assert(same == true, "source frontend read a register local rawequal argument before a later argument ran")
		assert(inserted == "0/1" and sub == "xy", "source frontend read a register local library fast-call argument before a later argument ran")
		assert(aliased == 10, "source frontend read a register local argument of a builtin alias before a later argument ran")
		assert(openLast == 1 and generic == 1, "source frontend changed Luau's in-order copy of generic call arguments")
		assert(fourArguments == 1 and fieldCallee == 1, "source frontend treated a four-argument or field-read builtin call as a fast call")
	elseif caseName == "source-frontend-builtin-fastcall-optimize0" or caseName == "source-frontend-builtin-fastcall-optimize0-direct-locals" then
		local maximum, clamped, aliased = exported(1)
		assert(maximum == 1 and clamped == 1 and aliased == 1, "source frontend treated a builtin call as a fast call at optimisation level 0")
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
	elseif caseName == "source-frontend-always-break-iteration" then
		local forLines = 0
		for line in string.gmatch(source, "[^\n]+") do
			if string.match(line, "^%s*for .+ do%s*$") ~= nil then
				forLines += 1
			end
		end
		assert(forLines == 8, "an always-breaking loop lost its native for loop")
		local function check(initial: any, limit: any, expected: { any })
			local results = table.pack(exported(initial, limit))
			assert(results.n == 8, "always-breaking loops changed the result count")
			for index = 1, 8 do
				assert(results[index] == expected[index], "always-breaking loops changed a result")
			end
		end
		check(1, 3, { 4, 6, 9, 4, 2, 0, 3, 2 })
		check(3, 1, { 3, 3, 3, 3, 2, 0, 3, 1 })
		check(3, 3, { 4, 12, 9, 4, 2, 0, 4, 4 })
		check(10, 3, { 3, 3, 3, 3, 2, 0, 3, 1 })
		check(2.5, 7, { 4, 10.5, 9, 4, 2, 0, 4, 3.5 })

	elseif caseName == "source-frontend-always-break-transfer-iteration" then
		local forLines = 0
		for line in string.gmatch(source, "[^\n]+") do
			if string.match(line, "^%s*for .+ do%s*$") ~= nil then
				forLines += 1
			end
		end
		assert(forLines == 8, "a nested-transfer always-break body lost its native for loop")
		assert(string.find(source, "continue", 1, true) == nil, "a nested-transfer always-break body emitted a continue")
		local function check(initial: any, limit: any, expected: { any })
			local results = table.pack(exported(initial, limit))
			assert(results.n == 9, "nested-transfer always-break bodies changed the result count")
			for index = 1, 9 do
				assert(results[index] == expected[index], "nested-transfer always-break bodies changed a result")
			end
		end
		check(1, 3, { 333, 3033, 33, 224, 202, 323, 6, 6, 6 })
		check(1.5, 3, { 336, 3036, 36, 224, 202, 325, 7.5, 10.5, 7.5 })
		check(2, 3, { 336, 3036, 36, 224, 202, 325, 9, 12, 9 })
		check(3, 7, { 303, 3336, 3, 224, 202, 303, 12, 15, 12 })
		check(4, 10, { 303, 3003, 3, 224, 202, 303, 15, 18, 15 })
		check(6, 7, { 303, 3003, 3, 224, 202, 303, -1, -1, -1 })
		check(3, 1, { 303, 3003, 3, 224, 202, 303, 3, 3, 3 })
		check(10, 3, { 303, 3003, 3, 224, 202, 303, 3, 3, 3 })
		check(2.5, 7, { 303, 3336, 3, 224, 202, 303, 10.5, 13.5, 10.5 })
		check(3, 3, { 303, 3336, 3, 202, 202, 303, 12, 15, 12 })

	elseif caseName == "per-execution-cell-inherited-flat" then
		local selectors = { -1, 0, 1, 2, 3, 5, 1.5 }
		local budgets = { 0, 1, 2, 3, 4, 6 }
		local expected = {
			{ 0, 10, 50, 140, 300, 910 },
			{ 0, 11, 53, 146, 310, 931 },
			{ 0, 12, 56, 152, 320, 952 },
			{ 0, 13, 59, 158, 330, 973 },
			{ 0, 14, 62, 164, 340, 994 },
			{ 0, 16, 68, 176, 360, 1036 },
			{ 0, 12.5, 57.5, 155, 325, 962.5 },
		}
		for selectorIndex, selector in selectors do
			for budgetIndex, budget in budgets do
				assert(
					exported(selector, budget) == expected[selectorIndex][budgetIndex],
					"a boxed per-execution cell changed a nested-function result"
				)
			end
		end

	elseif
		caseName == "source-frontend-generic-initializer-scope"
		or caseName == "source-frontend-generic-initializer-scope-direct-locals"
	then
		local function check(limit: number, expectedText: string, expectedScore: number)
			local text, score = exported(limit)
			assert(text == expectedText and score == expectedScore, "a fused generic-for initializer lost its operand's declaration")
		end
		check(0, "", 0)
		check(3, "3,7,10", 1)
		check(8, "1,2,3,5,6,7,9,10", 7)
	elseif
		caseName == "source-frontend-generic-initializer-scope-storage"
		or caseName == "source-frontend-generic-initializer-scope-storage-direct-locals"
	then
		local storage = string.find(source, "__lifter_value_storage", 1, true) ~= nil
		if caseName == "source-frontend-generic-initializer-scope-storage" then
			assert(storage, "the standard-luau storage arm lost its value storage")
		else
			assert(not storage, "the direct-locals arm took value storage")
		end
		local function check(limit: number, expectedText: string, expectedScore: number)
			local text, score = exported(limit)
			assert(text == expectedText and score == expectedScore, "a fused generic-for initializer lost its operand's declaration")
		end
		check(0, "", 0)
		check(3, "3,7,10", 1)
		check(8, "1,2,3,5,6,7,9,10", 6)
		check(12, "0,1,2,3,4,5,6,7,7,8,9,10", 15)

	elseif
		caseName == "source-frontend-generic-initializer-order"
		or caseName == "source-frontend-generic-initializer-order-direct-locals"
	then
		if caseName == "source-frontend-generic-initializer-order-direct-locals" then
			assert(
				string.find(source, " in source(order) do", 1, true) ~= nil,
				"the order-preserving header call lost its fused generic-for initializer"
			)
		end
		local function check(mode: string, limit: number, expected: string)
			assert(exported(mode, limit) == expected, "a fused generic-for initializer moved its producer past a later effect")
		end
		check("between", 3, "source,between,1=3,2=2,3=1")
		check("guarded", 5, "source,between,1=5,2=2,3=1")
		check("guarded", 3, "source,1=3,2=2,3=1")
		check("reassigned", 3, "1=3,2=2,3=1,1")
		check("outer", 3, "source,1:1=3,1:2=2,1:3=1,2:1=3,2:2=2,2:3=1")
		check("break", 3, "source,between,3@1")
		check("boundary", 3, "source,between|3@1")
		check("header", 3, "between,source,1=3,2=2,3=1")

	elseif
		caseName == "source-frontend-proved-branch-unreachable-consumer"
		or caseName == "source-frontend-proved-branch-unreachable-consumer-direct-locals"
	then
		local numbers, strings = exported(10)
		assert(
			numbers == "6,7,8,9,10" and strings == "1,2,3,4,10",
			"a local that an unreachable consumer of a proved branch also reads lost its declaration"
		)
		local fewNumbers, fewStrings = exported(3)
		assert(
			fewNumbers == "" and fewStrings == "1,2,3",
			"a local that an unreachable consumer of a proved branch also reads lost its declaration"
		)

	elseif
		caseName == "source-frontend-generic-initializer-read-after"
		or caseName == "source-frontend-generic-initializer-read-after-direct-locals"
	then
		local function check(mode: string, limit: number, expected: string)
			assert(exported(mode, limit) == expected, "a generic-for initializer result read outside its loop header lost its declaration")
		end
		check("after", 3, "source,1=3,2=2,3=1,after=0/function/true")
		check("body", 3, "source,1#3,2#3,3#3")
		check("break", 3, "source,3@1,after=0/function")
		check("boundary", 5, "source,1:0/function,source,2:0/function")
		check("boundary", 3, "source|3@1")
		check("unread", 3, "source,1=3,2=2,3=1")
		check("header", 3, "source,1=3,2=2,3=1")
		if caseName == "source-frontend-generic-initializer-read-after-direct-locals" then
			assert(
				select(2, string.gsub(source, " in source%(order%) do", "")) == 2,
				"a generic-for initializer read only by its header lost its fusion, or one read outside it kept it"
			)
		end
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
	elseif
		caseName == "source-frontend-closure-store-environment"
		or caseName == "source-frontend-closure-store-environment-direct-locals"
	then
		local assigned, defined = exported()
		assert(assigned == "p:old", "closure store created a closure after code that replaced the environment")
		assert(defined == "f:old", "closure store created a function statement's closure after its target prefix")
	elseif caseName == "source-frontend-interpolation" then
		local rendered, calls = exported(7)
		assert(string.byte(rendered, 1) == 0xff and string.byte(rendered, 2) == 0xfe, "source frontend changed string byte transport")
		assert(string.sub(rendered, 3) == "prefix %7 box:7 nil false suffix", "source frontend changed interpolation conversion or percent escaping")
		assert(calls == 1, "source frontend changed interpolation __tostring dispatch count")
	elseif
		caseName == "source-frontend-repeat-header-exit"
		or caseName == "source-frontend-repeat-header-exit-direct-locals"
	then
		-- Six functions with a `repeat` whose header block's own branch decides: five leave the loop from it (a store
		-- then a break, a bare break, a break inside an `if` arm with and without a statement after the loop, and a store
		-- then a break inside an `if` arm of a `while` whose arm returns after the loop), one returns from it. No function
		-- of the module may be written in the dispatcher form, and each must return what a copy of its source returns on
		-- n -1..6, with the arm flag true and false for the three in an `if` arm and m 0..3 for the one in a `while`.
		assert(
			string.find(source, "local __lifter_pc =", 1, true) == nil,
			"source-frontend-repeat-header-exit: the generated module declares local __lifter_pc ="
		)
		local function assignThenBreak(n: number): (number, number)
			local p, i = 0, 0
			repeat
				i = i + 1
				if i == n then
					p = 100
					break
				end
			until i >= 3
			return p, i
		end
		local function bareBreak(n: number): (number, number)
			local p, i = 0, 0
			repeat
				i = i + 1
				if i == n then
					break
				end
			until i >= 3
			return p, i
		end
		local function breakInArmBeforeStatement(n: number, a: boolean): (number, number)
			local p, i = 0, 0
			if a then
				repeat
					i = i + 1
					if i == n then
						p = 100
						break
					end
				until i >= 3
				p = p + 1
			end
			return p, i
		end
		local function returnFromHeader(n: number): (number, number)
			local p, i = 0, 0
			repeat
				i = i + 1
				if i == n then
					return -1, i
				end
			until i >= 3
			return p, i
		end
		local function breakInArmTail(n: number, a: boolean): (number, number)
			local p, i = 0, 0
			if a then
				repeat
					i = i + 1
					if i == n then
						p = 100
						break
					end
				until i >= 3
			end
			return p, i
		end
		local function breakInWhileArmBeforeReturn(n: number, a: boolean, m: number): (number, number)
			local count, step, round = 0, 0, 0
			while round < m do
				round = round + 1
				if a then
					repeat
						step = step + 1
						if step == n then
							count = count + 100
							break
						end
					until step % 3 == 0
					return count, step
				end
			end
			return -count, step
		end
		local functions = exported()
		assert(type(functions) == "table", "source-frontend-repeat-header-exit: the module did not return its function table")
		local rows = 0
		local mismatches = 0
		local first = "none"
		local function check(label: string, expected: any, actual: any)
			rows += 1
			local same = expected.n == actual.n
			for index = 1, expected.n do
				if expected[index] ~= actual[index] then
					same = false
				end
			end
			if not same then
				if mismatches == 0 then
					first = label
				end
				mismatches += 1
			end
		end
		for n = -1, 6 do
			check(`assignThenBreak({n})`, table.pack(assignThenBreak(n)), table.pack(functions.assignThenBreak(n)))
			check(`bareBreak({n})`, table.pack(bareBreak(n)), table.pack(functions.bareBreak(n)))
			check(`returnFromHeader({n})`, table.pack(returnFromHeader(n)), table.pack(functions.returnFromHeader(n)))
			for _, a in { true, false } do
				check(
					`breakInArmBeforeStatement({n}, {a})`,
					table.pack(breakInArmBeforeStatement(n, a)),
					table.pack(functions.breakInArmBeforeStatement(n, a))
				)
				check(`breakInArmTail({n}, {a})`, table.pack(breakInArmTail(n, a)), table.pack(functions.breakInArmTail(n, a)))
				for m = 0, 3 do
					check(
						`breakInWhileArmBeforeReturn({n}, {a}, {m})`,
						table.pack(breakInWhileArmBeforeReturn(n, a, m)),
						table.pack(functions.breakInWhileArmBeforeReturn(n, a, m))
					)
				end
			end
		end
		assert(rows == 120, `{caseName}: {rows} rows checked, not 120`)
		assert(mismatches == 0, `{caseName}: {mismatches} of {rows} rows differ from the source; first {first}`)
	elseif
		caseName == "source-frontend-repeat-header-exit-nested"
		or caseName == "source-frontend-repeat-header-exit-nested-direct-locals"
	then
		-- The same `repeat` nested in a `while`, so the loop's until exit continues the outer loop. No dispatcher form,
		-- and the result equals a copy of the source's on n 0..6 and m 0..3.
		assert(
			string.find(source, "local __lifter_pc =", 1, true) == nil,
			"source-frontend-repeat-header-exit-nested: the generated module declares local __lifter_pc ="
		)
		local function nested(n: number, m: number): (number, number)
			local p, i, j = 0, 0, 0
			while j < m do
				j = j + 1
				repeat
					i = i + 1
					if i == n then
						p = p + 100
						break
					end
				until i % 3 == 0
				p = p + 1
			end
			return p, i
		end
		local rows = 0
		local mismatches = 0
		local first = "none"
		for n = 0, 6 do
			for m = 0, 3 do
				rows += 1
				local expectedP, expectedI = nested(n, m)
				local actualP, actualI = exported(n, m)
				if expectedP ~= actualP or expectedI ~= actualI then
					if mismatches == 0 then
						first = `({n}, {m})`
					end
					mismatches += 1
				end
			end
		end
		assert(rows == 28, `{caseName}: {rows} rows checked, not 28`)
		assert(mismatches == 0, `{caseName}: {mismatches} of {rows} rows differ from the source; first {first}`)
	elseif
		caseName == "source-frontend-repeat-header-exit-while-tail"
		or caseName == "source-frontend-repeat-header-exit-while-tail-direct-locals"
	then
		-- Two functions whose `repeat`, with a break from its header block, is the last statement of a `while` body,
		-- directly or inside an `if` arm, so the break and the until exit both continue the `while`. No function of the
		-- module may be written in the dispatcher form, and each must return what a copy of its source returns on
		-- n -1..6 and m 0..3, with the arm flag true and false.
		assert(
			string.find(source, "local __lifter_pc =", 1, true) == nil,
			"source-frontend-repeat-header-exit-while-tail: the generated module declares local __lifter_pc ="
		)
		local function repeatEndsWhileBody(n: number, a: boolean, m: number): (number, number)
			local count, step, round = 0, 0, 0
			while round < m do
				round = round + 1
				repeat
					step = step + 1
					if step == n then
						count = count + 100
						break
					end
				until step % 3 == 0
			end
			return count, step
		end
		local function repeatEndsWhileArm(n: number, a: boolean, m: number): (number, number)
			local count, step, round = 0, 0, 0
			while round < m do
				round = round + 1
				if a then
					repeat
						step = step + 1
						if step == n then
							count = count + 100
							break
						end
					until step % 3 == 0
				end
			end
			return count, step
		end
		local functions = exported()
		assert(
			type(functions) == "table",
			"source-frontend-repeat-header-exit-while-tail: the module did not return its function table"
		)
		local rows = 0
		local mismatches = 0
		local first = "none"
		local function check(label: string, expected: any, actual: any)
			rows += 1
			local same = expected.n == actual.n
			for index = 1, expected.n do
				if expected[index] ~= actual[index] then
					same = false
				end
			end
			if not same then
				if mismatches == 0 then
					first = label
				end
				mismatches += 1
			end
		end
		for n = -1, 6 do
			for m = 0, 3 do
				for _, a in { true, false } do
					check(
						`repeatEndsWhileBody({n}, {a}, {m})`,
						table.pack(repeatEndsWhileBody(n, a, m)),
						table.pack(functions.repeatEndsWhileBody(n, a, m))
					)
					check(
						`repeatEndsWhileArm({n}, {a}, {m})`,
						table.pack(repeatEndsWhileArm(n, a, m)),
						table.pack(functions.repeatEndsWhileArm(n, a, m))
					)
				end
			end
		end
		assert(rows == 128, `{caseName}: {rows} rows checked, not 128`)
		assert(mismatches == 0, `{caseName}: {mismatches} of {rows} rows differ from the source; first {first}`)
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
	elseif caseName == "source-frontend-wrapped-local-continue" then
		-- The worker against a copy of the source function over 15360 rows (n 0..4, m 0..2, 32 masks for f, 4 for g
		-- and 8 for the values observe returns): the result and the order of the callback calls must match. A run
		-- that makes more than 400 callback calls stops with the error "call cap".
		local function reference(n: number, _m: number, marker: any, f: any, g: any, observe: any): any
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
		local function bit(mask: number, index: number): boolean
			return bit32.band(mask, bit32.lshift(1, index)) ~= 0
		end
		local function runRow(worker: any, n: number, m: number, maskF: number, maskG: number, maskO: number): (string, string)
			local log: { string } = {}
			local calls = 0
			local function tick(entry: string)
				calls += 1
				if calls > 400 then
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
			local ok, result = pcall(worker, n, m, "marker", f, g, observe)
			local outcome = if ok then "ok:" .. tostring(result) else "err:" .. string.gsub(tostring(result), "^.-:%d+: ", "")
			local shown = if #log <= 12 then table.concat(log, " ") else table.concat(log, " ", 1, 12) .. ` ... ({#log} calls)`
			return outcome .. " [" .. table.concat(log, " ") .. "]", outcome .. " [" .. shown .. "]"
		end
		local rows, mismatches = 0, 0
		local first = ""
		for n = 0, 4 do
			for m = 0, 2 do
				for maskF = 0, 31 do
					for maskG = 0, 3 do
						for maskO = 0, 7 do
							local expected, expectedShown = runRow(reference, n, m, maskF, maskG, maskO)
							local actual, actualShown = runRow(exported, n, m, maskF, maskG, maskO)
							rows += 1
							if expected ~= actual then
								mismatches += 1
								if first == "" then
									first = `n={n} m={m} maskF={maskF} maskG={maskG} maskO={maskO} expected={expectedShown} got={actualShown}`
								end
							end
						end
					end
				end
			end
		end
		assert(mismatches == 0, `a loop with two continues changed its behaviour: rows={rows} mismatches={mismatches} first: {first}`)
	elseif caseName == "source-frontend-double-rounding-comparison" then
		local equalArm, notEqualArm = exported()
		assert(equalArm == "else-arm", "equality with a double chain rounded beyond 2^53 followed exact integer arithmetic")
		assert(notEqualArm == "then-arm", "inequality with a double chain rounded beyond 2^53 followed exact integer arithmetic")
	elseif caseName == "source-frontend-double-rounding-comparison-in-range" then
		assert(exported() == "else-arm", "equality with a double chain rounded to 2^53 followed exact integer arithmetic")
	elseif caseName == "source-frontend-wide-integral-number" then
		local passed: { [number]: any, n: number } = { n = 0 }
		local returned = table.pack(exported(function(...: any)
			passed = table.pack(...)
		end))
		local record, list = returned[8], returned[9]
		assert(passed.n == 3 and returned.n == 9 and #list == 3, "wide integral numbers changed their count")
		local observed = {
			passed[1], passed[2], passed[3],
			returned[1], returned[2], returned[3], returned[4], returned[5], returned[6], returned[7],
			record.p53, record.p53plus2, record.p63, record.p64, record.e20, record.neg64, record.half64, record.half64expr,
			list[1], list[2], list[3],
		}
		local expected = {
			9223372036854775808, 18446744073709551616, -18446744073709551616,
			9007199254740992, 9007199254740994, 9223372036854775808, 18446744073709551616, 100000000000000000000, -18446744073709551616, 9223372036854775808,
			9007199254740992, 9007199254740994, 9223372036854775808, 18446744073709551616, 100000000000000000000, -18446744073709551616, 9223372036854775808, 9223372036854775808,
			9007199254740994, 18446744073709551616, 100000000000000000000,
		}
		for index, value in expected do
			assert(observed[index] == value, `wide integral number {index} changed its value`)
		end
	elseif caseName == "source-frontend-exact-number-literal" then
		local expected = {
			8.98846567431158e307,
			4.4942328371557898e307,
			0.000001,
			1e-9,
			1e-12,
			1.602176634e-19,
			1.7976931348623157e308,
			0.1,
			1e-320,
			1e23,
		}
		local values = exported()
		assert(type(values) == "table" and #values == #expected, "the number literal list changed its length")
		local changed = {}
		for index, value in expected do
			if string.pack(">d", values[index]) ~= string.pack(">d", value) then
				table.insert(changed, tostring(index))
			end
		end
		assert(#changed == 0, `number literals changed their bits at entries {table.concat(changed, ",")}`)
	elseif
		caseName == "source-frontend-loop-exit-flag-reentry"
		or caseName == "source-frontend-loop-exit-flag-reentry-direct-locals"
		or caseName == "source-frontend-loop-exit-flag-reentry-mid-pass"
		or caseName == "source-frontend-loop-exit-flag-reentry-mid-pass-direct-locals"
	then
		-- The worker against a copy of its source function over 24 rows (n 0..5, m 0..3): the result and the order of
		-- observe's arguments must match. The inner loop's `break` is carried by its exit's escape flag and the outer
		-- loop enters the inner loop again on every pass, so a flag one pass left set would end the next pass's inner
		-- loop after its first pass or, in the mid-pass shape, part way through it. A run that makes more than 400
		-- observe calls stops with the error "call cap".
		local function reentry(n: number, m: number, _marker: any, _f: any, _g: any, observe: any): any
			local total = 0
			for pass = 1, m do
				local acc = 0
				for i = 1, n do
					if i > 1 then
						if i > pass + 1 then
							continue
						end
					end
					acc += 1
					observe(i)
					if acc > 1 then
						break
					end
				end
				total = total * 10 + acc
			end
			return total
		end
		local function reentryMidPass(n: number, m: number, _marker: any, _f: any, _g: any, observe: any): any
			local total = 0
			for _ = 1, 2 do
				local acc = 0
				for i = 1, n do
					if i > 1 then
						if i > 2 then
							continue
						end
					end
					if i > 0 then
						if i > m then
							if acc > 5 then
								continue
							end
						end
						acc += 1
						if acc > 1 then
							break
						end
						acc += 10
						observe(10 * i)
					end
					acc += 100
					observe(100 * i)
				end
				total = total * 1000 + acc
			end
			return total
		end
		local reference = if string.find(caseName, "mid-pass", 1, true) ~= nil then reentryMidPass else reentry
		local function runRow(worker: any, n: number, m: number): string
			local log: { string } = {}
			local function observe(value: number)
				if #log >= 400 then
					error("call cap", 0)
				end
				table.insert(log, tostring(value))
			end
			local ok, result = pcall(worker, n, m, "marker", function()
				return false
			end, function()
				return false
			end, observe)
			local outcome = if ok then "ok:" .. tostring(result) else "err:" .. string.gsub(tostring(result), "^.-:%d+: ", "")
			return outcome .. " [" .. table.concat(log, ",") .. "]"
		end
		local rows, mismatches = 0, 0
		local first = ""
		for n = 0, 5 do
			for m = 0, 3 do
				local expected = runRow(reference, n, m)
				local actual = runRow(exported, n, m)
				rows += 1
				if expected ~= actual then
					mismatches += 1
					if first == "" then
						first = `n={n} m={m} expected={expected} got={actual}`
					end
				end
			end
		end
		assert(mismatches == 0, `{caseName}: {mismatches} of {rows} rows differ from the source; first {first}`)
	elseif
		caseName == "source-frontend-many-array-items-253"
		or caseName == "source-frontend-many-array-items-253-direct-locals"
	then
		assert(exported(1) == "s0" and exported(253) == "s252" and exported(254) == nil, "a constructor with 253 array items changed its items")
	elseif
		caseName == "source-frontend-many-array-items-254"
		or caseName == "source-frontend-many-array-items-254-direct-locals"
	then
		assert(exported(1) == "s0" and exported(254) == "s253" and exported(255) == nil, "a constructor with 254 array items changed its items")
	elseif
		caseName == "source-frontend-many-array-items-300"
		or caseName == "source-frontend-many-array-items-300-direct-locals"
		or caseName == "source-frontend-many-array-items-in-function-300"
		or caseName == "source-frontend-many-array-items-in-function-300-direct-locals"
	then
		assert(
			exported(1) == "s0" and exported(254) == "s253" and exported(300) == "s299" and exported(301) == nil,
			"a constructor with 300 array items changed its items"
		)
	elseif
		caseName == "source-frontend-many-array-items-1000"
		or caseName == "source-frontend-many-array-items-1000-direct-locals"
	then
		assert(
			exported(1) == "s0" and exported(254) == "s253" and exported(1000) == "s999" and exported(1001) == nil,
			"a constructor with 1000 array items changed its items"
		)
	elseif
		caseName == "source-frontend-many-number-items-300"
		or caseName == "source-frontend-many-number-items-300-direct-locals"
	then
		assert(exported(1) == 0 and exported(254) == 253 and exported(300) == 299, "a constructor with 300 number items changed its items")
	elseif
		caseName == "source-frontend-many-computed-items-300"
		or caseName == "source-frontend-many-computed-items-300-direct-locals"
	then
		local items = exported(5)
		assert(
			type(items) == "table" and #items == 300 and items[1] == 5 and items[254] == 258 and items[300] == 304,
			"a constructor with 300 computed items changed its items"
		)
	elseif
		caseName == "source-frontend-nested-continue-side-exit-generic"
		or caseName == "source-frontend-nested-continue-side-exit-while"
		or caseName == "source-frontend-nested-continue-side-exit-numeric"
		or caseName == "source-frontend-nested-continue-side-exit-elseif"
		or caseName == "source-frontend-nested-continue-side-exit-nested-break"
	then
		-- The worker against a copy of its source function over the rows of the wrapped-local-continue case (n 0..4,
		-- m 0..2, 32 masks for f, 4 for g and 8 for the values observe returns): the result and the order of the callback
		-- calls must match. Each loop holds a `continue` two `if`s deep and a later `break` that leaves the loop from
		-- inside the transfer wrapper the `continue` puts around the loop body; the generic shape enters its loop again on
		-- the outer loop's second pass, so a flag that carries the `break` must start false on each entry. A run that makes
		-- more than 400 callback calls stops with the error "call cap".
		local function generic(n: number, m: number, marker: any, f: any, g: any, observe: any): any
			local items: { number } = {}
			for k = 1, n do
				items[k] = k
			end
			local total = 0
			for pass = 1, 2 do
				for i, v in ipairs(items) do
					if f(v) then
						if g(v) then
							continue
						end
						observe(v)
					end
					if f(v, pass) then
						observe(300 + pass)
						break
					end
					total += i
				end
				observe(100 + pass)
			end
			return if m < total then total else marker
		end
		local function whileLoop(n: number, m: number, marker: any, f: any, g: any, observe: any): any
			local i = 0
			while i < n do
				i += 1
				if f(i) then
					if g(i) then
						continue
					end
					observe(i)
				end
				if f(i, 1) then
					break
				end
				observe(100)
			end
			return if m < i then i else marker
		end
		local function numeric(n: number, m: number, marker: any, f: any, g: any, observe: any): any
			local acc = 0
			for i = 1, n do
				if f(i) then
					if g(i) then
						continue
					end
					acc += i
				end
				if f(i, 1) then
					observe(300)
					break
				end
				observe(100)
			end
			return if m < acc then acc else marker
		end
		local function elseifContinue(n: number, m: number, marker: any, f: any, g: any, observe: any): any
			local acc = 0
			for i = 1, n do
				if f(i) then
					acc += i
				elseif g(i) then
					continue
				end
				if f(i, 1) then
					observe(300)
					break
				end
				observe(100)
			end
			return if m < acc then acc else marker
		end
		local function nestedBreak(n: number, m: number, marker: any, f: any, g: any, observe: any): any
			local acc = 0
			for i = 1, n do
				if f(i) then
					if g(i) then
						continue
					end
					acc += i
				end
				if f(i, 1) then
					if acc > m then
						observe(300)
						break
					end
					acc += 1
				end
				observe(100)
			end
			return if m < acc then acc else marker
		end
		local references: { [string]: any } = {
			["source-frontend-nested-continue-side-exit-generic"] = generic,
			["source-frontend-nested-continue-side-exit-while"] = whileLoop,
			["source-frontend-nested-continue-side-exit-numeric"] = numeric,
			["source-frontend-nested-continue-side-exit-elseif"] = elseifContinue,
			["source-frontend-nested-continue-side-exit-nested-break"] = nestedBreak,
		}
		local reference = references[caseName]
		local function bit(mask: number, index: number): boolean
			return bit32.band(mask, bit32.lshift(1, index)) ~= 0
		end
		local function runRow(worker: any, n: number, m: number, maskF: number, maskG: number, maskO: number): (string, string)
			local log: { string } = {}
			local calls = 0
			local function tick(entry: string)
				calls += 1
				if calls > 400 then
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
			local ok, result = pcall(worker, n, m, "marker", f, g, observe)
			local outcome = if ok then "ok:" .. tostring(result) else "err:" .. string.gsub(tostring(result), "^.-:%d+: ", "")
			local shown = if #log <= 12 then table.concat(log, " ") else table.concat(log, " ", 1, 12) .. ` ... ({#log} calls)`
			return outcome .. " [" .. table.concat(log, " ") .. "]", outcome .. " [" .. shown .. "]"
		end
		local rows, mismatches = 0, 0
		local first = ""
		for n = 0, 4 do
			for m = 0, 2 do
				for maskF = 0, 31 do
					for maskG = 0, 3 do
						for maskO = 0, 7 do
							local expected, expectedShown = runRow(reference, n, m, maskF, maskG, maskO)
							local actual, actualShown = runRow(exported, n, m, maskF, maskG, maskO)
							rows += 1
							if expected ~= actual then
								mismatches += 1
								if first == "" then
									first = `n={n} m={m} maskF={maskF} maskG={maskG} maskO={maskO} expected={expectedShown} got={actualShown}`
								end
							end
						end
					end
				end
			end
		end
		assert(mismatches == 0, `{caseName}: {mismatches} of {rows} rows differ from the source; first {first}`)
	elseif caseName == "source-frontend-closure-store-parenthesized-target" then
		local previous = ""
		for line in string.gmatch(source .. "\n", "([^\n]*)\n") do
			if string.match(line, "^%s*%(") ~= nil then
				local word = string.match(previous, "([%w_]+)%s*$")
				local closes = string.match(previous, "[%)%]]%s*$") ~= nil
				local keyword = word == "do" or word == "then" or word == "else" or word == "repeat" or word == "end"
				assert(not closes and (word == nil or keyword), `a statement that begins with a parenthesis follows a prefix expression: {previous} / {line}`)
			end
			if string.match(line, "%S") ~= nil then
				previous = line
			end
		end
		local events: { string } = {}
		local function observe(label: any): string
			table.insert(events, tostring(label))
			return "seen:" .. tostring(label)
		end
		assert(exported(observe, 0, false) == "seen:finish", "closure stores changed the normal completion")
		assert(table.concat(events, ",") == "start,finish", "closure stores changed the call order of the normal completion")
		table.clear(events)
		local storeOk, storeError = pcall(exported, observe, 0, true)
		assert(not storeOk, "a closure store into nil did not raise")
		assert(string.find(tostring(storeError), "attempt to index nil with 'handler'", 1, true) ~= nil, "the closure store raised another error")
		assert(table.concat(events, ",") == "start,store", "the closure store ran before or without its preceding call")
		table.clear(events)
		local loopOk, loopError = pcall(exported, observe, 2, false)
		assert(not loopOk, "a captured closure store into nil did not raise")
		assert(string.find(tostring(loopError), "attempt to index nil with 'captured'", 1, true) ~= nil, "the captured closure store raised another error")
		assert(table.concat(events, ",") == "start,1", "the captured closure store ran before or without its binding's call")
	else
		return false
	end
	return true
end

return table.freeze(SourceRuntimeOracle)
