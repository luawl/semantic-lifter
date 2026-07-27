local function expand(...)
	return ...
end

local function protectedSuccess(label, value)
	return label, value, nil, "tail:" .. label
end

local function protectedFailure(message)
	error(message, 0)
end

local function errorHandler(message)
	return "handled:" .. tostring(message)
end

local errorEffects = ""
local errorIdentity = {}

local function orderedErrorMessage()
	errorEffects ..= "m"
	return errorIdentity
end

local function orderedErrorExtra()
	errorEffects ..= "x"
	return "ignored"
end

local function dynamicLevelFailure()
	local dynamicLevel = 1
	error(errorIdentity, dynamicLevel)
end

local function nonpositiveDynamicLevelFailure()
	local dynamicLevel = (-0.0 - 0.1) - 0.2
	error("nonpositive-dynamic-error", dynamicLevel)
end

if false then
	local deadDynamicLevel = 0
	error("dead-dynamic-error", deadDynamicLevel)
end

local propagationEffects = ""

local function note(label, value)
	propagationEffects ..= label
	return value
end

local function observe(run)
	propagationEffects = ""
	local status, value = pcall(run)
	return status, value == errorIdentity, propagationEffects
end

local function returnTermination()
	return note("a", 1), error(note("m", errorIdentity), 0), note("z", 3)
end

local function argumentTermination()
	return note("!", 0)(note("b", 1), error(note("n", errorIdentity), 0), note("q", 3))
end

local function aggregateTermination()
	return {
		note("t", 1),
		text = `before {note("i", 2)} middle {error(note("e", errorIdentity), 0)} after {note("x", 3)}`,
		note("u", 4),
	}
end

local function constructorKeyTermination(label, key)
	return {
		[note(label, key)] = note("v", 1),
		[2] = error(note("e", errorIdentity), 0),
	}
end

local function observeConstructorKeyTermination()
	local nilStatus, nilIdentity, nilEffects = observe(function()
		return constructorKeyTermination("k", nil)
	end)
	local nanStatus, nanIdentity, nanEffects = observe(function()
		return constructorKeyTermination("n", 0 / 0)
	end)
	local function constructorTailPack(mode)
		propagationEffects ..= "t"
		if mode == "zero" then
			return
		elseif mode == "one" then
			return "one"
		end
		return "many-a", nil, "many-c"
	end
	local function orderedConstructorTail(key, mode)
		return {
			"prefix",
			[note("k", key)] = note("v", "keyed"),
			constructorTailPack(mode),
		}
	end
	local function run(key, mode)
		propagationEffects = ""
		local status, value = pcall(orderedConstructorTail, key, mode)
		return { status = status, identity = value == errorIdentity, effects = propagationEffects, value = value }
	end
	local tail = {
		nil_key = run(nil, "many"),
		zero = run(2, "zero"),
		one = run(3, "one"),
		many = run(3, "many"),
	}
	local function orderedConstructorVarargs(key, ...)
		return {
			"vararg-prefix",
			[note("k", key)] = note("v", "vararg-keyed"),
			...,
		}
	end
	propagationEffects = ""
	local varargValue = orderedConstructorVarargs(3, "vararg-a", nil, "vararg-c")
	return {
		nil_key = { status = nilStatus, identity = nilIdentity, effects = nilEffects },
		nan_key = { status = nanStatus, identity = nanIdentity, effects = nanEffects },
		tail = tail,
		varargs = { effects = propagationEffects, value = varargValue },
	}
end

local function arithmeticTermination()
	return note("l", 1) + -error(note("r", errorIdentity), 0)
end

local function assignmentTargetTermination()
	(error(note("p", errorIdentity), 0))[note("k", "key")] = note("w", 1)
end

local function assignmentValueTermination()
	local first, second, third = 0, 0, 0
	first, second, third = note("v", 1), error(note("m", errorIdentity), 0), note("z", 3)
	note("w", first + second + third)
end

local function numericLoopTermination()
	for _ = note("f", 1), error(note("l", errorIdentity), 0), note("s", 1) do
		note("b", 1)
	end
	note("a", 1)
end

local function genericLoopTermination()
	for _ in note("g", next), error(note("h", errorIdentity), 0), note("j", {}) do
		note("b", 1)
	end
	note("a", 1)
end

local function shortCircuitTermination(shouldThrow)
	return shouldThrow and error(note("c", errorIdentity), 0) or note("s", "survived")
end

local function repeatBreakSurvival()
	repeat
		break
	until error(note("u", errorIdentity), 0)
	return "escaped"
end

local function repeatNoBreakTermination()
	repeat
		note("r", 1)
	until error(note("u", errorIdentity), 0)
	note("a", 1)
end

local function repeatConditionalBreak(leave)
	repeat
		note("b", 1)
		if leave then
			break
		end
	until error(note("u", errorIdentity), 0)
	note("a", 1)
	return "escaped"
end

local function repeatNestedBreak()
	repeat
		repeat
			note("n", 1)
			break
		until true
	until error(note("u", errorIdentity), 0)
	note("a", 1)
end

local function repeatConditionalContinue(shouldContinue)
	repeat
		note("c", 1)
		if shouldContinue then
			shouldContinue = false
			continue
		end
		error(note("t", errorIdentity), 0)
	until note("l", true)
	note("a", 1)
	return "escaped"
end

local function repeatNestedContinue()
	repeat
		repeat
			note("n", 1)
			continue
		until true
		error(note("t", errorIdentity), 0)
	until error(note("u", errorIdentity), 0)
	note("a", 1)
end

local function worker(seed, ...)
	local fixedReply = (coroutine.yield("fixed-yield", seed))
	local openFirst, openSecond, openThird = coroutine.yield("open-yield", fixedReply, ...)
	return "done", openFirst, openSecond, openThird
end

local function protectedYieldWorker(shouldFail, ...)
	local status, tag, first, hole, last = pcall(function(...)
		local reply, replyHole, replyTail = coroutine.yield("protected-yield", ...)
		if shouldFail then
			error(errorIdentity, 0)
		end
		return "protected-return", reply, replyHole, replyTail
	end, ...)
	return status, tag, first, hole, last
end

local function runProtectedYield(shouldFail)
	local thread = coroutine.create(protectedYieldWorker)
	local firstStatus, firstTag, firstHead, firstHole, firstTail =
		coroutine.resume(thread, shouldFail, expand("protected-head", nil, 31))
	local finalStatus, callStatus, returnTag, reply, replyHole, replyTail =
		coroutine.resume(thread, expand("protected-reply", nil, 37))
	return {
		first_status = firstStatus,
		first_tag = firstTag,
		first_head = firstHead,
		first_hole = firstHole,
		first_tail = firstTail,
		final_status = finalStatus,
		call_status = callStatus,
		return_tag = returnTag,
		failure_identity = returnTag == errorIdentity,
		reply = reply,
		reply_hole = replyHole,
		reply_tail = replyTail,
	}
end

local function observeProtectedYield()
	return {
		success = runProtectedYield(false),
		failure = runProtectedYield(true),
	}
end

local function createForReturn()
	return coroutine.create(worker)
end

local function threadType(value)
	return type(value)
end

local function exactOpenTermination()
	error(coroutine.create(worker))
end

local function zeroLevel()
	return 0
end

local function unresolvedOpenTermination()
	error(pcall(zeroLevel))
end

local invokeAlias = pcall
local createAlias = coroutine.create
local failAlias = error

local function aliasFailure()
	failAlias(errorIdentity, 0)
end

local function aliasExactFailure()
	failAlias(createAlias(worker))
end

local mutableFail = failAlias
mutableFail = function(message)
	return "replacement:" .. message
end

local function ifJoinedPcall(useLeft)
	local joined = if useLeft then pcall else pcall
	return joined(protectedSuccess, "if-join", 10)
end

local function shortJoinedPcall()
	local joined = pcall and pcall
	return joined(protectedSuccess, "short-join", 11)
end

local function survivingJoinedPcall(shouldThrow)
	local joined = if shouldThrow then error(errorIdentity, 0) else pcall
	return joined(protectedSuccess, "surviving-join", 12)
end

local function mismatchedJoin(usePcall)
	local joined = if usePcall then pcall else xpcall
	if usePcall then
		return joined(protectedSuccess, "mismatch", 13)
	end
	return joined(protectedFailure, errorHandler, "mismatch-error")
end

local function observeRepeatReachability()
	local breakStatus, _, breakEffects = observe(repeatBreakSurvival)
	local noBreakStatus, noBreakIdentity, noBreakEffects = observe(repeatNoBreakTermination)
	local conditionalExitStatus, _, conditionalExitEffects = observe(function()
		return repeatConditionalBreak(true)
	end)
	local conditionalThrowStatus, conditionalThrowIdentity, conditionalThrowEffects = observe(function()
		return repeatConditionalBreak(false)
	end)
	local nestedStatus, nestedIdentity, nestedEffects = observe(repeatNestedBreak)
	local continueExitStatus, _, continueExitEffects = observe(function()
		return repeatConditionalContinue(true)
	end)
	local continueThrowStatus, continueThrowIdentity, continueThrowEffects = observe(function()
		return repeatConditionalContinue(false)
	end)
	local nestedContinueStatus, nestedContinueIdentity, nestedContinueEffects = observe(repeatNestedContinue)
	return {
		break_status = breakStatus,
		break_effects = breakEffects,
		no_break_status = noBreakStatus,
		no_break_identity = noBreakIdentity,
		no_break_effects = noBreakEffects,
		conditional_exit_status = conditionalExitStatus,
		conditional_exit_effects = conditionalExitEffects,
		conditional_throw_status = conditionalThrowStatus,
		conditional_throw_identity = conditionalThrowIdentity,
		conditional_throw_effects = conditionalThrowEffects,
		nested_status = nestedStatus,
		nested_identity = nestedIdentity,
		nested_effects = nestedEffects,
		continue_exit_status = continueExitStatus,
		continue_exit_effects = continueExitEffects,
		continue_throw_status = continueThrowStatus,
		continue_throw_identity = continueThrowIdentity,
		continue_throw_effects = continueThrowEffects,
		nested_continue_status = nestedContinueStatus,
		nested_continue_identity = nestedContinueIdentity,
		nested_continue_effects = nestedContinueEffects,
	}
end

local discardedCalls = 0
pcall(function()
	discardedCalls += 1
end)

local orderedErrorStatus, orderedErrorValue = pcall(function()
	error(orderedErrorMessage(), 0, orderedErrorExtra())
end)
local omittedErrorStatus, omittedErrorValue = pcall(function()
	error(errorIdentity)
end)
local dynamicLevelStatus, dynamicLevelValue = pcall(dynamicLevelFailure)
local nonpositiveLevelStatus, nonpositiveLevelValue = pcall(nonpositiveDynamicLevelFailure)
local returnTerminationStatus, returnTerminationIdentity, returnTerminationEffects = observe(returnTermination)
local argumentTerminationStatus, argumentTerminationIdentity, argumentTerminationEffects = observe(argumentTermination)
local aggregateTerminationStatus, aggregateTerminationIdentity, aggregateTerminationEffects = observe(aggregateTermination)
local constructorKey = observeConstructorKeyTermination()
local arithmeticTerminationStatus, arithmeticTerminationIdentity, arithmeticTerminationEffects = observe(arithmeticTermination)
local assignmentTargetStatus, assignmentTargetIdentity, assignmentTargetEffects = observe(assignmentTargetTermination)
local assignmentValueStatus, assignmentValueIdentity, assignmentValueEffects = observe(assignmentValueTermination)
local numericLoopStatus, numericLoopIdentity, numericLoopEffects = observe(numericLoopTermination)
local genericLoopStatus, genericLoopIdentity, genericLoopEffects = observe(genericLoopTermination)
local shortThrowStatus, shortThrowIdentity, shortThrowEffects = observe(function()
	return shortCircuitTermination(true)
end)
local shortSurviveStatus, _, shortSurviveEffects = observe(function()
	return shortCircuitTermination(false)
end)
local repeatReachability = observeRepeatReachability()
local exactOpenStatus, exactOpenValue = pcall(exactOpenTermination)
local exactOpenValueType = type(exactOpenValue)
local unresolvedOpenStatus, unresolvedOpenValue = pcall(unresolvedOpenTermination)
local aliasPcallStatus, aliasPcallLabel, aliasPcallValue = invokeAlias(protectedSuccess, "alias", 9)
local aliasThread, aliasExtra = createAlias(worker)
local aliasThreadType = type(aliasThread)
local aliasErrorStatus, aliasErrorValue = pcall(aliasFailure)
local aliasExactStatus, aliasExactValue = pcall(aliasExactFailure)
local aliasExactValueType = type(aliasExactValue)
local mutableAliasResult = mutableFail("ok", 0)
local ifJoinStatus, ifJoinLabel, ifJoinValue = ifJoinedPcall(false)
local shortJoinStatus, shortJoinLabel, shortJoinValue = shortJoinedPcall()
local survivingJoinStatus, survivingJoinLabel, survivingJoinValue = survivingJoinedPcall(false)
local joinedThrowStatus, joinedThrowIdentity = observe(function()
	return survivingJoinedPcall(true)
end)
local mismatchPcallStatus, mismatchPcallLabel, mismatchPcallValue = mismatchedJoin(true)
local mismatchXpcallStatus, mismatchXpcallMessage = mismatchedJoin(false)

local fixedPcallStatus = (pcall(protectedSuccess, "fixed", 3))
local openPcallStatus, openPcallLabel, openPcallValue, openPcallHole, openPcallTail =
	pcall(protectedSuccess, expand("open", 7))

local fixedXpcallStatus = (xpcall(protectedFailure, errorHandler, "fixed-error"))
local openXpcallStatus, openXpcallMessage = xpcall(protectedFailure, errorHandler, expand("open-error"))

local thread = (coroutine.create(worker))
local openThread, openExtra = coroutine.create(worker)
local openThreadType = type(openThread)
local returnedThread = (createForReturn())
local returnedThreadType = type(returnedThread)
local argumentThreadType = (threadType(coroutine.create(worker)))
local packedThreads = { "prefix", coroutine.create(worker) }
local tableThreadType = type(packedThreads[2])

local fixedResumeStatus = (coroutine.resume(thread, expand(11, "tail-a", nil, "tail-c")))
local secondStatus, secondTag, secondReply, secondTailA, secondTailHole, secondTailC =
	coroutine.resume(thread, expand("reply-one"))
local finalStatus, finalTag, finalFirst, finalHole, finalThird =
	coroutine.resume(thread, expand("resume-a", nil, "resume-c"))
local protectedYield = observeProtectedYield()

local result = {
	discarded_calls = discardedCalls,
	ordered_error_status = orderedErrorStatus,
	ordered_error_identity = orderedErrorValue == errorIdentity,
	ordered_error_effects = errorEffects,
	omitted_error_status = omittedErrorStatus,
	omitted_error_identity = omittedErrorValue == errorIdentity,
	dynamic_level_status = dynamicLevelStatus,
	dynamic_level_identity = dynamicLevelValue == errorIdentity,
	nonpositive_level_status = nonpositiveLevelStatus,
	nonpositive_level_value = nonpositiveLevelValue,
	return_termination_status = returnTerminationStatus,
	return_termination_identity = returnTerminationIdentity,
	return_termination_effects = returnTerminationEffects,
	argument_termination_status = argumentTerminationStatus,
	argument_termination_identity = argumentTerminationIdentity,
	argument_termination_effects = argumentTerminationEffects,
	aggregate_termination_status = aggregateTerminationStatus,
	aggregate_termination_identity = aggregateTerminationIdentity,
	aggregate_termination_effects = aggregateTerminationEffects,
	constructor_key = constructorKey,
	arithmetic_termination_status = arithmeticTerminationStatus,
	arithmetic_termination_identity = arithmeticTerminationIdentity,
	arithmetic_termination_effects = arithmeticTerminationEffects,
	assignment_target_status = assignmentTargetStatus,
	assignment_target_identity = assignmentTargetIdentity,
	assignment_target_effects = assignmentTargetEffects,
	assignment_value_status = assignmentValueStatus,
	assignment_value_identity = assignmentValueIdentity,
	assignment_value_effects = assignmentValueEffects,
	numeric_loop_status = numericLoopStatus,
	numeric_loop_identity = numericLoopIdentity,
	numeric_loop_effects = numericLoopEffects,
	generic_loop_status = genericLoopStatus,
	generic_loop_identity = genericLoopIdentity,
	generic_loop_effects = genericLoopEffects,
	short_throw_status = shortThrowStatus,
	short_throw_identity = shortThrowIdentity,
	short_throw_effects = shortThrowEffects,
	short_survive_status = shortSurviveStatus,
	short_survive_effects = shortSurviveEffects,
	repeat_reachability = repeatReachability,
	exact_open_status = exactOpenStatus,
	exact_open_value_type = exactOpenValueType,
	unresolved_open_status = unresolvedOpenStatus,
	unresolved_open_value = unresolvedOpenValue,
	alias_pcall_status = aliasPcallStatus,
	alias_pcall_label = aliasPcallLabel,
	alias_pcall_value = aliasPcallValue,
	alias_thread_type = aliasThreadType,
	alias_extra = aliasExtra,
	alias_error_status = aliasErrorStatus,
	alias_error_identity = aliasErrorValue == errorIdentity,
	alias_exact_status = aliasExactStatus,
	alias_exact_value_type = aliasExactValueType,
	mutable_alias_result = mutableAliasResult,
	if_join_status = ifJoinStatus,
	if_join_label = ifJoinLabel,
	if_join_value = ifJoinValue,
	short_join_status = shortJoinStatus,
	short_join_label = shortJoinLabel,
	short_join_value = shortJoinValue,
	surviving_join_status = survivingJoinStatus,
	surviving_join_label = survivingJoinLabel,
	surviving_join_value = survivingJoinValue,
	joined_throw_status = joinedThrowStatus,
	joined_throw_identity = joinedThrowIdentity,
	mismatch_pcall_status = mismatchPcallStatus,
	mismatch_pcall_label = mismatchPcallLabel,
	mismatch_pcall_value = mismatchPcallValue,
	mismatch_xpcall_status = mismatchXpcallStatus,
	mismatch_xpcall_message = mismatchXpcallMessage,
	fixed_pcall_status = fixedPcallStatus,
	open_pcall_status = openPcallStatus,
	open_pcall_label = openPcallLabel,
	open_pcall_value = openPcallValue,
	open_pcall_hole = openPcallHole,
	open_pcall_tail = openPcallTail,
	fixed_xpcall_status = fixedXpcallStatus,
	open_xpcall_status = openXpcallStatus,
	open_xpcall_message = openXpcallMessage,
	open_thread_type = openThreadType,
	open_extra = openExtra,
	returned_thread_type = returnedThreadType,
	argument_thread_type = argumentThreadType,
	table_thread_type = tableThreadType,
	fixed_resume_status = fixedResumeStatus,
	second_status = secondStatus,
	second_tag = secondTag,
	second_reply = secondReply,
	second_tail_a = secondTailA,
	second_tail_hole = secondTailHole,
	second_tail_c = secondTailC,
	final_status = finalStatus,
	final_tag = finalTag,
	final_first = finalFirst,
	final_hole = finalHole,
	final_third = finalThird,
	protected_yield = protectedYield,
}

return function()
	return result
end
