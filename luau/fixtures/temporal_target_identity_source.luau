return function(value)
	local reads = 0
	local namespace = setmetatable({}, {
		__index = function(_, key)
			reads += 1
			if key == "dispatch" then
				return function(argument)
					return "snapshot", argument + 1
				end
			end
			return nil
		end,
	})
	local unresolvedSnapshot = namespace.dispatch
	namespace.dispatch = function(argument)
		return "replacement", argument + 100
	end

	local unresolvedMutable = nil
	unresolvedMutable = function(argument)
		return "mutable", argument + 2
	end
	local sharedTarget = function(argument)
		return "joined", argument + 3
	end
	local joinedAlias = nil
	if value >= 0 then
		joinedAlias = sharedTarget
	else
		joinedAlias = sharedTarget
	end
	local unresolvedJoined = joinedAlias
	local precommitTarget = function(argument)
		return "precommit", argument + 4
	end
	local unresolvedPrecommit = precommitTarget
	local precommitTag = nil
	local precommitValue = nil
	unresolvedPrecommit, precommitTag, precommitValue = function(argument)
		return "late-precommit", argument + 400
	end, unresolvedPrecommit(value)
	local forHeaderTarget = function(argument)
		return argument
	end
	local unresolvedForHeader = forHeaderTarget
	local headerTotal = 0
	for index = unresolvedForHeader(value), value do
		headerTotal += index
		unresolvedForHeader = function(argument)
			return argument + 100
		end
	end
	local guardTarget = function(argument)
		return argument >= 0
	end
	local guardReplacement = function()
		return false
	end
	local unresolvedGuard = guardTarget
	local guardResult = nil
	if unresolvedGuard(value) then
		guardResult = "positive"
		for _ = 1, 1 do
			unresolvedGuard = guardReplacement
		end
	else
		guardResult = "negative"
		for _ = 1, 1 do
			unresolvedGuard = guardReplacement
		end
	end

	local snapshotTag, snapshotValue = unresolvedSnapshot(value)
	local mutableTag, mutableValue = unresolvedMutable(value)
	local joinedTag, joinedValue = unresolvedJoined(value)
	local loopPhaseCalls = 0
	local loopAnchor = function(argument)
		loopPhaseCalls += 1
		return "loop-fixed", argument + 5
	end
	local unresolvedLoopFixed = loopAnchor
	local loopRemaining = 0
	if value >= 0 then
		loopRemaining = 2
	end
	while loopRemaining > 0 and unresolvedLoopFixed(value) do
		unresolvedLoopFixed = loopAnchor
		loopRemaining -= 1
	end
	local loopTag, loopValue = unresolvedLoopFixed(value)
	local transferAnchor = function(argument)
		return "transfer-fixed", argument + 6
	end
	local transferSteps = 0
	local unresolvedBreakFixed = transferAnchor
	while true do
		transferSteps += 1
		unresolvedBreakFixed = transferAnchor
		break
	end
	local breakTag, breakValue = unresolvedBreakFixed(value)
	local unresolvedContinueFixed = transferAnchor
	local continueRemaining = 0
	if value >= 0 then
		continueRemaining = 2
	end
	while continueRemaining > 0 do
		transferSteps += 1
		unresolvedContinueFixed = transferAnchor
		continueRemaining -= 1
		continue
	end
	local continueTag, continueValue = unresolvedContinueFixed(value)
	local immediateAnchor = function(argument)
		return "immediate", argument + 7
	end
	local unresolvedImmediate = immediateAnchor
	local immediateTag, immediateValue = (function()
		return unresolvedImmediate(value)
	end)()
	unresolvedImmediate = function(argument)
		return "late-immediate", argument + 700
	end
	local innerFutureAnchor = function(argument)
		return "inner-future", argument + 8
	end
	local unresolvedInnerFuture = innerFutureAnchor
	local innerFutureTag, innerFutureValue = (function()
		local tag, result = unresolvedInnerFuture(value)
		unresolvedInnerFuture = function(argument)
			return "late-inner-future", argument + 800
		end
		return tag, result
	end)()
	local nestedWriteAnchor = function(argument)
		return "nested-write", argument + 9
	end
	local unresolvedNestedWrite = nestedWriteAnchor
	local nestedWriteTag, nestedWriteValue = (function()
		local tag, result = unresolvedNestedWrite(value)
		do
			local _ = (function()
				unresolvedNestedWrite = function(argument)
					return "late-nested-write", argument + 900
				end
			end)()
		end
		return tag, result
	end)()
	local readChainAnchor = function(argument)
		return "read-chain", argument + 10
	end
	local unresolvedReadChain = readChainAnchor
	local readChainTag, readChainValue = (function()
		local tag, result = (function()
			return unresolvedReadChain(value)
		end)()
		unresolvedReadChain = function(argument)
			return "late-read-chain", argument + 1000
		end
		return tag, result
	end)()
	local localInvokeAnchor = function(argument)
		return "local-invoke", argument + 11
	end
	local unresolvedLocalInvoke = localInvokeAnchor
	local localInvokeTag, localInvokeValue = (function()
		local invoke = function()
			return unresolvedLocalInvoke(value)
		end
		local tag, result = invoke()
		unresolvedLocalInvoke = function(argument)
			return "late-local-invoke", argument + 1100
		end
		return tag, result
	end)()
	local localFunctionAnchor = function(argument)
		return "local-function", argument + 12
	end
	local unresolvedLocalFunction = localFunctionAnchor
	local localFunctionTag, localFunctionValue = (function()
		local function invoke()
			return unresolvedLocalFunction(value)
		end
		local tag, result = invoke()
		unresolvedLocalFunction = function(argument)
			return "late-local-function", argument + 1200
		end
		return tag, result
	end)()
	local assignedInvokeAnchor = function(argument)
		return "assigned-invoke", argument + 13
	end
	local unresolvedAssignedInvoke = assignedInvokeAnchor
	local assignedInvokeTag, assignedInvokeValue = (function()
		local invoke
		invoke = function()
			return unresolvedAssignedInvoke(value)
		end
		local tag, result = invoke()
		unresolvedAssignedInvoke = function(argument)
			return "late-assigned-invoke", argument + 1300
		end
		return tag, result
	end)()
	local aliasInvokeAnchor = function(argument)
		return "alias-invoke", argument + 14
	end
	local unresolvedAliasedInvoke = aliasInvokeAnchor
	local aliasedInvokeTag, aliasedInvokeValue = (function()
		local invoke
		invoke = function()
			return unresolvedAliasedInvoke(value)
		end
		local alias = invoke
		local tag, result = alias()
		unresolvedAliasedInvoke = function(argument)
			return "late-alias-invoke", argument + 1400
		end
		return tag, result
	end)()
	local capturedInvokeAnchor = function(argument)
		return "capture-invoke", argument + 15
	end
	local unresolvedCapturedInvoke = capturedInvokeAnchor
	local capturedInvokeTag, capturedInvokeValue = (function()
		local invoke = function()
			return unresolvedCapturedInvoke(value)
		end
		local tag, result = (function()
			return invoke()
		end)()
		unresolvedCapturedInvoke = function(argument)
			return "late-capture-invoke", argument + 1500
		end
		return tag, result
	end)()
	for _ = 1, 1 do
		unresolvedMutable = function(argument)
			return "late", argument + 200
		end
	end
	return snapshotTag, snapshotValue, mutableTag, mutableValue, joinedTag, joinedValue, precommitTag, precommitValue, headerTotal, guardResult, reads, loopTag, loopValue, breakTag, breakValue, continueTag, continueValue, transferSteps, loopPhaseCalls, immediateTag, immediateValue, innerFutureTag, innerFutureValue, nestedWriteTag, nestedWriteValue, readChainTag, readChainValue, localInvokeTag, localInvokeValue, localFunctionTag, localFunctionValue, assignedInvokeTag, assignedInvokeValue, aliasedInvokeTag, aliasedInvokeValue, capturedInvokeTag, capturedInvokeValue
end
