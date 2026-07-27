return function(limit)
	local total = 0
	local index = 0
	while index < limit do
		index = index + 1
		if index % 2 == 0 then
			total = total + index
		end
	end
	local function guarded(start)
		while start ~= nil and start < limit do
			if start % 2 == 0 then
				if start == 2 then
					return "early", start
				end
			end
			start += 1
		end
		if start == nil then
			return "nil", -1
		end
		return "exit", start
	end
	local function nestedShared(op, count, seed)
		local value = seed
		while true do
			if op == 1 then
				value += 1
				op = 2
			elseif op == 2 then
				if count == 0 then
					return "nested-done", value
				end
				local steps = count
				count = 0
				for nested = steps, 1, -1 do
					value += nested
				end
			elseif op == 3 then
				value += 3
				op = 2
			elseif op == 4 then
				value += 4
				op = 2
			else
				op = 1
			end
		end
	end
	local earlyTag, earlyValue = guarded(0)
	local exitTag, exitValue = guarded(limit)
	local nilTag, nilValue = guarded(nil)
	local nestedEarlyTag, nestedEarlyValue = nestedShared(2, 0, 0)
	local nestedDoneTag, nestedDoneValue = nestedShared(1, 3, 0)
	local nestedFallbackTag, nestedFallbackValue = nestedShared(0, 2, 2)
	local nestedForwardedThreeTag, nestedForwardedThreeValue = nestedShared(3, 0, 10)
	local nestedForwardedFourTag, nestedForwardedFourValue = nestedShared(4, 0, 10)
	return total, earlyTag, earlyValue, exitTag, exitValue, nilTag, nilValue,
		nestedEarlyTag, nestedEarlyValue, nestedDoneTag, nestedDoneValue, nestedFallbackTag, nestedFallbackValue,
		nestedForwardedThreeTag, nestedForwardedThreeValue, nestedForwardedFourTag, nestedForwardedFourValue
end
