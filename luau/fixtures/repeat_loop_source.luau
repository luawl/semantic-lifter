return function(limit)
	local value = 0
	local captures = {}
	repeat
		value = value + 1
		local reachedLimit = false
		reachedLimit = value >= limit
		local iterationValue = 0
		iterationValue = value
		captures[value] = function()
			return iterationValue
		end
		if value == 2 then
			continue
		end
		if value == 5 then
			break
		end
	until reachedLimit
	return value, captures
end
