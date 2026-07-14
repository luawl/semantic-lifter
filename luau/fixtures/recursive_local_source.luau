return function(input)
	local function factorial(value)
		if value <= 1 then
			return 1
		end
		return value * factorial(value - 1)
	end
	return factorial(input)
end
