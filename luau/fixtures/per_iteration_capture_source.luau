return function()
	local first
	local second
	local index = 0
	while index < 2 do
		local state = 0
		local counter = function()
			state += 1
			return state
		end
		if index == 0 then
			first = counter
		else
			second = counter
		end
		index += 1
	end
	return first, second
end
