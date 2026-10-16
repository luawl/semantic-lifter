return function(limit)
	local getters = {}
	local setters = {}
	local index = 0
	while index < limit do
		index += 1
		local state = index * 10
		getters[index] = function()
			return state
		end
		if index % 2 == 0 then
			state += 1
		end
		setters[index] = function(delta)
			state += delta
		end
		state *= 2
	end
	return getters, setters
end
