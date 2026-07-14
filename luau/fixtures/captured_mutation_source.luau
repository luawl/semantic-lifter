return function(start)
	local state = start
	return function(delta)
		state = state + delta
		return state
	end
end
