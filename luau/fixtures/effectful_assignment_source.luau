return function(seed)
	local calls = 0
	local state = seed
	local function produce(delta)
		calls += 1
		return state + delta, "ignored"
	end
	local function fixedResult()
		return (produce(6))
	end

	state = produce(5)
	local fixed, leaked = fixedResult()
	return state, calls, fixed, leaked
end
