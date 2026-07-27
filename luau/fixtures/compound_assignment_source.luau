local function probeEnvironment(initial, increment)
	local effects = ""
	local store = { redirected = initial }
	local environment = setmetatable({}, {
		__index = function(_, name)
			effects ..= "r"
			return store[name]
		end,
		__newindex = function(_, name, value)
			effects ..= "w"
			store[name] = value
		end,
	})
	local function worker()
		local function right()
			effects ..= "v"
			return increment
		end
		redirected += right()
		return redirected
	end
	setfenv(worker, environment)
	local result = worker()
	return result, effects, store.redirected, getfenv(worker) == environment
end

return function(initial, increment)
	local calls = 0
	local object = { value = initial }
	local key = function()
		calls += 1
		return "value"
	end
	local right = function()
		object.value = 100
		return increment
	end
	object[key()] += right()
	local state = initial
	local proxy = setmetatable({}, {
		__add = function()
			state = 100
			return increment
		end,
	})
	state += proxy + 0
	semantic_lifter_compound_global_probe = initial
	local globalRight = function()
		semantic_lifter_compound_global_probe = 100
		return increment
	end
	semantic_lifter_compound_global_probe += globalRight()
	local globalResult = semantic_lifter_compound_global_probe
	semantic_lifter_compound_global_probe = nil
	local environmentResult, environmentEffects, storedEnvironmentValue, environmentMatches = probeEnvironment(initial, increment)
	local concatState = "old"
	local concatRight = setmetatable({}, {
		__concat = function()
			concatState = "new"
			return "rhs"
		end,
	})
	concatState ..= concatRight .. ""
	return object.value, calls, state, globalResult, concatState, environmentResult, environmentEffects, storedEnvironmentValue, environmentMatches
end
