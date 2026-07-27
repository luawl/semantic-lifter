return function(key, value)
	local record = { fixed = 3 }
	record[key] = value
	local dynamic = record[key]
	local order = 0
	local leftRecord = function()
		order = order * 10 + 1
		return record
	end
	local rightKey = function()
		order = order * 10 + 2
		return key
	end
	local nested = leftRecord()[rightKey()]
	local metamethodEffects = ""
	local stored = {}
	local proxy = setmetatable({}, {
		__newindex = function(_, writtenKey, writtenValue)
			metamethodEffects ..= "w"
			stored[writtenKey] = writtenValue
		end,
		__index = function(_, readKey)
			metamethodEffects ..= "r"
			return stored[readKey]
		end,
	})
	local proxyValue = function()
		metamethodEffects ..= "v"
		return value + 1
	end
	proxy.slot = proxyValue()
	local proxyRead = proxy.slot
	local function environmentWorker()
		return redirected
	end
	local environment = setmetatable({}, {
		__index = function(_, name)
			metamethodEffects ..= "e"
			if name == "redirected" then
				return value + 20
			end
			return nil
		end,
	})
	setfenv(environmentWorker, environment)
	local environmentRead = environmentWorker()
	local environmentMatches = getfenv(environmentWorker) == environment
	return record.fixed + dynamic, nested, order, proxyRead, metamethodEffects, environmentRead, environmentMatches
end
