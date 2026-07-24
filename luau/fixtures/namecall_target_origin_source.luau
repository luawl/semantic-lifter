local order = ""

local function makeReceiver(tag, delta)
	local receiver = { tag = tag, delta = delta }
	return setmetatable(receiver, {
		__index = function(tableValue, key)
			order = order .. "m"
			assert(tableValue == receiver)
			assert(key == "dispatch")
			return function(self, value)
				order = order .. "c"
				assert(self == receiver)
				return self.tag, value + self.delta
			end
		end,
	})
end

local function argument(value)
	order = order .. "a"
	return value
end

local immutableReceiver = makeReceiver("value-receiver", 1)
local unresolvedValue = immutableReceiver

local mutableReceiver = makeReceiver("stale", 0)
local unresolvedPlace = mutableReceiver
mutableReceiver = makeReceiver("place-receiver", 2)
unresolvedPlace = mutableReceiver

semantic_lifter_origin_method_receiver = makeReceiver("environment-receiver", 3)
local unresolvedEnvironment = semantic_lifter_origin_method_receiver

return function(value)
	order = ""
	local valueTag, valueResult = unresolvedValue:dispatch(argument(value))
	local placeTag, placeResult = unresolvedPlace:dispatch(argument(value))
	local environmentTag, environmentResult = unresolvedEnvironment:dispatch(argument(value))
	return valueTag, valueResult, placeTag, placeResult, environmentTag, environmentResult, order
end
