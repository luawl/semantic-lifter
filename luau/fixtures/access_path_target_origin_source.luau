local immutableNamespace = {
	dispatch = function(value)
		return "value", value + 1
	end,
}
local unresolvedValue = immutableNamespace.dispatch

local mutableNamespace = {
	dispatch = function(value)
		return "before", value
	end,
}
local unresolvedPlace = mutableNamespace.dispatch
mutableNamespace = {
	dispatch = function(value)
		return "place", value + 2
	end,
}
unresolvedPlace = mutableNamespace.dispatch

semantic_lifter_origin_namespace = {
	dispatch = function(value)
		return "environment", value + 3
	end,
}
local unresolvedEnvironment = semantic_lifter_origin_namespace.dispatch

return function(value)
	local valueTag, valueResult = unresolvedValue(value)
	local placeTag, placeResult = unresolvedPlace(value)
	local environmentTag, environmentResult = unresolvedEnvironment(value)
	return valueTag, valueResult, placeTag, placeResult, environmentTag, environmentResult
end
