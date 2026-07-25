local immutableKey = "dispatch"
local immutableNamespace = {
	dispatch = function(value)
		return "value-key", value + 1
	end,
}
local unresolvedValue = immutableNamespace[immutableKey]

local mutableKey = "before"
local mutableNamespace = {
	before = function(value)
		return "stale", value
	end,
}
local unresolvedPlace = mutableNamespace[mutableKey]
mutableKey = "after"
mutableNamespace = {
	after = function(value)
		return "place-key", value + 2
	end,
}
unresolvedPlace = mutableNamespace[mutableKey]

semantic_lifter_origin_dynamic_namespace = {
	dispatch = function(value)
		return "environment-key", value + 3
	end,
}
semantic_lifter_origin_dynamic_key = "dispatch"
local unresolvedEnvironment = semantic_lifter_origin_dynamic_namespace[semantic_lifter_origin_dynamic_key]

local computedIndex = 2
local computedNamespace = {
	[1] = function(value)
		return "expression-key", value + 4
	end,
}
local unresolvedExpression = computedNamespace[computedIndex - 1]

return function(value)
	local valueTag, valueResult = unresolvedValue(value)
	local placeTag, placeResult = unresolvedPlace(value)
	local environmentTag, environmentResult = unresolvedEnvironment(value)
	local expressionTag, expressionResult = unresolvedExpression(value)
	return valueTag, valueResult, placeTag, placeResult, environmentTag, environmentResult, expressionTag, expressionResult
end
