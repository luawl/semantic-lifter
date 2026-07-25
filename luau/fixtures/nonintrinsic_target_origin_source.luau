local immutableOrigin = function(value)
	return "value", value + 1
end
local unresolvedValue = immutableOrigin

local function mutableOrigin(value)
	return "before", value
end
local unresolvedPlace = mutableOrigin
mutableOrigin = function(value)
	return "place", value + 2
end
unresolvedPlace = mutableOrigin

semantic_lifter_origin_environment = function(value)
	return "environment", value + 3
end
local unresolvedEnvironment = semantic_lifter_origin_environment

local function localFunctionFactory()
	local function localFunctionOrigin(value)
		return "local-function", value + 4
	end
	return localFunctionOrigin
end
local unresolvedLocalFunction = localFunctionFactory()

local function conditionalFactory(useFirst)
	if (not useFirst) and true then
		return function(value)
			return "conditional-true", value + 5
		end
	else
		return function(value)
			return "conditional-false", value + 6
		end
	end
end
local unresolvedConditional = conditionalFactory(nil)

local function conditionalExpressionFactory(useFirst)
	return if (not useFirst) or false
		then function(value)
			return "conditional-expression-true", value + 7
		end
		else function(value)
			return "conditional-expression-false", value + 8
		end
end
local unresolvedConditionalExpression = conditionalExpressionFactory(0)

return function(value)
	local valueTag, valueResult = unresolvedValue(value)
	local placeTag, placeResult = unresolvedPlace(value)
	local environmentTag, environmentResult = unresolvedEnvironment(value)
	local localFunctionTag, localFunctionResult = unresolvedLocalFunction(value)
	local conditionalTag, conditionalResult = unresolvedConditional(value)
	local conditionalExpressionTag, conditionalExpressionResult = unresolvedConditionalExpression(value)
	return valueTag, valueResult, placeTag, placeResult, environmentTag, environmentResult,
		localFunctionTag, localFunctionResult, conditionalTag, conditionalResult,
		conditionalExpressionTag, conditionalExpressionResult
end
