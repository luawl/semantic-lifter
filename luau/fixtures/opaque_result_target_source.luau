local providerCalls = 0
local provider = {
	target = function()
		providerCalls += 1
		return "ignored", pcall
	end,
}

local unresolvedResultTarget
local selectedTarget = (function(_, target)
	return target
end)(provider.target())
local convergedTarget = if providerCalls == 1 then selectedTarget else selectedTarget
unresolvedResultTarget = convergedTarget

return function(value)
	local function double(input)
		return input * 2
	end
	local ok, result = unresolvedResultTarget(double, value)
	return ok, result, providerCalls
end
