return function(value)
	local calls = 0
	local probe = function(result)
		calls = calls + 1
		return result
	end
	local first = value or probe("fallback")
	local second = false and probe("never")
	local placed = ""
	local order = ""
	local condition = function()
		order ..= "c"
		return value ~= nil
	end
	local arm = function(result)
		order ..= result
		return result
	end
	placed = if condition() then arm("t") else arm("f")
	local reads = 0
	local getRecord = function()
		reads += 1
		return { selected = value }
	end
	local selected = getRecord().selected or "missing"
	local typedAnd = value ~= nil and true
	local typedOr = value == nil or false
	return first, second, calls, placed, order, selected, reads, typedAnd, typedOr
end
