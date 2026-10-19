-- Luau reads a register local named by the left operand of an arithmetic or comparison operator
-- at the operator, after the right operand ran. The controls stay in operand order: the arguments of
-- a generic call (Luau reads a builtin fast call's register argument and a method call's receiver
-- late; neither is used here), concatenation operands, and a child function's upvalue snapshot.
local function parameterSum(value)
	local reset = function()
		value = 100
		return 0
	end
	return value + reset()
end

return function(initial, increment)
	local state = initial
	local bump = function()
		state = 100
		return increment
	end
	local bumpTo = function(result)
		state = 100
		return result
	end
	local sum = state + bump()
	state = initial
	local grouped = (state) * (bump() + 1)
	state = initial
	local equal = state == bumpTo(100)
	state = initial
	local ordered = state < bumpTo(50)
	local steps = 0
	state = initial
	while state < (function()
		steps += 1
		state += 100
		return 50
	end)() do
		steps += 10
	end
	local loopSums = {}
	for index = 1, 2 do
		local cell = index
		local reset = function()
			cell = 100
			return 0
		end
		loopSums[index] = cell + reset()
	end
	local proxy = setmetatable({}, {
		__index = function()
			state = 100
			return increment
		end,
	})
	state = initial
	local metamethod = state + proxy.field
	state = initial
	local first, second = (function(...)
		return ...
	end)(state, bump())
	state = initial
	local joined = state .. bump()
	local box = {
		read = function()
			return state + bump()
		end,
	}
	state = initial
	local snapshot = box.read()
	return sum, grouped, equal, ordered, steps, loopSums[1], loopSums[2], parameterSum(initial), metamethod, first, second, joined, snapshot
end
