-- Luau hands a register local that is the value of a multiple assignment's table target to the store,
-- after every value ran and before the statement writes its own locals. The controls keep operand
-- order: a local target's value, a child function's upvalue value, a single assignment, and a statement
-- that writes the value's own local (the store takes the value from before the statement).
local function pair(left, right)
	return tostring(left) .. "/" .. tostring(right)
end

local function parameterValue(value)
	local target = {}
	local replace = function()
		value = "new"
		return 5
	end
	target.x, target.y = value, replace()
	return pair(target.x, target.y)
end

return function(seed)
	local value = seed
	local target = {}
	local other = nil
	local replace = function()
		value = "new"
		return 5
	end
	target.x, other = value, replace()
	local fieldLocal = pair(target.x, other)
	value = seed
	target = {}
	target.x, target.y = value, replace()
	local twoFields = pair(target.x, target.y)
	value = seed
	target = {}
	local key = "x"
	target[key], target.y = value, replace()
	local keyed = pair(target.x, target.y)
	local parameter = parameterValue(seed)
	value = seed
	target = {}
	other, target.y = value, replace()
	local localTarget = pair(other, target.y)
	local box = {
		write = function()
			target.x, target.y = value, replace()
		end,
	}
	value = seed
	target = {}
	box.write()
	local snapshot = pair(target.x, target.y)
	value = seed
	target = {}
	target.x = value
	value = "new"
	local single = tostring(target.x)
	value = seed
	target = {}
	value, target.x = "new", value
	local ownWrite = pair(value, target.x)
	return fieldLocal, twoFields, keyed, parameter, localTarget, snapshot, single, ownWrite
end
