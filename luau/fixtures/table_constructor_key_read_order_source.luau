-- Luau hands a register local that is a table constructor's key to the item's store, after the item's
-- value ran. The controls keep operand order: a child function's upvalue key, a replacing call in an
-- earlier item, and a list item, which is copied in order.
local function pair(left, right)
	return tostring(left) .. "/" .. tostring(right)
end

local function parameterKey(key)
	local replace = function()
		key = "b"
		return 1
	end
	local made = { [key] = replace() }
	return pair(made.a, made.b)
end

return function(seed)
	local key = seed
	local other = "z"
	local replace = function()
		key = "b"
		return 1
	end
	local made = { [key] = replace() }
	local literal = pair(made.a, made.b)
	key = seed
	made = { [key] = replace(), [other] = 2 }
	local ordered = pair(made.a, made.b) .. "," .. tostring(made.z)
	key = seed
	made = { [(key)] = (replace()) }
	local grouped = pair(made.a, made.b)
	local parameter = parameterKey(seed)
	key = seed
	local box = {
		build = function()
			return { [key] = replace() }
		end,
	}
	made = box.build()
	local snapshot = pair(made.a, made.b)
	key = seed
	made = { a = replace(), [key] = 2 }
	local earlierItem = pair(made.a, made.b)
	local item = "old"
	local renew = function()
		item = "new"
		return item
	end
	made = { item, renew() }
	local listItem = pair(made[1], made[2])
	return literal, ordered, grouped, parameter, snapshot, earlierItem, listItem
end
