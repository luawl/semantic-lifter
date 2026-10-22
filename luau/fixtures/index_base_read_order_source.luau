-- Luau reads a register local that is the table of an index expression `t[key]` at the indexing
-- instruction, after the key ran. The controls keep operand order: a child function's upvalue table
-- (a snapshot), a table computed by a field read, and a constant key.
local function parameterTable(list)
	local replace = function()
		list = { 7, 8 }
		return 1
	end
	return list[replace()]
end

return function(first, second)
	local data = { first, second }
	local replace = function()
		data = { 100, 200 }
		return 1
	end
	local plain = data[replace()]
	data = { first, second }
	local arithmetic = data[replace() + 1]
	data = { first, second }
	local grouped = (data)[replace()]
	local keyMeta = setmetatable({}, {
		__add = function()
			data = { 100, 200 }
			return 1
		end,
	})
	data = { first, second }
	local metamethod = data[keyMeta + 0]
	local loopValues = {}
	for index = 1, 2 do
		local cell = { index, index }
		local reset = function()
			cell = { 100 * index, 0 }
			return 1
		end
		loopValues[index] = cell[reset()]
	end
	local parameter = parameterTable({ first, second })
	local box = {
		read = function()
			return data[replace()]
		end,
	}
	data = { first, second }
	local snapshot = box.read()
	data = { first, second }
	local constantKey = data[2]
	local holder = { list = { first, second } }
	local swap = function()
		holder.list = { 100, 200 }
		return 1
	end
	local fieldTable = holder.list[swap()]
	return plain, arithmetic, grouped, metamethod, loopValues[1], loopValues[2], parameter, snapshot, constantKey, fieldTable
end
