-- Luau passes a register local that is the receiver of a method call `o:m(...)` to NAMECALL, which
-- runs after the arguments, so the receiver is read after they ran. Every argument here is fixed (a
-- grouped call or a call before another argument). The controls keep operand order: a receiver
-- computed by a field read and a child function's upvalue receiver.
local Proto = {}
Proto.__index = Proto
function Proto:who(_unused)
	return self.tag
end
function Proto:add(item)
	table.insert(self.items, item)
	return #self.items
end

local function make(tag)
	return setmetatable({ tag = tag, items = {} }, Proto)
end

return function(width)
	local object = make("old")
	local replace = function()
		object = make("new")
		return 0
	end
	local grouped = object:who((replace()))
	object = make("old")
	local leading = object:who(replace(), width)
	object = make("old")
	local wrapped = (object):who((replace()))
	object = make("old")
	local previous = object
	object:add((replace()))
	local statement = tostring(#previous.items) .. "/" .. tostring(#object.items)
	local text = "ab"
	local retext = function()
		text = "xyz"
		return width
	end
	local repeated = text:rep((retext()))
	local loopTags = {}
	for index = 1, 2 do
		local cell = make("old" .. index)
		local reset = function()
			cell = make("new" .. index)
			return 0
		end
		loopTags[index] = cell:who((reset()))
	end
	local holder = { object = make("old") }
	local swap = function()
		holder.object = make("new")
		return 0
	end
	local fieldReceiver = holder.object:who(swap())
	local box = {
		ask = function()
			return object:who((replace()))
		end,
	}
	object = make("old")
	local snapshot = box.ask()
	return grouped, leading, wrapped, statement, repeated, loopTags[1], loopTags[2], fieldReceiver, snapshot
end
