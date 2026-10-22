-- Luau reads a register local that is the table or the key of an assignment target at the store,
-- after every assigned value ran and before the statement writes its own locals. The controls keep
-- operand order: a multiple assignment that also writes the table or key local, a child function's
-- upvalue table, and a table computed by a field read.
local function pair(left, right)
	return tostring(left) .. "/" .. tostring(right)
end

return function(tag)
	local target = { kind = "old" }
	local previous = target
	local replace = function()
		target = { kind = "new" }
		return tag
	end
	target.field = replace()
	local byName = pair(previous.field, target.field)
	target = { kind = "old" }
	previous = target
	target[1] = replace()
	local byNumber = pair(previous[1], target[1])
	target = { kind = "old" }
	previous = target
	local extra = nil
	target.field, extra = replace(), tag .. "!"
	local multiple = pair(previous.field, target.field) .. "," .. tostring(extra)
	local key = "a"
	local store = {}
	local rekey = function()
		key = "b"
		return tag
	end
	store[key] = rekey()
	local byKey = pair(store.a, store.b)
	local slot = "a"
	local bag = {}
	local previousBag = bag
	local both = function()
		slot = "b"
		bag = {}
		return tag
	end
	bag[slot] = both()
	local tableAndKey = pair(previousBag.a, previousBag.b) .. "," .. pair(bag.a, bag.b)
	target = { kind = "old" }
	previous = target
	target, target.field = { kind = "new" }, tag
	local ownTableWrite = pair(previous.field, target.field)
	key = "a"
	store = {}
	key, store[key] = "b", tag
	local ownKeyWrite = pair(store.a, store.b)
	local box = {
		write = function()
			target.field = replace()
		end,
	}
	target = { kind = "old" }
	previous = target
	box.write()
	local snapshot = pair(previous.field, target.field)
	local holder = { inner = { kind = "old" } }
	local previousInner = holder.inner
	local swap = function()
		holder.inner = { kind = "new" }
		return tag
	end
	holder.inner.field = swap()
	local fieldTable = pair(previousInner.field, holder.inner.field)
	return byName, byNumber, multiple, byKey, tableAndKey, ownTableWrite, ownKeyWrite, snapshot, fieldTable
end
