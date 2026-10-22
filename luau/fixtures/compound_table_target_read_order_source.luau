-- Luau reads a register local that is the table or the key of a compound assignment's table target
-- twice: for the current value, before the right-hand side ran, and for the store, after it. The
-- controls: a child function's upvalue table (read once) and a right-hand side that touches nothing.
local function pair(left, right)
	return tostring(left) .. "/" .. tostring(right)
end

return function(start, step)
	local target = { field = start }
	local previous = target
	local replace = function()
		target = { 50, field = 50 }
		return step
	end
	target.field += replace()
	local byName = pair(previous.field, target.field)
	target = { start }
	previous = target
	target[1] += replace()
	local byNumber = pair(previous[1], target[1])
	local key = "a"
	local counts = { a = start, b = 100 }
	local rekey = function()
		key = "b"
		return step
	end
	counts[key] += rekey()
	local byKey = pair(counts.a, counts.b)
	local text = { value = "p" }
	local previousText = text
	local retext = function()
		text = { value = "new" }
		return "q"
	end
	text.value ..= retext()
	local concat = pair(previousText.value, text.value)
	local meta = {}
	local previousMeta = meta
	setmetatable(meta, {
		__index = function()
			meta = {}
			return start
		end,
	})
	meta.field += step
	local metamethod = pair(rawget(previousMeta, "field"), rawget(meta, "field"))
	local box = {
		bump = function()
			target.field += replace()
		end,
	}
	target = { field = start }
	previous = target
	box.bump()
	local snapshot = pair(previous.field, target.field)
	local plain = { field = start }
	local steady = function()
		return step
	end
	plain.field += steady()
	return byName, byNumber, byKey, concat, metamethod, snapshot, plain.field
end
