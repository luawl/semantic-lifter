-- At its default optimisation level (1) Luau calls a builtin with two or three fixed arguments through
-- FASTCALL2 or FASTCALL3, which reads a register-local argument at the call, after the later arguments
-- ran; a never-written local alias of a builtin is a builtin too. The controls keep operand order: an
-- open last argument (a generic CALL), a function that is not a builtin, four arguments, and a
-- builtin read from a table field.
local function larger(a, b)
	if a > b then
		return a
	end
	return b
end

return function(initial)
	local count = initial
	local bump = function()
		count = 10
		return 0
	end
	local maximum = math.max(count, (bump()))
	count = initial
	local arithmetic = math.max(count, bump() - 5)
	count = initial
	local clamped = math.clamp(count, (bump()), 100)
	count = initial
	local same = rawequal(count, (bump()) + 10)
	local list = {}
	local previousList = list
	local relist = function()
		list = {}
		return "item"
	end
	table.insert(list, (relist()))
	local inserted = tostring(#previousList) .. "/" .. tostring(#list)
	local text = "abc"
	local retext = function()
		text = "xyz"
		return 1
	end
	local sub = string.sub(text, (retext()), 2)
	local alias = math.max
	count = initial
	local aliased = alias(count, (bump()))
	count = initial
	local openLast = math.max(count, bump())
	count = initial
	local generic = larger(count, (bump()))
	count = initial
	local fourArguments = bit32.bor(count, (bump()), 0, 0)
	local library = { max = math.max }
	count = initial
	local fieldCallee = library.max(count, (bump()))
	return maximum, arithmetic, clamped, same, inserted, sub, aliased, openLast, generic, fourArguments, fieldCallee
end
