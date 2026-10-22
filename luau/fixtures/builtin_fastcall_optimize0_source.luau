--!optimize 0
-- At optimisation level 0 (the hot comment above, before the first token) Luau compiles no builtin
-- fast call, so every argument of a builtin is copied in operand order.
return function(initial)
	local count = initial
	local bump = function()
		count = 10
		return 0
	end
	local maximum = math.max(count, (bump()))
	count = initial
	local clamped = math.clamp(count, (bump()), 100)
	local alias = math.max
	count = initial
	local aliased = alias(count, (bump()))
	return maximum, clamped, aliased
end
