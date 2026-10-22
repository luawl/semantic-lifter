--!optimize 2
-- The source asks for optimisation level 2, whose inliner changes what the program reads, so the source
-- frontend refuses it with unsupported_optimization_level instead of lifting it under the level-1 rule.
return function(seed)
	local count = seed
	local bump = function()
		count = 10
		return 0
	end
	return math.max(count, (bump()))
end
