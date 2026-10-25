-- Closures stored into a field of a parenthesized nil: one in a loop body right after the local the closure captures,
-- and one right after a call statement. A store into nil raises when it runs, after the calls before it.
return function(observe, count, fail)
	observe("start")
	for index = 1, count do
		local seen = observe(index);
		(nil).captured = function()
			return seen
		end
	end
	if fail then
		observe("store");
		(nil).handler = function()
			return count
		end
	end
	return observe("finish")
end
