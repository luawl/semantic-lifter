-- A loop with two continues. The second sits in a loop-boundary body (`if g(i1) then ... else return i1 end`) and
-- reaches the loop header through an escape flag, so the arm `if f(i1) then ... end` that holds both continues is
-- written inside a transfer wrapper; the first continue sits in that arm and must still start the next pass.
return function(n, m, marker, f, g, observe)
	local i = 0
	while true do
		local i1 = i + 1
		if f(i1) then
			if f(i1, 1) then
				i = i1
				continue
			end
			if g(i1) then
				if observe(i1) then
					observe(250)
					i = i1
					continue
				end
			else
				return i1
			end
		end
		observe(100)
		if n < i1 then
			return marker
		end
		i = i1
	end
end
