-- A numeric `for` whose body holds a `continue` in an `elseif` arm (an `if`/`elseif` whose continue arm stops at a
-- block other than the loop header) and a later `break` arm with a statement, so the break block stays a side exit.
return function(n, m, marker, f, g, observe)
	local acc = 0
	for i = 1, n do
		if f(i) then
			acc += i
		elseif g(i) then
			continue
		end
		if f(i, 1) then
			observe(300)
			break
		end
		observe(100)
	end
	return if m < acc then acc else marker
end
