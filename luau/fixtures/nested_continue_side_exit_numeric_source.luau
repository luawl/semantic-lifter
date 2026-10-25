-- A numeric `for` whose body holds a `continue` nested two `if`s deep and a later `break` arm with a statement.
return function(n, m, marker, f, g, observe)
	local acc = 0
	for i = 1, n do
		if f(i) then
			if g(i) then
				continue
			end
			acc += i
		end
		if f(i, 1) then
			observe(300)
			break
		end
		observe(100)
	end
	return if m < acc then acc else marker
end
