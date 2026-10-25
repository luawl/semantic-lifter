-- A numeric `for` whose body holds a `continue` nested two `if`s deep and a later `break` that itself sits two `if`s
-- deep, in an unwrapped arm under the loop body's wrapper, with a statement before the `break` so its block is a side
-- exit.
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
			if acc > m then
				observe(300)
				break
			end
			acc += 1
		end
		observe(100)
	end
	return if m < acc then acc else marker
end
