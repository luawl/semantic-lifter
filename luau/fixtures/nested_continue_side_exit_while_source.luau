-- A `while` loop whose body holds a `continue` nested two `if`s deep and a later bare `break`.
return function(n, m, marker, f, g, observe)
	local i = 0
	while i < n do
		i += 1
		if f(i) then
			if g(i) then
				continue
			end
			observe(i)
		end
		if f(i, 1) then
			break
		end
		observe(100)
	end
	return if m < i then i else marker
end
