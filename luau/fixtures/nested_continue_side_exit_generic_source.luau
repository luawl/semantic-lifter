-- A generic `for` whose body holds a `continue` nested two `if`s deep and, after it, a `break` arm with a statement
-- (so the break block is no pure forwarder and stays a loop-boundary side exit), entered twice by an outer loop
-- (so a flag that carries the break must start false on each entry).
return function(n, m, marker, f, g, observe)
	local items = {}
	for k = 1, n do
		items[k] = k
	end
	local total = 0
	for pass = 1, 2 do
		for i, v in ipairs(items) do
			if f(v) then
				if g(v) then
					continue
				end
				observe(v)
			end
			if f(v, pass) then
				observe(300 + pass)
				break
			end
			total += i
		end
		observe(100 + pass)
	end
	return if m < total then total else marker
end
