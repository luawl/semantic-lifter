-- An inner numeric `for` whose `continue` sits two `if`s deep, so its body is written inside a transfer wrapper, and
-- whose `break` the resolver plans as a loop-boundary exit carried by the exit's escape flag; an outer numeric `for`
-- enters it again on every pass, so the flag must start false on each entry of the inner loop.
return function(n, m, marker, f, g, observe)
	local total = 0
	for pass = 1, m do
		local acc = 0
		for i = 1, n do
			if i > 1 then
				if i > pass + 1 then
					continue
				end
			end
			acc += 1
			observe(i)
			if acc > 1 then
				break
			end
		end
		total = total * 10 + acc
	end
	return total
end
