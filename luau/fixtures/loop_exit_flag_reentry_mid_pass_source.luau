-- The same re-entered inner numeric `for` with a second `continue` inside the `if` arm that holds its `break`, so the
-- exit arm sits two transfer wrappers deep and work follows it in the arm and after the arm: the first consumer a pass
-- reaches reads the exit's escape flag, so a flag left set by the outer loop's previous pass would end the inner loop
-- part way through its first pass.
return function(n, m, marker, f, g, observe)
	local total = 0
	for _ = 1, 2 do
		local acc = 0
		for i = 1, n do
			if i > 1 then
				if i > 2 then
					continue
				end
			end
			if i > 0 then
				if i > m then
					if acc > 5 then
						continue
					end
				end
				acc += 1
				if acc > 1 then
					break
				end
				acc += 10
				observe(10 * i)
			end
			acc += 100
			observe(100 * i)
		end
		total = total * 1000 + acc
	end
	return total
end
