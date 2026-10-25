return function(n, m)
	local p, i, j = 0, 0, 0
	while j < m do
		j = j + 1
		repeat
			i = i + 1
			if i == n then
				p = p + 100
				break
			end
		until i % 3 == 0
		p = p + 1
	end
	return p, i
end
