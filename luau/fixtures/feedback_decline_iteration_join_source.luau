return function(n, a, b)
	local s = 0
	for i = 1, n do
		if i == a then
			while true do
				for k = 1, 3 do
					s += k
				end
			end
		elseif i == b then
			while true do
			end
		end
		s += i
	end
	return s
end
