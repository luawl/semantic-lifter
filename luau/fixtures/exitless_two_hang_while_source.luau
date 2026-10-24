return function(count)
	local total, k = 0, 0
	while k < count do
		k += 1
		if k == 64 then
			while true do end
		end
		if k == 128 then
			while true do end
		end
		total += k
	end
	return total
end
