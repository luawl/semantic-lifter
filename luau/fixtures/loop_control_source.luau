return function(limit)
	local total = 0
	local index = 0
	while index < limit do
		index = index + 1
		if index == 3 then
			continue
		end
		if index == 6 then
			break
		end
		total = total + index
	end
	return total
end
