return function(limit)
	local score = 0
	if limit > 2 then
		score += 1
	end
	if limit > 4 then
		score += 2
	end
	if limit > 6 then
		score += 3
	end
	if limit > 8 then
		score += 4
	end
	if limit > 10 then
		score += 5
	end
	if limit > 12 then
		score += 6
	end
	if limit > 14 then
		score += 7
	end
	if limit > 16 then
		score += 8
	end
	if limit > 18 then
		score += 9
	end
	if limit > 20 then
		score += 10
	end
	if limit > 22 then
		score += 11
	end
	if limit > 24 then
		score += 12
	end
	if limit > 26 then
		score += 13
	end
	if limit > 28 then
		score += 14
	end
	if limit > 30 then
		score += 15
	end
	local order = {}
	for index = 1, limit do
		order[index] = (index * 7) % 11
	end
	table.sort(order)
	local parts = {}
	for position, entry in ipairs(order) do
		parts[position] = tostring(entry)
	end
	return table.concat(parts, ","), score
end
