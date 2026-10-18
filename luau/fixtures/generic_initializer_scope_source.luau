return function(limit)
	local score = 0
	if limit > 2 then
		score += 1
	end
	if limit > 4 then
		score += 2
	end
	if limit > 6 then
		score += 4
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
