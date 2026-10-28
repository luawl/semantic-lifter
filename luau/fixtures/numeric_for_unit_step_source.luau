local function compute(items, callback)
	local total = 0
	for i = 1, #items do
		total = total + callback(items[i])
	end
	return total
end
return compute
