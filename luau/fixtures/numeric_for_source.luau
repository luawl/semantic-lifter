return function(initial: any, limit: any, step: any)
	local total = 0
	local first: (() -> number)? = nil
	local last: (() -> number)? = nil
	for index = initial, limit, step do
		local capture = function()
			return index
		end
		if first == nil then
			first = capture
		end
		last = capture
		total += index
	end
	local firstOnly = 0
	for index = initial, limit, step do
		firstOnly = index
		break
	end
	local emptyFirstOnly = 0
	for index = 1, 0, 1 do
		emptyFirstOnly = index
		break
	end
	return total, first, last, firstOnly, emptyFirstOnly
end
