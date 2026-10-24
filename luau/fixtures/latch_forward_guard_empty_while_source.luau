return function(count)
	local k = 0
	local function step()
		k += 1
		return k < count
	end
	while step() do end
	return k
end
