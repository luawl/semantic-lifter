return function(sink)
	local count = 1
	local function bump()
		count = count + 10
		return 0
	end
	sink(count, bump())
	return count
end
