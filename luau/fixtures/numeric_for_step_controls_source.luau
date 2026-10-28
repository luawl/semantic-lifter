local function steps(first, last, step)
	local down = 0
	local odd = 0
	local given = 0
	for i = last, first, -1 do
		down = down * 10 + i
	end
	for i = first, last, 2 do
		odd = odd + i
	end
	for i = first, last, step do
		given = given + i
	end
	return down, odd, given
end
return steps
