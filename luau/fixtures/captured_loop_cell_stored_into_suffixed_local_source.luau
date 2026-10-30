local function worker(selector, budget)
	local n = 3
	if type(selector) == "number" then
		n = selector % 4 + 1
	end
	local x_2 = nil
	local fs = {}
	for i = 1, n do
		local x = i * 3 + n
		x_2 = function()
			return x
		end
		if i % 2 == 0 then
			x = x * 2
		else
			x = x + 1
		end
		fs[i] = x_2
	end
	local s = 0
	for i = 1, #fs do
		s = s * 7 + fs[i]()
	end
	return s, n
end
return worker
