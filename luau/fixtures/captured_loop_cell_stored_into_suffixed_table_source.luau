local function worker(selector, budget)
	local n = 3
	if type(selector) == "number" then
		n = selector % 4 + 1
	end
	local t_2 = {}
	for i = 1, n do
		local t = i * 5 + n
		t_2[i] = function()
			return t
		end
		if i % 2 == 0 then
			t = t * 2
		else
			t = t + 1
		end
	end
	local s = 0
	for i = 1, #t_2 do
		s = s * 7 + t_2[i]()
	end
	return s, n
end
return worker
