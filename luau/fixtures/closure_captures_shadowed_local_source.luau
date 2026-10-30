local function worker(selector, budget)
	local base = 3
	if type(budget) == "number" then
		base = budget
	end
	local x = base * 3 + 1
	local x = function()
		return x * 10
	end
	local r = x()
	x = nil
	return r
end
return worker
