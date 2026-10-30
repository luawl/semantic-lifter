local function worker(selector, budget)
	local total = 0
	local rounds = 0
	repeat
		if selector == 1000 then
			total = total + selector
		end
		rounds += 1
		if selector == 4 then
			total = total + 2
			if budget > 7 then
				continue
			end
			total = total + 1
		elseif selector == 3 then
			if budget > 1 then
				continue
			end
			total = total + 4
		end
		total = total + 1
	until rounds >= 5 or total >= 6 or budget > 5
	return total
end
return worker
