local function worker(selector, budget)
	local total = 0
	local rounds = 0
	repeat
		rounds = rounds + 1
		if budget < 2 then
			total = total + 1
		elseif total % 3 == 0 then
			if selector == 3 then
				break
			elseif selector == 2 then
				total = total + 7
				continue
			end
			total = total + 4
			continue
		else
			if selector == 4 then
				break
			end
		end
		total = total + 100
	until total >= 6 or rounds >= 5
	return total, rounds
end
return worker
