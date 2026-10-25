local function worker(selector, budget)
	local total = 0
	local rounds = 0
	if selector == 1000 then
		local a0_0 = selector * 2
		local a0_1 = selector * 3
		local a0_2 = selector * 4
		local a0_3 = selector * 5
		local a0_4 = selector * 6
		local a0_5 = selector * 7
		total = total + a0_0
		total = total + a0_1
		total = total + a0_2
		total = total + a0_3
		total = total + a0_4
		total = total + a0_5
		total = total - a0_0
		total = total - a0_1
		total = total - a0_2
		total = total - a0_3
		total = total - a0_4
		total = total - a0_5
	elseif selector == 1001 then
		local a1_0 = selector * 2
		local a1_1 = selector * 3
		local a1_2 = selector * 4
		local a1_3 = selector * 5
		local a1_4 = selector * 6
		local a1_5 = selector * 7
		total = total + a1_0
		total = total + a1_1
		total = total + a1_2
		total = total + a1_3
		total = total + a1_4
		total = total + a1_5
		total = total - a1_0
		total = total - a1_1
		total = total - a1_2
		total = total - a1_3
		total = total - a1_4
		total = total - a1_5
	end
	repeat
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
