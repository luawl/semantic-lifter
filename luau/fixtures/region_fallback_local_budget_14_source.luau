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
		local a0_6 = selector * 8
		local a0_7 = selector * 9
		local a0_8 = selector * 10
		local a0_9 = selector * 11
		local a0_10 = selector * 12
		local a0_11 = selector * 13
		local a0_12 = selector * 14
		local a0_13 = selector * 15
		total = total + a0_0
		total = total + a0_1
		total = total + a0_2
		total = total + a0_3
		total = total + a0_4
		total = total + a0_5
		total = total + a0_6
		total = total + a0_7
		total = total + a0_8
		total = total + a0_9
		total = total + a0_10
		total = total + a0_11
		total = total + a0_12
		total = total + a0_13
		total = total - a0_0
		total = total - a0_1
		total = total - a0_2
		total = total - a0_3
		total = total - a0_4
		total = total - a0_5
		total = total - a0_6
		total = total - a0_7
		total = total - a0_8
		total = total - a0_9
		total = total - a0_10
		total = total - a0_11
		total = total - a0_12
		total = total - a0_13
	elseif selector == 1001 then
		local a1_0 = selector * 2
		local a1_1 = selector * 3
		local a1_2 = selector * 4
		local a1_3 = selector * 5
		local a1_4 = selector * 6
		local a1_5 = selector * 7
		local a1_6 = selector * 8
		local a1_7 = selector * 9
		local a1_8 = selector * 10
		local a1_9 = selector * 11
		local a1_10 = selector * 12
		local a1_11 = selector * 13
		local a1_12 = selector * 14
		local a1_13 = selector * 15
		total = total + a1_0
		total = total + a1_1
		total = total + a1_2
		total = total + a1_3
		total = total + a1_4
		total = total + a1_5
		total = total + a1_6
		total = total + a1_7
		total = total + a1_8
		total = total + a1_9
		total = total + a1_10
		total = total + a1_11
		total = total + a1_12
		total = total + a1_13
		total = total - a1_0
		total = total - a1_1
		total = total - a1_2
		total = total - a1_3
		total = total - a1_4
		total = total - a1_5
		total = total - a1_6
		total = total - a1_7
		total = total - a1_8
		total = total - a1_9
		total = total - a1_10
		total = total - a1_11
		total = total - a1_12
		total = total - a1_13
	end
	while rounds < 8 do
		rounds += 1
		total += rounds
		if selector == 5 or budget > 4 then
			continue
		end
	end
	return total, rounds
end
return worker
