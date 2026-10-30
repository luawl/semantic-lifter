local function worker(selector, budget)
	local passes = 3
	if type(budget) == "number" and budget >= 1 and budget <= 11 then
		passes = 1 + budget % 4
	end
	local scale = 5
	if type(selector) == "number" then
		scale = selector
	end
	local fns = {}
	local total = 0
	for i = 1, passes do
		local j = i
		local i = j * scale + 1
		total += i
		fns[j] = function()
			return i
		end
		total += fns[j]()
	end
	local acc = {}
	acc[1] = total + 1
	acc[2] = total + 2
	acc[3] = total + 3
	acc[4] = total + 4
	acc[5] = total + 5
	acc[6] = total + 6
	acc[7] = total + 7
	acc[8] = total + 8
	acc[9] = total + 9
	acc[10] = total + 10
	acc[11] = total + 11
	acc[12] = total + 12
	acc[13] = total + 13
	acc[14] = total + 14
	acc[15] = total + 15
	acc[16] = total + 16
	acc[17] = total + 17
	acc[18] = total + 18
	acc[19] = total + 19
	acc[20] = total + 20
	acc[21] = total + 21
	acc[22] = total + 22
	acc[23] = total + 23
	acc[24] = total + 24
	acc[25] = total + 25
	acc[26] = total + 26
	acc[27] = total + 27
	acc[28] = total + 28
	acc[29] = total + 29
	acc[30] = total + 30
	acc[31] = total + 31
	acc[32] = total + 32
	acc[33] = total + 33
	acc[34] = total + 34
	acc[35] = total + 35
	acc[36] = total + 36
	acc[37] = total + 37
	acc[38] = total + 38
	acc[39] = total + 39
	acc[40] = total + 40
	return total, #fns, acc[40]
end
return worker
