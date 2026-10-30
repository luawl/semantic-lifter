local function worker(selector, budget)
	local base = 2
	if type(budget) == "number" then
		base = budget
	end
	local acc = {}
	local log = function(v)
		return v * 2 + base
	end
	local first = log(1)
	local log = function(v)
		return log(v) + 100
	end
	acc[1] = base + 1
	acc[2] = base + 2
	acc[3] = base + 3
	acc[4] = base + 4
	acc[5] = base + 5
	acc[6] = base + 6
	acc[7] = base + 7
	acc[8] = base + 8
	acc[9] = base + 9
	acc[10] = base + 10
	acc[11] = base + 11
	acc[12] = base + 12
	acc[13] = base + 13
	acc[14] = base + 14
	acc[15] = base + 15
	acc[16] = base + 16
	acc[17] = base + 17
	acc[18] = base + 18
	acc[19] = base + 19
	acc[20] = base + 20
	acc[21] = base + 21
	acc[22] = base + 22
	acc[23] = base + 23
	acc[24] = base + 24
	acc[25] = base + 25
	acc[26] = base + 26
	acc[27] = base + 27
	acc[28] = base + 28
	acc[29] = base + 29
	acc[30] = base + 30
	acc[31] = base + 31
	acc[32] = base + 32
	acc[33] = base + 33
	acc[34] = base + 34
	acc[35] = base + 35
	acc[36] = base + 36
	acc[37] = base + 37
	acc[38] = base + 38
	acc[39] = base + 39
	acc[40] = base + 40
	local r = log(3)
	log = nil
	return r, first, acc[40]
end
return worker
