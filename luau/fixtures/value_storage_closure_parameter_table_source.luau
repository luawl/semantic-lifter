local function fill(t, n)
	local u = t
	local t = n * 3 + 1
	local w = t + 2
	u.get = function()
		return t * 10 + w
	end
	local acc = {}
	acc[1] = n + 1
	acc[2] = n + 2
	acc[3] = n + 3
	acc[4] = n + 4
	acc[5] = n + 5
	acc[6] = n + 6
	acc[7] = n + 7
	acc[8] = n + 8
	acc[9] = n + 9
	acc[10] = n + 10
	acc[11] = n + 11
	acc[12] = n + 12
	acc[13] = n + 13
	acc[14] = n + 14
	acc[15] = n + 15
	acc[16] = n + 16
	acc[17] = n + 17
	acc[18] = n + 18
	acc[19] = n + 19
	acc[20] = n + 20
	acc[21] = n + 21
	acc[22] = n + 22
	acc[23] = n + 23
	acc[24] = n + 24
	acc[25] = n + 25
	acc[26] = n + 26
	acc[27] = n + 27
	acc[28] = n + 28
	acc[29] = n + 29
	acc[30] = n + 30
	acc[31] = n + 31
	acc[32] = n + 32
	acc[33] = n + 33
	acc[34] = n + 34
	acc[35] = n + 35
	acc[36] = n + 36
	acc[37] = n + 37
	acc[38] = n + 38
	acc[39] = n + 39
	acc[40] = n + 40
	return u.get(), w, acc[40]
end
local function worker(selector, budget)
	local n = 2
	if type(selector) == "number" then
		n = selector
	end
	return fill({}, n)
end
return worker
