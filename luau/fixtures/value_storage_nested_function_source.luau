-- A worker and the function it makes both hold more than 120 candidate values (plain statements), so the standard
-- target gives each a storage table. The worker computes a number and makes a table right before making the
-- function; the function appends to the table and reads the number.
local function worker(selector, budget)
	local acc = {}
	local limit = 4
	if type(budget) == "number" and budget >= 1 then
		limit = 2 + budget % 5
	end
	local base = 1
	if type(selector) == "number" then
		base = selector
	end
	acc[1] = limit + 1
	acc[2] = limit + 2
	acc[3] = limit + 3
	acc[4] = limit + 4
	acc[5] = limit + 5
	acc[6] = limit + 6
	acc[7] = limit + 7
	acc[8] = limit + 8
	acc[9] = limit + 9
	acc[10] = limit + 10
	acc[11] = limit + 11
	acc[12] = limit + 12
	acc[13] = limit + 13
	acc[14] = limit + 14
	acc[15] = limit + 15
	acc[16] = limit + 16
	acc[17] = limit + 17
	acc[18] = limit + 18
	acc[19] = limit + 19
	acc[20] = limit + 20
	acc[21] = limit + 21
	acc[22] = limit + 22
	acc[23] = limit + 23
	acc[24] = limit + 24
	acc[25] = limit + 25
	acc[26] = limit + 26
	acc[27] = limit + 27
	acc[28] = limit + 28
	acc[29] = limit + 29
	acc[30] = limit + 30
	acc[31] = limit + 31
	acc[32] = limit + 32
	acc[33] = limit + 33
	acc[34] = limit + 34
	acc[35] = limit + 35
	acc[36] = limit + 36
	acc[37] = limit + 37
	acc[38] = limit + 38
	acc[39] = limit + 39
	acc[40] = limit + 40
	local scale = base * 3 + limit
	local log = {}
	local inner = function(n)
		local own = {}
		own[1] = n + 1
		own[2] = n + 2
		own[3] = n + 3
		own[4] = n + 4
		own[5] = n + 5
		own[6] = n + 6
		own[7] = n + 7
		own[8] = n + 8
		own[9] = n + 9
		own[10] = n + 10
		own[11] = n + 11
		own[12] = n + 12
		own[13] = n + 13
		own[14] = n + 14
		own[15] = n + 15
		own[16] = n + 16
		own[17] = n + 17
		own[18] = n + 18
		own[19] = n + 19
		own[20] = n + 20
		own[21] = n + 21
		own[22] = n + 22
		own[23] = n + 23
		own[24] = n + 24
		own[25] = n + 25
		own[26] = n + 26
		own[27] = n + 27
		own[28] = n + 28
		own[29] = n + 29
		own[30] = n + 30
		own[31] = n + 31
		own[32] = n + 32
		own[33] = n + 33
		own[34] = n + 34
		own[35] = n + 35
		own[36] = n + 36
		own[37] = n + 37
		own[38] = n + 38
		own[39] = n + 39
		own[40] = n + 40
		own[41] = n + 41
		own[42] = n + 42
		own[43] = n + 43
		own[44] = n + 44
		own[45] = n + 45
		own[46] = n + 46
		own[47] = n + 47
		own[48] = n + 48
		own[49] = n + 49
		own[50] = n + 50
		own[51] = n + 51
		own[52] = n + 52
		own[53] = n + 53
		own[54] = n + 54
		own[55] = n + 55
		own[56] = n + 56
		own[57] = n + 57
		own[58] = n + 58
		own[59] = n + 59
		own[60] = n + 60
		own[61] = n + 61
		own[62] = n + 62
		own[63] = n + 63
		own[64] = n + 64
		own[65] = n + 65
		own[66] = n + 66
		own[67] = n + 67
		own[68] = n + 68
		own[69] = n + 69
		own[70] = n + 70
		log[#log + 1] = scale + own[1]
		return scale * 2 + n + own[70]
	end
	local first = inner(limit)
	local second = inner(base)
	return first, second, #log, log[1], acc[40]
end
return worker
