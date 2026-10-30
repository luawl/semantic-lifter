-- A worker whose numeric for pass declares a local, stores a closure that returns it and reads the local again in the
-- same pass; the closures run after the loop. The plain statements after the loop give the worker more than 120
-- candidate values, so the standard target keeps its values in a storage table: each closure must still return the
-- local of its own pass.
local function worker(selector, budget)
	local passes = 3
	if type(budget) == "number" and budget >= 1 then
		passes = 2 + budget % 4
	end
	local scale = 10
	if type(selector) == "number" then
		scale = selector
	end
	local fns = {}
	local total = 0
	for i = 1, passes do
		local li = i * scale
		fns[i] = function()
			return li
		end
		total += li
	end
	local acc = {}
	acc[1] = passes + 1
	acc[2] = passes + 2
	acc[3] = passes + 3
	acc[4] = passes + 4
	acc[5] = passes + 5
	acc[6] = passes + 6
	acc[7] = passes + 7
	acc[8] = passes + 8
	acc[9] = passes + 9
	acc[10] = passes + 10
	acc[11] = passes + 11
	acc[12] = passes + 12
	acc[13] = passes + 13
	acc[14] = passes + 14
	acc[15] = passes + 15
	acc[16] = passes + 16
	acc[17] = passes + 17
	acc[18] = passes + 18
	acc[19] = passes + 19
	acc[20] = passes + 20
	acc[21] = passes + 21
	acc[22] = passes + 22
	acc[23] = passes + 23
	acc[24] = passes + 24
	acc[25] = passes + 25
	acc[26] = passes + 26
	acc[27] = passes + 27
	acc[28] = passes + 28
	acc[29] = passes + 29
	acc[30] = passes + 30
	acc[31] = passes + 31
	acc[32] = passes + 32
	acc[33] = passes + 33
	acc[34] = passes + 34
	acc[35] = passes + 35
	acc[36] = passes + 36
	acc[37] = passes + 37
	acc[38] = passes + 38
	acc[39] = passes + 39
	acc[40] = passes + 40
	local sum = 0
	local weighted = 0
	for i = 1, passes do
		sum += fns[i]()
		weighted = weighted * 3 + fns[i]()
	end
	return sum, weighted, total, acc[40]
end
return worker
