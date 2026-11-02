-- Author-written worker: a repeat loop whose odd passes take an if holding a continue one if deeper; the loop
-- body ends in one straight-line tail, which the structured layout writes in both arms.
local function three(x)
	return x, x + 1, x + 2
end
local function sum(...)
	local s = 0
	for _, v in { ... } do
		s += v
	end
	return s, select("#", ...)
end
local function worker(selector, budget)
	local total = 0
	local index = 0
	local probes = {}
	local acc = {}
	for z = 100, 120 do acc[z] = 0 end
	repeat
		index += 1
		if index % 2 == 1 then
			total = total + 2
			if index == selector then
				continue
			end
			total = total + 1
		end
		local a, b, c = three(index)
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
		acc[108] = acc[108] + a * 100 + b * 10 + c
		acc[109] = sum(three(total))
	until index >= 8
	local seen = 0
	for _, probe in probes do
		seen = seen * 7 + probe()
	end
	return total, index, seen, acc[108], acc[109]
end
return worker
