-- Author-written worker: a repeat loop of two passes whose odd pass may continue one if deeper; its tail declares a local that a stored closure captures, runs 34 plain statements and bumps the local.
local function worker(a, b)
	local probes = {}
	local total = 0
	local n = 0
	local queue = { 3, 1, 4, 1, 5, 9, 2, 6, 5, 3 }
	local i = 0
	repeat
		i += 1
		local item = queue[i]
		if i % 2 == 1 then
			if i == a then
				continue
			end
		end
		local cell = total * 10 + i
		probes[#probes + 1] = function()
			return cell
		end
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		n = n + 0
		n = n + 1
		cell += 1
	until i >= 2
	local seen = 0
	for _, probe in probes do
		seen = seen * 7 + probe()
	end
	return total, n, seen
end
return worker
