local function worker(selector, budget)
	local s = tonumber(selector) or 0
	local b = tonumber(budget) or 0
	local log = ""
	local last = 0
	local total = 0
	repeat
		total = total + 1
		local cell = total * 3 + 1
		if total == 2 + math.min(b, 40) or s == total then
			last = last + cell
			local k = 0
			repeat
				k += 1
				if k == s then
					return -k, last, log
				end
				if k == b then
					log = log .. "kb"
					break
				end
			until k >= 3
			break
		end
	until total > 50
	return last, total, log
end
return worker
