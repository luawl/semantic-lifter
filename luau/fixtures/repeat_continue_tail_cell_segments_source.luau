-- A repeat whose odd passes may continue one if deeper; the tail declares a local captured by a stored closure,
-- runs 29 plain statements and bumps the local.
local function worker(a, b)
	local probes = {}
	local i = 0
	local n = 0
	repeat
		i += 1
		if i % 2 == 1 then
			if i == a then
				continue
			end
		end
		local cell = i
		probes[#probes + 1] = function()
			return cell
		end
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		n += 1
		cell += 1
	until i >= 4
	local seen = 0
	for _, probe in probes do
		seen = seen * 7 + probe()
	end
	return n, seen
end
return worker
