-- A `repeat` worker that counts its passes and skips to its `until` test with a `continue` two `if`s deep in its
-- first arm, with an `if` after that arm and an `or` in the `until` test.
local function worker(selector, budget)
	local total = 0
	local passes = 0
	repeat
		passes += 1
		if selector == 4 then
			total = total + 2
			if budget > 7 then
				continue
			end
			total = total + 1
		end
		total = total + 1
		if selector ~= 0 then
			total = total + 1
		end
	until total >= 6 or budget > 5
	total = total + 100
	return total, passes
end
return worker
