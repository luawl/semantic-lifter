-- A `repeat` worker with a `continue` under an `if` in an `if` arm and another under an `if` in an `elseif` arm, and
-- a three-way `or` in its `until` test.
local function worker(selector, budget)
	local total = 0
	local rounds = 0
	repeat
		rounds += 1
		if selector == 4 then
			total = total + 2
			if budget > 7 then
				continue
			end
			total = total + 1
		elseif selector == 3 then
			if budget > 1 then
				continue
			end
			total = total + 4
		end
		total = total + 1
	until rounds >= 5 or total >= 6 or budget > 5
	return total, rounds
end
return worker
