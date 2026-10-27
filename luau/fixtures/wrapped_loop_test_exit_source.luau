-- A `while true` worker that leaves at its first test, skips to its next pass with a `continue` that follows a
-- statement two `if`s deep, and leaves again at its last test, an `if` whose only statement is `break`.
local function worker(selector, budget)
	local total = 0
	local rounds = 0
	while true do
		if total >= 6 then
			break
		end
		rounds += 1
		if selector == 4 then
			total += 2
			if budget > 7 then
				total += 1
				continue
			end
			total += 1
		end
		total += 1
		if budget > 5 then
			break
		end
	end
	return total, rounds
end
return worker
