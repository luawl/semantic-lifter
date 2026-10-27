-- A `repeat` worker that skips queue items equal to a selector with `continue` two `if`s deep and whose `until` test
-- is an `or`; nothing after the tests reads the item.
local function worker(selector, budget)
	local queue = { 3, 1, 4, 1, 5, 9, 2, 6 }
	local index = 0
	local sum = 0
	local skipped = 0
	repeat
		index += 1
		local item = queue[index]
		if item ~= nil then
			if item == selector then
				skipped += 1
				continue
			end
			sum += 1
		end
		sum += 0
	until index >= 8 or sum > budget
	return sum, skipped, index
end
return worker
