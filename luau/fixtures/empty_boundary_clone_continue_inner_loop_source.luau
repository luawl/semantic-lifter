-- A `repeat` worker over a queue that adds the item equal to the selector to a skip total and skips to its `until`
-- test with a `continue` two `if`s deep; the test reads the queue length.
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
				skipped += item
				continue
			end
			sum += item
		end
		sum += 0
	until index >= #queue or sum > budget
	return sum, skipped, index
end
return worker
