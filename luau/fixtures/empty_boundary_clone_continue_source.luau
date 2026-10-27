-- A `repeat` worker over a queue that skips the item equal to the selector with a `continue` two `if`s deep; its
-- `until` test is an `or`, and only `sum += 0` follows the outer `if`.
local function worker(selector, budget)
	local queue = { 3, 1, 4, 1, 5, 9, 2, 6 }
	local index = 0
	local sum = 0
	repeat
		index += 1
		local item = queue[index]
		if item ~= nil then
			if item == selector then
				continue
			end
			sum += item
		end
		sum += 0
	until index >= 8 or sum > budget
	return sum, index
end
return worker
