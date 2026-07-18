return function(...)
	local pair = function()
		return 4, 5
	end
	local left, right = pair()
	local first, second = ...
	left, right = right, left
	local order = ""
	local target = { slot = 0 }
	local function tableAddress()
		order = order .. "t"
		return target
	end
	local function keyAddress()
		order = order .. "k"
		return "slot"
	end
	local function rightValue()
		order = order .. "r"
		target.slot = 100
		return 7
	end
	tableAddress()[keyAddress()] = rightValue()
	local index = 1
	local slots = { 10, 20 }
	index, slots[index] = 2, 30
	return left, right, first, second, target.slot, order, index, slots[1], slots[2]
end
