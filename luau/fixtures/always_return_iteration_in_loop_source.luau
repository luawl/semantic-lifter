return function(initial: any, limit: any)
	local function whileFirst(from: any, to: any): number
		local total = 0
		while total < 3 do
			for index = from, to do
				return index + total
			end
			total += 1
		end
		return total
	end

	local function roundFirst(from: any, to: any): number
		local total = 0
		for round = 1, 3 do
			for index = from, to do
				return index + round
			end
			total += round
		end
		return total
	end

	local function whileSigned(from: any, to: any): number
		local total = 0
		while total < 3 do
			for index = from, to do
				if index > 1 then
					return index + total
				end
				return -index
			end
			total += 1
		end
		return total
	end

	local function whileFirstKey(values: { any }): any
		local total = 0
		while total < 3 do
			for key in pairs(values) do
				return key
			end
			total += 1
		end
		return total
	end

	local function repeatFirst(from: any, to: any): number
		local total = 0
		repeat
			for index = from, to do
				return index + total
			end
			total += 1
		until total >= 3
		return total
	end

	local function guardedInWhile(from: any, to: any): number
		local total = 0
		while total < 5 do
			total += 1
			for index = from, to do
				return index + total
			end
			if total > to then
				break
			end
		end
		return total
	end

	return whileFirst(initial, limit),
		roundFirst(initial, limit),
		whileSigned(initial, limit),
		whileFirstKey({ limit }),
		whileFirstKey({}),
		repeatFirst(initial, limit),
		guardedInWhile(initial, limit)
end
