return function(initial: any, limit: any)
	local function breakInWhile(from: any, to: any): number
		local total = 0
		while total < 3 do
			for index = from, to do
				total += 1
				break
			end
			total += 1
		end
		return total
	end

	local function breakLastInWhile(from: any, to: any): number
		local total = 0
		local trips = 0
		while trips < 3 do
			trips += 1
			for index = from, to do
				total += index
				break
			end
		end
		return total + trips
	end

	local function breakInNumericFor(from: any, to: any): number
		local total = 0
		for round = 1, 3 do
			for index = from, to do
				total += round
				break
			end
			total += 1
		end
		return total
	end

	local function breakInRepeat(from: any, to: any): number
		local total = 0
		repeat
			for index = from, to do
				total += 1
				break
			end
			total += 1
		until total >= 3
		return total
	end

	local function firstKeyEachRound(values: { any }): number
		local total = 0
		local rounds = 0
		while rounds < 2 do
			rounds += 1
			for key in pairs(values) do
				total += key
				break
			end
		end
		return total
	end

	local function breakTwoPathsInWhile(from: any, to: any): number
		local total = 0
		while total < 3 do
			for index = from, to do
				if index > 1 then
					total += 1
				end
				break
			end
			total += 1
		end
		return total
	end

	local function breakLastInIf(from: any, to: any): number
		local total = 1
		if to > 2 then
			for index = from, to do
				total += index
				break
			end
		end
		return total
	end

	return breakInWhile(initial, limit),
		breakLastInWhile(initial, limit),
		breakInNumericFor(initial, limit),
		breakInRepeat(initial, limit),
		firstKeyEachRound({ limit }),
		firstKeyEachRound({}),
		breakTwoPathsInWhile(initial, limit),
		breakLastInIf(initial, limit)
end
