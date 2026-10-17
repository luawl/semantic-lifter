return function(initial: any, limit: any)
	local function nestedBreakThenCode(from: any, to: any): number
		local total = 0
		local trips = 0
		while trips < 3 do
			trips += 1
			for index = from, to do
				if index > 1 then
					if index > 2 then
						break
					end
					total += 1
				end
				total += 10
				break
			end
			total += 100
		end
		return total + trips
	end

	local function deepNestedBreakThenCode(from: any, to: any): number
		local total = 0
		local trips = 0
		while trips < 3 do
			trips += 1
			for index = from, to do
				if index > 1 then
					if index > 2 then
						if index > 3 then
							break
						end
						total += 100
					end
					total += 1
				end
				total += 10
				break
			end
			total += 1000
		end
		return total + trips
	end

	local function nestedBreakInRepeat(from: any, to: any): number
		local total = 0
		local trips = 0
		repeat
			trips += 1
			for index = from, to do
				if index > 1 then
					if index > 2 then
						break
					end
					total += 1
				end
				total += 10
				break
			end
		until trips >= 3
		return total + trips
	end

	local function nestedBreakEachRoundThenCode(values: { any }, stop: any): number
		local total = 0
		local rounds = 0
		while rounds < 2 do
			rounds += 1
			for key, value in pairs(values) do
				if key > 0 then
					if value == stop then
						break
					end
					total += 1
				end
				total += 10
				break
			end
			total += 100
		end
		return total + rounds
	end

	local function nestedBreakLastInIfThenCode(from: any, to: any): number
		local total = 0
		local trips = 0
		while trips < 3 do
			trips += 1
			if trips > 1 then
				for index = from, to do
					if index > 1 then
						if index > 2 then
							break
						end
						total += 1
					end
					total += 10
					break
				end
			end
			total += 100
		end
		return total + trips
	end

	local function returnOrBreakInWhile(from: any, to: any): number
		local total = 0
		local trips = 0
		while trips < 3 do
			trips += 1
			for index = from, to do
				if index > 5 then
					return -1
				end
				total += index
				break
			end
		end
		return total + trips
	end

	local function nestedReturnInWhile(from: any, to: any): number
		local total = 0
		local trips = 0
		while trips < 3 do
			trips += 1
			for index = from, to do
				if index > 1 then
					if index > 5 then
						return -1
					end
					total += 1
				end
				total += index
				break
			end
		end
		return total + trips
	end

	local function returnAfterCodeInWhile(from: any, to: any): number
		local total = 0
		local trips = 0
		while trips < 3 do
			trips += 1
			for index = from, to do
				total += index
				if index > 5 then
					return -1
				end
				break
			end
		end
		return total + trips
	end

	return nestedBreakThenCode(initial, limit),
		deepNestedBreakThenCode(initial, limit),
		nestedBreakInRepeat(initial, limit),
		nestedBreakEachRoundThenCode({ initial, limit }, limit),
		nestedBreakEachRoundThenCode({}, limit),
		nestedBreakLastInIfThenCode(initial, limit),
		returnOrBreakInWhile(initial, limit),
		nestedReturnInWhile(initial, limit),
		returnAfterCodeInWhile(initial, limit)
end
