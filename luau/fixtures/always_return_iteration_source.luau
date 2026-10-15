return function(initial: any, limit: any)
	local function firstIndex(from: any, to: any): number
		for index = from, to do
			return index
		end
		return 0
	end

	local function isEmpty(values: { any }): boolean
		for _ in pairs(values) do
			return false
		end
		return true
	end

	local function guardedFirst(from: any, to: any): number
		local total = 1
		if to > 2 then
			for index = from, to do
				return index + total
			end
			total += 5
		end
		return total
	end

	local function guardedFirstKey(values: { any }, enabled: boolean): any
		local total = 1
		if enabled then
			for key in pairs(values) do
				return key
			end
			total += 5
		end
		return total
	end

	local function nestedTerminalExit(from: any, to: any): number
		local total = 0
		if from ~= 0 then
			if to > 2 then
				for index = from, to do
					return index
				end
				return 0
			end
			total += 1
		end
		return total
	end

	return firstIndex(initial, limit),
		isEmpty({}),
		isEmpty({ initial }),
		guardedFirst(initial, limit),
		guardedFirstKey({ limit }, limit > 2),
		guardedFirstKey({}, true),
		nestedTerminalExit(initial, limit)
end
