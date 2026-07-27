return function(mode: string)
	local total = 0
	local first: (() -> (any, any))? = nil
	local last: (() -> (any, any))? = nil

	local function record(index: any, value: any, capture: () -> (any, any))
		if first == nil then
			first = capture
		end
		last = capture
		total += index * 10 + value
	end

	if mode == "table" then
		for index, value in { 2, 3, 4 } do
			local capture = function()
				return index, value
			end
			record(index, value, capture)
		end
	elseif mode == "iter" then
		local subject = { values = { 2, 3, 4 } }
		setmetatable(subject, {
			__iter = function(self)
				local function advance(state, control)
					local index = (control or 0) + 1
					local value = state.values[index]
					if value == nil then
						return nil
					end
					return index, value
				end
				return advance, self, nil
			end,
		})
		for index, value in subject do
			local capture = function()
				return index, value
			end
			record(index, value, capture)
		end
	elseif mode == "callable" then
		local subject = { limit = 3 }
		setmetatable(subject, {
			__call = function(self, _state, control)
				local index = control + 1
				if index > self.limit then
					return nil
				end
				return index, index * 2
			end,
		})
		for index, value in subject, nil, 0 do
			local capture = function()
				return index, value
			end
			record(index, value, capture)
		end
	elseif mode == "segmented" then
		local marker = 0
		if marker == 0 then marker += 1 end
		if marker == 1 then marker += 1 end
		if marker == 2 then marker += 1 end
		if marker == 3 then marker += 1 end
		while marker < 0 do
			marker += 1
		end
		local function startArgument(): number
			return 1
		end
		local function startValue(value: number): number
			return value
		end
		local function limitValue(): number
			return 3
		end
		local function stepValue(): number
			return 1
		end
		for value = startValue(startArgument()), limitValue(), stepValue() do
			total += value
		end
		for index, value in ipairs({ 2, 3, 4 }) do
			local capture = function()
				return index, value
			end
			record(index, value, capture)
		end
		total += marker * 100
	elseif mode == "scalar" then
		local values = { 7, 8 }
		local function advance(_state, control)
			local index = (control or 0) + 1
			local value = values[index]
			if value == nil then
				return nil
			end
			return index, value
		end
		local function makeIterator()
			return advance, "leaked-state", 99
		end
		for index, value in (makeIterator()), nil, nil do
			local capture = function()
				return index, value
			end
			record(index, value, capture)
		end
	elseif mode == "factory" then
		local state = { 7, 8 }
		local factoryCalls = 0
		local function advance(values, control)
			local index = control + 1
			local value = values[index]
			if value == nil then
				return nil
			end
			return index, value
		end
		local function makeIterator()
			factoryCalls += 1
			return advance, state, 0
		end
		for index, value in makeIterator() do
			local capture = function()
				return index, value
			end
			record(index, value, capture)
		end
		total += factoryCalls * 1000
	elseif mode == "single" then
		local subject = { values = { 2, 3, 4 } }
		local prepareCalls = 0
		setmetatable(subject, {
			__iter = function(self)
				prepareCalls += 1
				local function advance(state, control)
					local index = (control or 0) + 1
					local value = state.values[index]
					if value == nil then
						return nil
					end
					return index, value
				end
				return advance, self, nil
			end,
		})
		for index, value in subject do
			local capture = function()
				return index, value
			end
			record(index, value, capture)
			break
		end
		total += prepareCalls * 1000
	else
		local state = { 5, 6 }
		local function advance(values, control)
			local index = control + 1
			local value = values[index]
			if value == nil then
				return nil
			end
			return index, value
		end
		for index, value in advance, state, 0 do
			local capture = function()
				return index, value
			end
			record(index, value, capture)
		end
	end

	return total, first, last
end
