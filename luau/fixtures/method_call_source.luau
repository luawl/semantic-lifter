return function(value)
	local calls = 0
	local order = ""
	local add = function(self, delta)
		return self.base + delta
	end
	local object = setmetatable({ base = 5 }, {
		__index = function(_, key)
			order = order .. "resolve"
			if key == "add" then
				return add
			end
			return nil
		end,
	})
	local get = function()
		calls = calls + 1
		return object
	end
	local argument = function()
		order = order .. ":argument"
		return value
	end
	local result = get():add(argument())
	local missingOrder = ""
	local missingReceiver = setmetatable({}, {
		__index = function()
			missingOrder ..= "resolve"
			return nil
		end,
	})
	local missingArgument = function()
		missingOrder ..= ":argument"
		return value
	end
	local missingOk, missingError = pcall(function()
		return missingReceiver:missing(missingArgument())
	end)
	local callableOrder = ""
	local callable = setmetatable({ base = 20 }, {
		__call = function(self, first, second)
			callableOrder ..= "i"
			return self.base + first, second, nil, self.base
		end,
	})
	local getCallable = function()
		callableOrder ..= "c"
		return callable
	end
	local firstCallableArgument = function()
		callableOrder ..= "1"
		return value
	end
	local secondCallableArgument = function()
		callableOrder ..= "2"
		return value + 1
	end
	local fixedFirst, fixedSecond, fixedThird, fixedFourth = getCallable()(firstCallableArgument(), secondCallableArgument())
	local packed = { getCallable()(firstCallableArgument(), secondCallableArgument()) }
	return result, calls, order, missingOk, missingError, missingOrder, fixedFirst, fixedSecond, fixedThird, fixedFourth, packed, callableOrder
end
