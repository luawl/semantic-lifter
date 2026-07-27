return function(left, right)
	local double = function(value)
		return value * 2
	end
	local sum = left + right
	local doubled = double(sum)
	local order = 0
	local first = function()
		order = order * 10 + 1
		return left
	end
	local second = function()
		order = order * 10 + 2
		return right
	end
	local ordered = first() + -second()
	local transitiveSource = 1
	transitiveSource = 2
	local transitiveDerived = transitiveSource + 0.5
	transitiveDerived = transitiveSource + 1.5
	local transitiveResult = transitiveDerived + 1
	local dynamicEffects = ""
	local constantMetamethod = function(effect, result)
		return function()
			dynamicEffects ..= effect
			return result
		end
	end
	local dynamicMetatable = {
		__len = constantMetamethod("l", 7),
		__unm = constantMetamethod("u", { tag = "unary-result" }),
		__add = constantMetamethod("a", 11),
		__sub = constantMetamethod("s", 12),
		__mul = constantMetamethod("m", 13),
		__div = constantMetamethod("d", 14),
		__idiv = constantMetamethod("i", 15),
		__mod = constantMetamethod("r", 16),
		__pow = constantMetamethod("p", 17),
		__concat = constantMetamethod("c", "joined"),
		__eq = constantMetamethod("e", "truthy"),
		__lt = function(firstValue, secondValue)
			dynamicEffects ..= "o" .. firstValue.side .. secondValue.side
			return nil
		end,
		__le = function(firstValue, secondValue)
			dynamicEffects ..= "q" .. firstValue.side .. secondValue.side
			return "truthy"
		end,
	}
	local dynamicLeft = setmetatable({ side = "L" }, dynamicMetatable)
	local dynamicRight = setmetatable({ side = "R" }, dynamicMetatable)
	local dynamicLength = #dynamicLeft
	local dynamicUnary = -dynamicLeft
	local dynamicAdd = dynamicLeft + dynamicRight
	local dynamicSubtract = dynamicLeft - dynamicRight
	local dynamicMultiply = dynamicLeft * dynamicRight
	local dynamicDivide = dynamicLeft / dynamicRight
	local dynamicFloorDivide = dynamicLeft // dynamicRight
	local dynamicModulo = dynamicLeft % dynamicRight
	local dynamicPower = dynamicLeft ^ dynamicRight
	local dynamicConcat = dynamicLeft .. dynamicRight
	local dynamicEqual = dynamicLeft == dynamicRight
	local dynamicNotEqual = dynamicLeft ~= dynamicRight
	local dynamicOrdered = dynamicLeft < dynamicRight
	local dynamicLessEqual = dynamicLeft <= dynamicRight
	local dynamicGreater = dynamicLeft > dynamicRight
	local dynamicGreaterEqual = dynamicLeft >= dynamicRight
	local primitiveOperators = {
		add = 0.5 + 2,
		subtract = 5 - 2,
		multiply = 0.5 * 4,
		divide = 5 / 2,
		floorDivide = 5 // 2,
		modulo = 5 % 2,
		power = 2 ^ 3,
		concat = "value=" .. 2,
		equal = "a" == "b",
		notEqual = "a" ~= "b",
		less = "a" < "b",
		lessEqual = "a" <= "b",
		greater = "b" > "a",
		greaterEqual = "b" >= "b",
		logicalNot = not left,
		negate = -0.5,
		length = #"typed",
		dynamicLength = dynamicLength,
		dynamicUnaryTag = dynamicUnary.tag,
		dynamicAdd = dynamicAdd,
		dynamicSubtract = dynamicSubtract,
		dynamicMultiply = dynamicMultiply,
		dynamicDivide = dynamicDivide,
		dynamicFloorDivide = dynamicFloorDivide,
		dynamicModulo = dynamicModulo,
		dynamicPower = dynamicPower,
		dynamicConcat = dynamicConcat,
		dynamicEqual = dynamicEqual,
		dynamicNotEqual = dynamicNotEqual,
		dynamicOrdered = dynamicOrdered,
		dynamicLessEqual = dynamicLessEqual,
		dynamicGreater = dynamicGreater,
		dynamicGreaterEqual = dynamicGreaterEqual,
		dynamicEffects = dynamicEffects,
	}
	return doubled, ordered, order, primitiveOperators, transitiveResult
end
