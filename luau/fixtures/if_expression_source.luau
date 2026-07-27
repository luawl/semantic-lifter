return function(flag)
	local calls = 0
	local choose = function(value)
		calls += 1
		return value
	end
	local result = if flag then choose("yes") else choose("no")
	local nested = if (if flag then choose(true) else choose(false)) then choose("nested-yes") else choose("nested-no")
	local order = ""
	local condition = function()
		order ..= "c"
		return flag
	end
	local arm = function(value)
		order ..= value
		return value
	end
	local consume = function(value)
		order ..= "u"
		return value
	end
	local immediate = consume(if condition() then arm("t") else arm("f"))
	local typed = if flag then "typed-yes" else "typed-no"
	local transitiveSource = 1
	transitiveSource = 2
	local transitive = (if flag then transitiveSource + 0.5 else transitiveSource + 1.5) + 1
	return result, calls, nested, immediate, order, flag or "return-fallback", typed, transitive
end
