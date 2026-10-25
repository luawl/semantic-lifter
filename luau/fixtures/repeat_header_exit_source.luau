local function assignThenBreak(n)
	local p, i = 0, 0
	repeat
		i = i + 1
		if i == n then
			p = 100
			break
		end
	until i >= 3
	return p, i
end

local function bareBreak(n)
	local p, i = 0, 0
	repeat
		i = i + 1
		if i == n then
			break
		end
	until i >= 3
	return p, i
end

local function breakInArmBeforeStatement(n, a)
	local p, i = 0, 0
	if a then
		repeat
			i = i + 1
			if i == n then
				p = 100
				break
			end
		until i >= 3
		p = p + 1
	end
	return p, i
end

local function returnFromHeader(n)
	local p, i = 0, 0
	repeat
		i = i + 1
		if i == n then
			return -1, i
		end
	until i >= 3
	return p, i
end

local function breakInArmTail(n, a)
	local p, i = 0, 0
	if a then
		repeat
			i = i + 1
			if i == n then
				p = 100
				break
			end
		until i >= 3
	end
	return p, i
end

local function breakInWhileArmBeforeReturn(n, a, m)
	local count, step, round = 0, 0, 0
	while round < m do
		round = round + 1
		if a then
			repeat
				step = step + 1
				if step == n then
					count = count + 100
					break
				end
			until step % 3 == 0
			return count, step
		end
	end
	return -count, step
end

local functions = {
	assignThenBreak = assignThenBreak,
	bareBreak = bareBreak,
	breakInArmBeforeStatement = breakInArmBeforeStatement,
	returnFromHeader = returnFromHeader,
	breakInArmTail = breakInArmTail,
	breakInWhileArmBeforeReturn = breakInWhileArmBeforeReturn,
}

return function()
	return functions
end
