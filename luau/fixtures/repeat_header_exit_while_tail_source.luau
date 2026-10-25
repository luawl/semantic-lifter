local function repeatEndsWhileBody(n, a, m)
	local count, step, round = 0, 0, 0
	while round < m do
		round = round + 1
		repeat
			step = step + 1
			if step == n then
				count = count + 100
				break
			end
		until step % 3 == 0
	end
	return count, step
end

local function repeatEndsWhileArm(n, a, m)
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
		end
	end
	return count, step
end

local functions = {
	repeatEndsWhileBody = repeatEndsWhileBody,
	repeatEndsWhileArm = repeatEndsWhileArm,
}

return function()
	return functions
end
