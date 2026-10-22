-- Luau numbers are doubles. Both chains start from integer literals within 2^53 and round at every step:
-- (2^53 - 1) + 3 is 9007199254740994, exact; times 3 is 27021597764222982, which rounds to 27021597764222984;
-- subtracting 9007199254740989 rounds to 18014398509481996 and then to 9007199254741008; and subtracting 13
-- gives 9007199254740995, which rounds to 9007199254740996. Exact integer arithmetic on the same literals ends at
-- 9007199254740991 instead, so the equality with 9007199254740991 is false and the inequality is true.
local function chainEqual()
	local almost = 9007199254740991
	local a = almost + 3
	local b = a * 3
	local c = b - 9007199254740989
	local d = c - 9007199254740989
	local e = d - 13
	if e == 9007199254740991 then
		return "then-arm"
	else
		return "else-arm"
	end
end

local function chainNotEqual()
	local almost = 9007199254740991
	local a = almost + 3
	local b = a * 3
	local c = b - 9007199254740989
	local d = c - 9007199254740989
	local e = d - 13
	if e ~= 9007199254740991 then
		return "then-arm"
	else
		return "else-arm"
	end
end

return function()
	return chainEqual(), chainNotEqual()
end
