-- Luau numbers are doubles. The chain starts from integer literals within 2^53 and rounds at every step:
-- (2^53 - 1) + 4 is 9007199254740995, which rounds to 9007199254740996; times 3 is 27021597764222988, exact;
-- subtracting 9007199254740991 rounds to 18014398509481996 and then to 9007199254741004; and subtracting 12
-- gives 9007199254740992, which is 2^53. Exact integer arithmetic on the same literals ends at 9007199254740991
-- instead, so the equality with 9007199254740991 is false.
local function chainEqual()
	local almost = 9007199254740991
	local a = almost + 4
	local b = a * 3
	local c = b - 9007199254740991
	local d = c - 9007199254740991
	local e = d - 12
	if e == 9007199254740991 then
		return "then-arm"
	else
		return "else-arm"
	end
end

return function()
	return chainEqual()
end
