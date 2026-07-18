return function(left, right)
	if not "present" then
		return "unreachable-dynamic-not"
	end
	if "present" == false then
		return "unreachable-dynamic-equal"
	end
	if "present" ~= "present" then
		return "unreachable-dynamic-not-equal"
	end
	local selected
	if left > right then
		selected = left
	else
		selected = right
	end
	return selected * 2
end
