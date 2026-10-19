-- A local read by an outer condition and by an inner condition that resolution proves from the
-- outer arm (internal_facts, proved_branch): the inner condition's block is threaded past and
-- left unreachable, and its exact-pure read of the local must not release the local's
-- declaration (EMIT-UNDECLARED-LOCAL-AFTER-PROVED-BRANCH).
return function(limit)
	local a = "a"
	local k = "k"
	local numbers = {}
	for i = 1, limit do
		local big = i > 5
		if big == ("a" < "b") then
			if big == (a < "b") then
				numbers[#numbers + 1] = i
			else
				numbers[#numbers + 1] = -i
			end
		end
	end
	local strings = {}
	for i = 1, limit do
		local s = "k" .. i
		if s < "k" .. "5" then
			if s < k .. "5" then
				strings[#strings + 1] = i
			else
				strings[#strings + 1] = -i
			end
		end
	end
	return table.concat(numbers, ","), table.concat(strings, ",")
end
