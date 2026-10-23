-- The returned function starts count at 0i, an i-suffixed integer literal of Luau's integer type rather than a
-- number, and sets it to 7 when flag is true. The source frontend lifts Luau numbers only and refuses this source.
return function(flag)
	local count = 0i
	if flag then
		count = 7
	end
	return count
end
