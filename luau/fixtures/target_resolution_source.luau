local recoveredPcall = pcall

return function(value)
	local function double(input)
		return input * 2
	end
	local localStatus, localValue = recoveredPcall(double, value)
	local groupedStatus, groupedValue = (recoveredPcall)(double, value + 1)
	local globalStatus, globalValue = pcall(double, value + 2)
	return localStatus, localValue, groupedStatus, groupedValue, globalStatus, globalValue
end
