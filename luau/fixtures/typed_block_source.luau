type NumberBox = { value: number }
type MixedArgumentCallback = (any, label: string?) -> boolean

return function(input: any): number
	local result: number
	do
		local box: NumberBox = { value = input :: number }
		result = box.value
	end
	if true then
		return result
	else
		return result
	end
	local unreachable = input
end
