local function identity<T>(value: T): T
	return value
end

local namespace = { base = 4 }
local root = { child = namespace }

local function mutable_offset(value: number): number
	return value + 1
end

local original_offset = mutable_offset
mutable_offset = nil
mutable_offset = function(value: number): number
	return value + 2
end

function namespace.double(value: number): number
	return identity(value * 2)
end

function namespace:add(value: number): number
	return self.base + value
end

function root.child.triple(value: number): number
	return value * 3
end

return function(value: number)
	return namespace.double(value), namespace:add(value), root.child.triple(value), original_offset(value), mutable_offset(value)
end
