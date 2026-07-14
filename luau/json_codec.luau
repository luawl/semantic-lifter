--!strict

local ARRAY_METATABLE = {}

local function newArray<T>(): { T }
	return setmetatable({}, ARRAY_METATABLE) :: any
end

local JSON_ESCAPES = {
	['"'] = '\\"',
	["\\"] = "\\\\",
	["\b"] = "\\b",
	["\f"] = "\\f",
	["\n"] = "\\n",
	["\r"] = "\\r",
	["\t"] = "\\t",
}

local function encodeString(value: string): string
	assert(utf8.len(value) ~= nil, "JSON string is not valid UTF-8")
	local escaped = string.gsub(value, '[%z\1-\31\\"]', function(character: string): string
		return JSON_ESCAPES[character] or string.format("\\u%04x", string.byte(character))
	end)
	return '"' .. escaped .. '"'
end

local function indentation(depth: number): string
	return string.rep("  ", depth)
end

local function encodeValue(value: any, pretty: boolean, depth: number): string
	local valueType = typeof(value)
	if valueType == "string" then
		return encodeString(value)
	elseif valueType == "boolean" then
		return if value then "true" else "false"
	elseif valueType == "number" then
		assert(value == value and math.abs(value) ~= math.huge, "JSON does not support non-finite numbers")
		return tostring(value)
	elseif valueType ~= "table" then
		error(`unsupported JSON value type {valueType}`)
	end

	if getmetatable(value) == ARRAY_METATABLE then
		local encodedItems = {}
		for index = 1, #value do
			table.insert(encodedItems, encodeValue(value[index], pretty, depth + 1))
		end
		if #encodedItems == 0 then
			return "[]"
		elseif not pretty then
			return "[" .. table.concat(encodedItems, ",") .. "]"
		end
		local childIndent = indentation(depth + 1)
		return "[\n"
			.. childIndent
			.. table.concat(encodedItems, ",\n" .. childIndent)
			.. "\n"
			.. indentation(depth)
			.. "]"
	end

	local keys = {}
	for key in value do
		assert(type(key) == "string", "JSON object keys must be strings")
		table.insert(keys, key)
	end
	table.sort(keys)
	if #keys == 0 then
		return "{}"
	end

	local encodedFields = {}
	for _, key in keys do
		local separator = if pretty then ": " else ":"
		table.insert(encodedFields, encodeString(key) .. separator .. encodeValue(value[key], pretty, depth + 1))
	end
	if not pretty then
		return "{" .. table.concat(encodedFields, ",") .. "}"
	end
	local childIndent = indentation(depth + 1)
	return "{\n"
		.. childIndent
		.. table.concat(encodedFields, ",\n" .. childIndent)
		.. "\n"
		.. indentation(depth)
		.. "}"
end

local function encode(value: any, pretty: boolean?): string
	return encodeValue(value, pretty == true, 0)
end

return table.freeze({
	newArray = newArray,
	encode = encode,
})
