--!strict

-- A JSON document decoded with every number read from its own text. Lune's serde.decode("json") can read a number
-- text one or two units in the last place away, so each number token outside a string crosses the decoder as the
-- JSON string "\u0001<text>" and is read back with tonumber, which rounds correctly and must name a finite double.
-- Every text the transport marks is read back and nothing else is: a decoded value that is still a JSON number, or a
-- string that begins with the mark but was not marked, refuses the document.

local JsonExact = {}

local MARK = "\1"

local function markNumbers(bytes: string): (string, number)
	local parts: { string } = {}
	local count = 0
	local position = 1
	while true do
		local start = string.find(bytes, '["%-%d]', position)
		if start == nil then
			break
		end
		if string.byte(bytes, start) == 34 then
			-- a string, copied as it is up to its closing quote; a backslash escapes the byte after it
			local cursor = start + 1
			while true do
				local stop = string.find(bytes, '[\\"]', cursor)
				if stop == nil then
					cursor = #bytes + 1
					break
				end
				if string.byte(bytes, stop) == 92 then
					cursor = stop + 2
				else
					cursor = stop + 1
					break
				end
			end
			table.insert(parts, string.sub(bytes, position, cursor - 1))
			position = cursor
		else
			local _, stop = string.find(bytes, "^%-?%d+", start)
			if stop == nil or string.find(bytes, "^%-?0%d", start) ~= nil then
				-- a lone minus sign or a leading zero: left to the decoder, which refuses it
				table.insert(parts, string.sub(bytes, position, start))
				position = start + 1
				continue
			end
			local _, fraction = string.find(bytes, "^%.%d+", stop + 1)
			if fraction ~= nil then
				stop = fraction
			end
			local _, exponent = string.find(bytes, "^[eE][%+%-]?%d+", stop + 1)
			if exponent ~= nil then
				stop = exponent
			end
			table.insert(parts, string.sub(bytes, position, start - 1))
			table.insert(parts, '"\\u0001' .. string.sub(bytes, start, stop) .. '"')
			count += 1
			position = stop + 1
		end
	end
	table.insert(parts, string.sub(bytes, position))
	return table.concat(parts), count
end

local function readNumber(value: string, label: string): number
	local text = string.sub(value, 2)
	local exact = if string.match(text, "^%-?%d+%.?%d*[eE]?[%+%-]?%d*$") ~= nil then tonumber(text) else nil
	assert(exact ~= nil, `{label} holds a marked string that is not a JSON number`)
	assert(
		exact == exact and exact ~= math.huge and exact ~= -math.huge,
		`{label} holds a number text that names no finite double`
	)
	return exact
end

function JsonExact.decode(bytes: string, label: string, decode: (string) -> any): any
	local marked, markedCount = markNumbers(bytes)
	local decoded = decode(marked)
	local readCount = 0
	if type(decoded) == "string" and string.sub(decoded, 1, 1) == MARK then
		decoded = readNumber(decoded, label)
		readCount += 1
	elseif type(decoded) == "number" then
		error(`{label} holds a JSON number that did not use exact text transport`, 0)
	elseif type(decoded) == "table" then
		local stack: { any } = { decoded }
		local visited: { [any]: boolean } = {}
		while #stack > 0 do
			local record: any = table.remove(stack)
			if visited[record] then
				continue
			end
			visited[record] = true
			for key, child in record do
				if type(child) == "string" and string.sub(child, 1, 1) == MARK then
					record[key] = readNumber(child, label)
					readCount += 1
				elseif type(child) == "number" then
					error(`{label} holds a JSON number that did not use exact text transport`, 0)
				elseif type(child) == "table" then
					table.insert(stack, child)
				end
			end
		end
	end
	assert(readCount == markedCount, `{label} holds a string that the exact number transport did not mark`)
	return decoded
end

return table.freeze(JsonExact)
