return function(mode, limit)
	local log = {}
	local function source(list)
		table.insert(log, "source")
		return ipairs(list)
	end
	local order = { limit, 2, 1 }
	if mode == "after" then
		local step, state, start = source(order)
		for position, entry in step, state, start do
			table.insert(log, tostring(position) .. "=" .. tostring(entry))
		end
		table.insert(log, "after=" .. tostring(start) .. "/" .. type(step) .. "/" .. tostring(state == order))
	elseif mode == "body" then
		local step, state, start = source(order)
		for position, entry in step, state, start do
			table.insert(log, tostring(position) .. "#" .. tostring(#state))
		end
	elseif mode == "break" then
		local step, state, start = source(order)
		for position, entry in step, state, start do
			table.insert(log, tostring(entry) .. "@" .. tostring(position))
			break
		end
		table.insert(log, "after=" .. tostring(start) .. "/" .. type(step))
	elseif mode == "boundary" then
		if limit > 4 then
			order = {}
		end
		for round = 1, 2 do
			local step, state, start = source(order)
			for position, entry in step, state, start do
				return table.concat(log, ",") .. "|" .. tostring(entry) .. "@" .. tostring(position)
			end
			table.insert(log, tostring(round) .. ":" .. tostring(start) .. "/" .. type(step))
		end
	elseif mode == "unread" then
		local step, state, start = source(order)
		for position, entry in step, state, start do
			table.insert(log, tostring(position) .. "=" .. tostring(entry))
		end
	else
		for position, entry in source(order) do
			table.insert(log, tostring(position) .. "=" .. tostring(entry))
		end
	end
	return table.concat(log, ",")
end
