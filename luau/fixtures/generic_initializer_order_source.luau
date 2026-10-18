return function(mode, limit)
	local log = {}
	local function source(list)
		table.insert(log, "source")
		return ipairs(list)
	end
	local order = { limit, 2, 1 }
	if mode == "between" then
		local step, state, start = source(order)
		table.insert(log, "between")
		for position, entry in step, state, start do
			table.insert(log, tostring(position) .. "=" .. tostring(entry))
		end
	elseif mode == "guarded" then
		local step, state, start = source(order)
		if limit > 4 then
			table.insert(log, "between")
		end
		for position, entry in step, state, start do
			table.insert(log, tostring(position) .. "=" .. tostring(entry))
		end
	elseif mode == "reassigned" then
		local list = order
		local step, state, start = ipairs(list)
		list = { 9 }
		for position, entry in step, state, start do
			table.insert(log, tostring(position) .. "=" .. tostring(entry))
		end
		table.insert(log, tostring(#list))
	elseif mode == "outer" then
		local step, state, start = source(order)
		for round = 1, 2 do
			for position, entry in step, state, start do
				table.insert(log, tostring(round) .. ":" .. tostring(position) .. "=" .. tostring(entry))
			end
		end
	elseif mode == "break" then
		local step, state, start = source(order)
		table.insert(log, "between")
		for position, entry in step, state, start do
			table.insert(log, tostring(entry) .. "@" .. tostring(position))
			break
		end
	elseif mode == "boundary" then
		for round = 1, 2 do
			local step, state, start = source(order)
			table.insert(log, "between")
			for position, entry in step, state, start do
				return table.concat(log, ",") .. "|" .. tostring(entry) .. "@" .. tostring(position)
			end
		end
	else
		table.insert(log, "between")
		for position, entry in source(order) do
			table.insert(log, tostring(position) .. "=" .. tostring(entry))
		end
	end
	return table.concat(log, ",")
end
