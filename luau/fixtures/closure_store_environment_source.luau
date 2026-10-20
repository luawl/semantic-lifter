return function()
	local function changer()
		local caller = getfenv(2)
		setfenv(2, setmetatable({ marker = "new" }, { __index = caller }))
		return "p"
	end
	local function assignment()
		setfenv(1, setmetatable({ marker = "old" }, { __index = getfenv(1) }))
		local holder = {}
		local label
		holder.get, label = function()
			return marker
		end, changer()
		return label .. ":" .. tostring(holder.get())
	end
	local function statement()
		setfenv(1, setmetatable({ marker = "old" }, { __index = getfenv(1) }))
		local inner = {}
		local outer = setmetatable({}, {
			__index = function()
				local caller = getfenv(2)
				setfenv(2, setmetatable({ marker = "new" }, { __index = caller }))
				return inner
			end,
		})
		function outer.box.get()
			return marker
		end
		return "f:" .. tostring(inner.get())
	end
	return assignment(), statement()
end
