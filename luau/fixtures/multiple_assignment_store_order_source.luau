-- Luau 0.720 runs a multiple assignment in this order: the targets' tables and keys, then the values left to
-- right, writing a register-local target as soon as its value exists when no later value names it at run time
-- and it is no table target's table or key; then the table, global and upvalue stores in target order, each
-- taking a register-local table, key or value at its own store; then the remaining local targets. Code that
-- runs inside the statement (a table's or the environment's __newindex, a later value, a raising store) sees
-- that order. A name inside a type annotation is not a run-time use. Children that hold a statement are table
-- fields, and the module uses setfenv, so no optimisation level inlines them.
local function trap(onStore)
	return setmetatable({}, {
		__newindex = function(t, k, v)
			rawset(t, k, v)
			onStore(k, v)
		end,
	})
end

local cases = {}

function cases.storeOperands(seed)
	local first: any, other: any, bag, sink = {}, {}, {}, {}
	local second, key, value = first, "a", seed
	local hook = trap(function()
		second, key, value = other, "b", "new"
	end)
	hook.x, second.y, bag[key], sink.z = 1, 2, 3, value
	return tostring(first.y) .. "/" .. tostring(other.y) .. "/" .. tostring(bag.a) .. "/" .. tostring(bag.b) .. "/" .. tostring(sink.z)
end

function cases.environment(seed)
	local up = seed
	local box = {}
	local onStore = function(_k) end
	local environment = trap(function(k)
		onStore(k)
	end)
	function box.worker()
		local value, u, first: any, other: any, log = seed, seed, {}, {}, ""
		local target = first
		onStore = function(k)
			log = log .. k .. "=" .. u .. ";"
			value, target = "new", other
		end
		GLOBAL_A, u, GLOBAL_B, target.y, up = 1, "new", value, 2, value
		return log, first.y, other.y
	end
	setfenv(box.worker, environment)
	local log, firstY, otherY = box.worker()
	return log .. tostring(rawget(environment, "GLOBAL_B")) .. "/" .. tostring(firstY) .. "/" .. tostring(otherY) .. "/" .. tostring(up)
end

function cases.upvalueStore(seed)
	local up = seed
	local box = {}
	function box.store()
		local value = seed
		local hook = trap(function()
			value = "new"
		end)
		hook.x, up = 1, value
	end
	box.store()
	return up
end

function cases.localTiming(seed)
	local u, w, log = seed, seed, ""
	local sink = {}
	local hook = trap(function(k)
		log = log .. k .. "=" .. u .. ";"
		w = "hook"
	end)
	hook.x, u, sink.y, w = 1, "new", w, "last"
	return log .. tostring(sink.y) .. "/" .. w
end

function cases.controls(seed)
	local value = seed
	local sink = {}
	local hook = trap(function()
		value = "new"
	end)
	hook.x, sink.y, sink.z = 1, value
	local up = seed
	local box = {}
	function box.store()
		local own = seed
		local ownHook = trap(function()
			own = "new"
		end)
		up, ownHook.x = own, 1
	end
	box.store()
	return tostring(sink.y) .. "/" .. tostring(sink.z) .. "/" .. tostring(up)
end

function cases.valueObservers(seed)
	local u, v, seen = seed, nil, nil
	local function peek()
		seen = u
		return u
	end
	u, v = "new", peek()
	local laterValue = v
	u = seed
	u, v = "new", 1, peek()
	return laterValue .. "/" .. seen
end

function cases.conflicts(seed)
	local u, log = seed, ""
	local t = trap(function(k, v)
		log = log .. tostring(k) .. "=" .. u .. "/" .. tostring(v) .. ";"
	end)
	u, t.x = "new", u
	u = seed
	u, t[u] = "new", 1
	return log .. u
end

function cases.orders(seed)
	local u, log = seed, ""
	local t = trap(function(k)
		log = log .. k .. "=" .. u .. ";"
	end)
	local function pair()
		return "new", 1
	end
	u, t.x = pair()
	local spread = log
	local v, w
	u = seed
	local function current()
		return u
	end
	v, u, w = u, "new", current()
	return spread .. v .. "/" .. u .. "/" .. w
end

function cases.raisingStore(seed)
	local holder: any = {}
	local box = {}
	function box.early()
		local u, w = seed, seed
		holder.early = function()
			return u .. "/" .. w
		end
		local missing = holder.none
		u, missing.x, w = "new", 1, "last"
	end
	function box.postponed()
		local e = holder.none
		holder.postponed = function()
			return type(e)
		end
		e, e.x = {}, 1
	end
	local first = pcall(box.early)
	local second = pcall(box.postponed)
	return tostring(first) .. "/" .. holder.early() .. "/" .. tostring(second) .. "/" .. holder.postponed()
end

function cases.typeLevel(seed)
	local u, v, x, log = seed, nil, nil, ""
	local function current()
		return u
	end
	u, v = "new", current() :: typeof(u)
	local assertion = v
	u = seed
	u, v = "new", (function(_x: typeof(u))
		return current()
	end)(1)
	local parameter = v
	u = seed
	u, v = "new", (function(): typeof(u)
		return current()
	end)()
	local returned = v
	u = seed
	u, v = "new", (function()
		type Alias = typeof(u)
		return current()
	end)()
	local aliased = v
	u = seed
	local w: typeof(u) = "w"
	u, x, v = "new", w, current()
	local declared = v
	u = seed
	local t = trap(function(k)
		log = log .. k .. "=" .. u .. ";"
	end)
	u, t.x = "new", w
	u = seed
	u, t.y = "new", (1 :: typeof(u))
	u = seed
	u, v = "new", (function()
		return u
	end)()
	return assertion .. "/" .. parameter .. "/" .. returned .. "/" .. aliased .. "/" .. declared .. "/" .. log .. v
end

function cases.combined(seed)
	local u, log = seed, ""
	local w: typeof(u) = seed
	local sink = {}
	local t = trap(function(k)
		log = log .. k .. "=" .. u .. ";"
		w = "new"
	end)
	t.x, u, sink.y = 1, "new", w
	return log .. tostring(sink.y)
end

return function(seed)
	return cases.storeOperands(seed),
		cases.environment(seed),
		cases.upvalueStore(seed),
		cases.localTiming(seed),
		cases.controls(seed),
		cases.valueObservers(seed),
		cases.conflicts(seed),
		cases.orders(seed),
		cases.raisingStore(seed),
		cases.typeLevel(seed),
		cases.combined(seed)
end
