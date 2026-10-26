-- Luau reads a register-local method receiver at NAMECALL, after the arguments ran. In every loop below a
-- closure of the same function binds the receiver (it replaces it, or only reads it), and the call's only
-- argument is an open call, so the receiver is read after that call and the call's argument pack is stored in
-- a block the loop re-enters: a loop body (a per-iteration receiver, a function-level receiver in a numeric
-- for and in a while, a receiver a closure only reads), a while condition (the loop header), a repeat-until
-- condition (the latch), an if condition inside a loop, and a generic-for initializer an outer loop re-enters.
local Proto = {}
Proto.__index = Proto
function Proto:who(_unused)
	return self.tag
end
function Proto:add(value)
	self.total += value
	return self.total
end
function Proto:more(n)
	return self.tag == "new" and n <= 2
end
function Proto:done(n)
	return (self.tag == "new" and n >= 2) or n >= 5
end
function Proto:items(n)
	local tag = self.tag
	local position = 0
	return function()
		position += 1
		if position <= n then
			return position, tag
		end
		return nil
	end
end

local function make(tag)
	return setmetatable({ tag = tag, total = 0 }, Proto)
end

local function double(index)
	return index * 2
end

local function iterationReceiver(count)
	local tags = {}
	for index = 1, count do
		local cell = make("old" .. index)
		local reset = function()
			cell = make("new" .. index)
			return 0
		end
		tags[index] = cell:who(reset())
	end
	return tags[1] .. " " .. tags[2]
end

local function outerReceiver(count)
	local object = make("old")
	local replace = function()
		object = make("new")
		return 0
	end
	local tags = {}
	for index = 1, count do
		object = make("old" .. index)
		tags[index] = object:who(replace())
	end
	return tags[1] .. " " .. tags[2]
end

local function whileReceiver(count)
	local object = make("old")
	local replace = function()
		object = make("new")
		return 0
	end
	local seen = {}
	local remaining = count
	while remaining > 0 do
		remaining -= 1
		object = make("old" .. remaining)
		table.insert(seen, object:who(replace()))
	end
	return seen[1] .. " " .. seen[2]
end

local function readOnlyReceiver(count)
	local sum = make("sum")
	local report = function()
		return sum.total
	end
	local last = 0
	for index = 1, count do
		if index == count then
			sum = make("late")
		end
		last = sum:add(double(index))
	end
	return last .. "/" .. report()
end

local function whileConditionReceiver()
	local object = make("old")
	local count = 0
	local step = function()
		count += 1
		object = make("new")
		return count
	end
	local seen = {}
	while object:more(step()) do
		table.insert(seen, count)
		object = make("old")
	end
	return #seen .. " " .. tostring(seen[1]) .. " " .. tostring(seen[2]) .. " " .. count
end

local function repeatUntilReceiver()
	local object = make("old")
	local count = 0
	local step = function()
		count += 1
		object = make("new")
		return count
	end
	local seen = {}
	repeat
		object = make("old")
		table.insert(seen, count)
	until object:done(step())
	return #seen .. " " .. tostring(seen[1]) .. " " .. tostring(seen[2]) .. " " .. count
end

local function ifConditionReceiver()
	local object = make("old")
	local count = 0
	local step = function()
		count += 1
		object = make("new")
		return count
	end
	local seen = {}
	while true do
		object = make("old")
		table.insert(seen, count)
		if object:done(step()) then
			break
		end
	end
	return #seen .. " " .. tostring(seen[1]) .. " " .. tostring(seen[2]) .. " " .. count
end

local function genericForReceiver()
	local object = make("old")
	local count = 0
	local step = function()
		count += 1
		object = make("new" .. count)
		return 2
	end
	local seen = {}
	local rounds = 0
	while rounds < 2 do
		rounds += 1
		object = make("old")
		for position, tag in object:items(step()) do
			table.insert(seen, tag .. ":" .. position)
		end
	end
	return table.concat(seen, " ")
end

return function(count)
	return iterationReceiver(count),
		outerReceiver(count),
		whileReceiver(count),
		readOnlyReceiver(count),
		whileConditionReceiver(),
		repeatUntilReceiver(),
		ifConditionReceiver(),
		genericForReceiver()
end
