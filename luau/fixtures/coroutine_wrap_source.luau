local function expand(...)
	return ...
end

local errorIdentity = {}
local effects = ""

local wrapped = coroutine.wrap(function(first, ...)
	effects ..= "s"
	local reply, replyHole, replyTail = coroutine.yield("wrapped-yield", first, ...)
	effects ..= "r"
	return "wrapped-done", reply, replyHole, replyTail
end)

local firstTag, firstHead, firstHole, firstTail = wrapped(expand("wrapped-head", nil, 41))
local finalTag, finalReply, finalHole, finalTail = wrapped(expand("wrapped-reply", nil, 43))
local deadStatus, deadError = pcall(wrapped)

local failing = coroutine.wrap(function()
	coroutine.yield("wrapped-failure-yield")
	error(errorIdentity, 0)
end)
local failureTag = failing()
local failureStatus, failureValue = pcall(failing)

local result = {
	effects = effects,
	first_tag = firstTag,
	first_head = firstHead,
	first_hole = firstHole,
	first_tail = firstTail,
	final_tag = finalTag,
	final_reply = finalReply,
	final_hole = finalHole,
	final_tail = finalTail,
	dead_status = deadStatus,
	dead_error_type = type(deadError),
	failure_tag = failureTag,
	failure_status = failureStatus,
	failure_error_type = type(failureValue),
}

return function()
	return result
end
