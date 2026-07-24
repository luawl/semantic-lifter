local immutableKey = "dispatch"
local immutableRoot = {
	layer = {
		dispatch = function(value)
			return "value-path", value + 1
		end,
	},
}
local unresolvedValue = immutableRoot.layer[immutableKey]

local mutableKey = "before"
local mutableRoot = {
	layer = {
		before = function(value)
			return "stale", value
		end,
	},
}
local unresolvedPlace = mutableRoot.layer[mutableKey]
mutableKey = "after"
mutableRoot = {
	layer = {
		after = function(value)
			return "place-path", value + 2
		end,
	},
}
unresolvedPlace = mutableRoot.layer[mutableKey]

semantic_lifter_origin_path_key = "dispatch"
semantic_lifter_origin_path_root = {
	layer = {
		dispatch = function(value)
			return "environment-path", value + 3
		end,
	},
}
local unresolvedEnvironment = semantic_lifter_origin_path_root.layer[semantic_lifter_origin_path_key]

local literalRoot = {
	[7] = {
		[false] = function(value)
			return "literal-path", value + 5
		end,
	},
}
local unresolvedLiteral = literalRoot[7][false]

local order = ""
local function makeReceiver(tag, delta)
	local receiver = { tag = tag, delta = delta }
	return setmetatable(receiver, {
		__index = function(tableValue, key)
			order = order .. "m"
			assert(tableValue == receiver)
			assert(key == "dispatch")
			return function(self, value)
				order = order .. "c"
				assert(self == receiver)
				return self.tag, value + self.delta
			end
		end,
	})
end
local receiverKey = "target"
local receiverRoot = { layer = { target = makeReceiver("receiver-path", 4) } }
local unresolvedReceiver = receiverRoot.layer[receiverKey]

local unresolvedDirectKey = "callable"
local unresolvedDirectRoot = {}
setmetatable(unresolvedDirectRoot, {
	__index = function(tableValue, key)
		order = order .. "t"
		assert(tableValue == unresolvedDirectRoot)
		assert(key == unresolvedDirectKey)
		return function(value)
			order = order .. "d"
			return "direct-path", value + 6
		end
	end,
})

local directReceiver = makeReceiver("direct-receiver-path", 7)
local directReceiverLayer = {}
setmetatable(directReceiverLayer, {
	__index = function(tableValue, key)
		order = order .. "r"
		assert(tableValue == directReceiverLayer)
		assert(key == "target")
		return directReceiver
	end,
})
local unresolvedDirectReceiverKey = "target"
local unresolvedDirectReceiverRoot = { layer = directReceiverLayer }

local function argument(value)
	order = order .. "a"
	return value
end

return function(value)
	order = ""
	local valueTag, valueResult = unresolvedValue(value)
	local placeTag, placeResult = unresolvedPlace(value)
	local environmentTag, environmentResult = unresolvedEnvironment(value)
	local literalTag, literalResult = unresolvedLiteral(value)
	local receiverTag, receiverResult = unresolvedReceiver:dispatch(argument(value))
	local receiverOrder = order
	order = ""
	local directTag, directResult = unresolvedDirectRoot[unresolvedDirectKey](argument(value))
	local directOrder = order
	order = ""
	local directReceiverTag, directReceiverResult = unresolvedDirectReceiverRoot.layer[unresolvedDirectReceiverKey]:dispatch(argument(value))
	local directReceiverOrder = order
	return valueTag, valueResult, placeTag, placeResult, environmentTag, environmentResult, literalTag, literalResult, receiverTag, receiverResult, receiverOrder, directTag, directResult, directOrder, directReceiverTag, directReceiverResult, directReceiverOrder
end
