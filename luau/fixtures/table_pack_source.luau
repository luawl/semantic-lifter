return function(dynamicKey, ...)
	local function produce()
		return 3, nil, 5
	end

	local fromCall = { 1, 2, produce() }
	local fromVarargs = { "head", ... }
	local mixed = {
		marker = "ok",
		[2] = "overwritten",
		10,
		produce(),
	}
	local ordered = {
		[dynamicKey] = "dynamic",
		"prefix",
		produce(),
	}

	return fromCall[1],
		fromCall[2],
		fromCall[3],
		fromCall[4],
		fromCall[5],
		fromVarargs[1],
		fromVarargs[2],
		fromVarargs[3],
		fromVarargs[4],
		mixed.marker,
		mixed[1],
		mixed[2],
		mixed[3],
		mixed[4],
		ordered[dynamicKey],
		ordered[1],
		ordered[2],
		ordered[3],
		ordered[4]
end
