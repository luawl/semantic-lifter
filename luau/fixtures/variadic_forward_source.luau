return function(...)
	local forward = function(prefix, ...)
		return prefix, ...
	end
	local produce = function(...)
		return ...
	end
	return forward("head", produce(...))
end
