return function(value: number)
	local subject = { value = value, calls = 0 }
	setmetatable(subject, {
		__tostring = function(self)
			self.calls += 1
			return "box:" .. self.value
		end,
	})
	local literalByte = "\255"
	local rendered = `\254prefix %{value} {subject} {nil} {false} suffix`
	return literalByte .. rendered, subject.calls
end
