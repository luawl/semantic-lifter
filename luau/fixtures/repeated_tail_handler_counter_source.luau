-- Author-written worker: per-item handler state. A repeat loop walks eight items; odd items take an if holding a
-- continue one if deeper. Each other item declares a click counter, fills a 34-field record, and only then stores a
-- handler that bumps and returns the counter; the handlers run after the loop.
local function worker(selector, budget)
	local handlers = {}
	local records = {}
	local index = 0
	local shown = 0
	repeat
		index += 1
		if index % 2 == 1 then
			shown = shown + 1
			if index == selector then
				continue
			end
			shown = shown + 2
		end
		local clicks = index * 10
		local record = {}
		record.f1 = shown + 1
		record.f2 = shown + 2
		record.f3 = shown + 3
		record.f4 = shown + 4
		record.f5 = shown + 5
		record.f6 = shown + 6
		record.f7 = shown + 7
		record.f8 = shown + 8
		record.f9 = shown + 9
		record.f10 = shown + 10
		record.f11 = shown + 11
		record.f12 = shown + 12
		record.f13 = shown + 13
		record.f14 = shown + 14
		record.f15 = shown + 15
		record.f16 = shown + 16
		record.f17 = shown + 17
		record.f18 = shown + 18
		record.f19 = shown + 19
		record.f20 = shown + 20
		record.f21 = shown + 21
		record.f22 = shown + 22
		record.f23 = shown + 23
		record.f24 = shown + 24
		record.f25 = shown + 25
		record.f26 = shown + 26
		record.f27 = shown + 27
		record.f28 = shown + 28
		record.f29 = shown + 29
		record.f30 = shown + 30
		record.f31 = shown + 31
		record.f32 = shown + 32
		record.f33 = shown + 33
		record.f34 = shown + 34
		records[#records + 1] = record
		handlers[#handlers + 1] = function()
			clicks += 1
			return clicks
		end
	until index >= 8
	local seen = 0
	for _, handler in handlers do
		seen = seen * 7 + handler()
	end
	return shown, index, seen, #records
end
return worker
