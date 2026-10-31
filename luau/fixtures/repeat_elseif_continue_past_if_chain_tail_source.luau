local function worker(selector, budget)
	if type(selector) ~= "number" then
		selector = 1
	end
	if type(budget) ~= "number" then
		budget = 2
	end
	local total = 0
	local rounds = 0
	local fs = {}
	repeat
		rounds = rounds + 1
		local c1
		if selector ~= 3 then
			c1 = total + rounds
		end
		if budget < 2 then
			repeat
				rounds = rounds + 1
				total = total + 1
			until total >= 9 or budget > 5 or rounds >= 24
			fs[#fs + 1] = function(d) return d + 1 end
			fs[#fs + 1] = function(d) return d + 2 end
		elseif total % 3 == 0 then
			if selector == 3 or budget > 9 then
				c1 = (c1 or 0) + 4
				local b2 = rounds * 3
				local function c2(d)
					b2 = b2 + d
					return b2
				end
				total = total + (c1 or 0)
				break
			elseif total % 3 == 0 then
				while rounds < 24 and not (total >= 7 and budget > 5) do
					rounds = rounds + 1
					local c3 = rounds
					fs[#fs + 1] = function(d) return d + 1 end
				end
				if total % 3 == 0 then
				end
				fs[#fs + 1] = function(d) return d + 1 end
				continue
			end
			local b4 = 4
			local function c4(d)
				b4 = b4 + d
				return b4
			end
			total = total + b4 % 5
			continue
		else
			if total % 3 == 0 then
				for pass = 1, 3 do
					rounds = rounds + 1
					local c5 = rounds
					total = total + c5 % 5
				end
				local b6 = rounds * 7
				local function c6(d)
					b6 = b6 + d
					return b6
				end
			elseif selector == 4 then
				c1 = (c1 or 0) + 1
				if selector == 4 then
					break
				elseif budget > 5 then
					fs[#fs + 1] = function(d) return d + 1 end
					continue
				end
			end
		end
		total = total + (c1 or 0) % 5
		repeat
			rounds = rounds + 1
			local b7 = rounds
			local function c7(d)
				b7 = b7 + d
				return b7
			end
			total = total + 1
			total = total + 1
		until total >= 9 or budget > 7 or rounds >= 16
		if budget < 2 then
			total = total + 2
			fs[#fs + 1] = function(d) return d + 1 end
			continue
		end
	until (c1 or 0) >= 6 or rounds >= 5 or budget > 5 or rounds >= 12
	local sum = 0
	for index = 1, #fs do
		sum = (sum * 7 + fs[index](index)) % 1000003
	end
	for index = 1, #fs do
		sum = (sum * 5 + fs[index](0)) % 1000003
	end
	return total + 100, sum, rounds
end
return worker
