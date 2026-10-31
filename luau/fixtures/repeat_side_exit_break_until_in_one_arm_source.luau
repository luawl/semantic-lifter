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
		fs[#fs + 1] = function(d) return (c1 or 0) + d end
	until (c1 or 0) >= 4 or total >= 6 or selector == 2 or rounds >= 16
	repeat
		rounds = rounds + 1
		local c2 = total
		total = total + 1
		if budget > 5 then
			total = total + c2 % 5
			while rounds < 28 and not (total >= 7 and budget > 5) do
				rounds = rounds + 1
				local c3
				if selector ~= 3 then
					c3 = total + rounds
				end
				repeat
					rounds = rounds + 1
					if budget > 7 then
					elseif rounds % 2 == 1 then
						fs[#fs + 1] = function(d) c3 = (c3 or 0) + d return c3 end
						continue
					else
					end
				until rounds >= 5 or selector == 2 or rounds >= 12
			end
			if selector ~= 0 then
				c2 = c2 + 3
				continue
			elseif rounds % 2 == 1 then
				c2 = c2 + 2
				fs[#fs + 1] = function(d) c2 = c2 + d return c2 end
				continue
			else
				total = total + 2
			end
			if rounds % 2 == 1 then
			end
		else
			if selector == 4 then
				if budget < 2 then
					if selector ~= 0 then
					end
				elseif budget > 5 then
					fs[#fs + 1] = function(d) c2 = c2 + d return c2 end
				end
				if selector == 4 then
					fs[#fs + 1] = function(d) c2 = c2 + d return c2 end
					continue
				end
				break
			else
				total = total + 2
				if budget < 2 then
					total = total + c2
					break
				end
			end
		end
	until c2 >= 9 or total >= 6 or budget > 5 or rounds >= 24
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
