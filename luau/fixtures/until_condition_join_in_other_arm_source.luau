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
		local c1 = rounds
		total = total + 2
		c1 = c1 + 4
		if budget > 5 then
			total = total + 1
			repeat
				rounds = rounds + 1
				local c2 = total
				if selector == 4 then
				elseif selector ~= 0 then
				else
				end
			until rounds >= 9 or budget > 7 or rounds >= 28
		elseif budget > 7 then
			if total > 4 and selector ~= 1 then
				while rounds < 24 and not (total >= 8 and budget > 5) do
					rounds = rounds + 1
					local c3 = total + rounds
					for pass = 1, 5 do
						rounds = rounds + 1
					end
				end
				local b4 = total
				local function c4(d)
					b4 = b4 + d
					return b4
				end
				break
			elseif selector == 3 or budget > 9 then
				if rounds % 2 == 1 then
					if budget < 2 then
					else
					end
					continue
				end
				c1 = c1 + 2
			else
				c1 = c1 + 2
				c1 = c1 + 5
			end
			fs[#fs + 1] = function(d) return c1 + d end
			continue
		end
	until c1 >= 5 or total >= 6 or selector == 2 or rounds >= 20
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
