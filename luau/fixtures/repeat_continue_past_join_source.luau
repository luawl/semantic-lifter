local function worker(selector, budget)
    local total = 0
    repeat
        if selector == 4 then
            total = total + 2
            if budget > 7 then
                continue
            end
            total = total + 1
        end
        total = total + 1
        if selector ~= 0 then
            total = total + 1
        end
    until total >= 6 or budget > 5
    total = total + 100
    return total
end
return worker
