local function worker(selector, budget)
    local total = 0
    repeat
        if selector == 4 then
            total = total + 2
        elseif budget > 7 then
            total = total + 3
            continue
        end
        total = total + 1
    until total >= 6
    total = total + 100
    return total
end
return worker
