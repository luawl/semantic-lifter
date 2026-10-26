local function worker(selector, budget)
    local total = 0
    repeat
        local step = if type(selector) == "number" then selector + 1 else 1
        if step > 2 then
            total += step
            if budget > 3 then
                continue
            end
            total += 1
        end
        total += 1
    until total > 10 or step > 5
    return total
end
return worker
