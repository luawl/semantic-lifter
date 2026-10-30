local function worker(selector, budget)
    local total = 0
    local trail = 0
    local last = 0
    while true do
        local cell = total * 3 + (if selector == 4 then 1 else 0)
        cell = cell + 1
        trail = trail * 7 + cell
        cell = cell * 2
        if total >= budget % 4 + 2 or (selector == 4 and total >= 2) then
            last = cell
            break
        end
        total = total + 1
    end
    return total, trail, last
end
return worker
