local function worker(selector, budget)
    local total = 0
    local fs = {}
    local last = 0
    while true do
        local cell = total * 3 + (if selector == 4 then 1 else 0)
        cell = cell + 1
        fs[#fs + 1] = function()
            return cell
        end
        cell = cell * 2
        if total >= budget % 4 + 2 or (selector == 4 and total >= 2) then
            last = cell
            break
        end
        total = total + 1
    end
    local sum = 0
    for index = 1, #fs do
        sum = sum * 7 + fs[index]()
    end
    return total, sum, last
end
return worker
