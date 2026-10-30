local function worker(selector, budget)
    local total = 0
    local base = if budget > 5 then 2 else 0
    local fs = {}
    repeat
        local cell = total * 3 + (if selector == 4 then 1 else 0) + base
        cell = cell + 1
        fs[#fs + 1] = function()
            return cell
        end
        cell = cell * 2
        if total >= 4 or (selector == 4 and total >= 2) then
            cell = cell + 100
            break
        end
        total = total + 1
    until false
    local sum = 0
    for index = 1, #fs do
        sum = sum * 7 + fs[index]()
    end
    return total, sum
end
return worker
