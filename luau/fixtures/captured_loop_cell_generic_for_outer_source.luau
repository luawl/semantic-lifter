local function worker(selector, budget)
    local total = 0
    local fs = {}
    local last = 0
    for _, item in ipairs({ 1, 2 }) do
        total = 0
        while true do
            local cell = total * 3 + item
            cell = cell + 1
            fs[#fs + 1] = function()
                return cell
            end
            if total >= 3 or (selector == 4 and total >= 1) then
                last = last + cell
                break
            end
            total = total + 1
        end
    end
    local sum = 0
    for index = 1, #fs do
        sum = sum * 7 + fs[index]()
    end
    return total, sum, last
end
return worker
