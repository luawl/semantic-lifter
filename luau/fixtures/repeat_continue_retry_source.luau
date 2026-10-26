local function worker(selector, budget)
    local attempts = 0
    local result = 0
    repeat
        attempts += 1
        if selector > 2 then
            result += selector
            if result % 2 == 0 then
                continue
            end
            result -= 1
        end
        result += 1
    until attempts >= 4 or result > budget
    return result, attempts
end
return worker
