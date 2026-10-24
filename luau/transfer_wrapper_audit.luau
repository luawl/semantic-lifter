--!strict
-- Transfer wrapper audit for structured generated texts: no `repeat ... until true` transfer wrapper may only
-- forward escape flags, and no wrapper may declare a stop flag (`local __lifter_escape_<n> = false` right before its
-- `repeat`) that nothing in its scope sets or reads.
-- A wrapper only forwards flags when the flag it declares, if any, is such a dead declaration; no `continue` binds to
-- it; every `break` that binds to it (through `if` arms and `do` blocks) follows a set of, or is the whole body of a
-- consumer `if <flag> then break end` of, a flag that the propagation right after its `until true` re-dispatches with
-- a `break`; every consumer in that propagation is a `break`; and every set of such a flag that reaches `until true`
-- without a `break` is the last statement on its path. Without that wrapper the same transfers leave the statement
-- around it directly. A wrapper with no declaration counts on the same rules, unless it sets a flag its propagation
-- does not read.
-- A passing run prints nothing. A failing run prints one line per finding, `<path> forwarding <line of repeat>` or
-- `<path> dead-flag <line of declaration> <flag>`, and fails one assertion that counts them. With --counts it prints
-- `<path> forwarding=<f> dead=<d>` for every text and asserts nothing.
-- argv: [--counts] <generated Luau path>...
local fs = require("@lune/fs")
local process = require("@lune/process")

type Token = { v: string, line: number }
type Arm = { line: number, items: { Item } }
type Item = { kind: string, line: number, endLine: number, cond: string, arms: { Arm }, nested: { Item } }
type Consumer = { flag: string, kind: string }
type ParentIf = { item: Item, list: { Item }, index: number, arm: Arm }
type Site = { kind: string, list: { Item }, index: number, bare: boolean, parentIf: ParentIf? }
type Wrapper = {
	flag: string?,
	declLine: number,
	repeatLine: number,
	dead: boolean,
	continues: number,
	breaks: { string },
	loose: { { cls: string, tail: boolean } },
	post: { Consumer },
}

local function lex(text: string): { Token }
	local tokens: { Token } = {}
	local line = 0
	local i = 1
	local n = #text
	local function push(value: string)
		table.insert(tokens, { v = value, line = line })
	end
	local function countLines(first: number, last: number)
		for k = first, last do
			if string.byte(text, k) == 10 then
				line += 1
			end
		end
	end
	while i <= n do
		local c = string.sub(text, i, i)
		if c == "\n" then
			line += 1
			i += 1
		elseif c == " " or c == "\t" or c == "\r" then
			i += 1
		elseif c == "-" and string.sub(text, i + 1, i + 1) == "-" then
			local equals = string.match(text, "^%-%-%[(=*)%[", i)
			if equals ~= nil then
				local close = "]" .. equals .. "]"
				local stop = string.find(text, close, i, true)
				local last = if stop == nil then n else stop + #close - 1
				countLines(i, last)
				i = last + 1
			else
				while i <= n and string.sub(text, i, i) ~= "\n" do
					i += 1
				end
			end
		elseif c == '"' or c == "'" or c == "`" then
			local k = i + 1
			while k <= n and string.sub(text, k, k) ~= c do
				if string.sub(text, k, k) == "\\" then
					k += 1
				end
				if string.sub(text, k, k) == "\n" then
					line += 1
				end
				k += 1
			end
			push("<str>")
			i = k + 1
		elseif c == "[" and string.match(text, "^%[=*%[", i) ~= nil then
			local equals = string.match(text, "^%[(=*)%[", i) :: string
			local close = "]" .. equals .. "]"
			local stop = string.find(text, close, i, true)
			local last = if stop == nil then n else stop + #close - 1
			countLines(i, last)
			push("<str>")
			i = last + 1
		elseif string.match(c, "[%a_]") ~= nil then
			local word = string.match(text, "^[%a_][%w_]*", i) :: string
			push(word)
			i += #word
		elseif string.match(c, "%d") ~= nil then
			local number = string.match(text, "^%d[%w_%.]*", i) :: string
			push("<num>")
			i += #number
		else
			push(c)
			i += 1
		end
	end
	return tokens
end

local function parse(tokens: { Token }): { Item }
	local p = 1
	local parseArm: (stops: { [string]: boolean }) -> { Item }
	local function expectWord(word: string): Token
		local token = tokens[p]
		assert(token ~= nil and token.v == word, `expected {word} at {if token ~= nil then tostring(token.line + 1) else "the end"}`)
		p += 1
		return token
	end
	local function parseFunction(): Item
		local token = expectWord("function")
		while p <= #tokens and tokens[p].v ~= "(" do
			p += 1
		end
		local depth = 0
		while p <= #tokens do
			if tokens[p].v == "(" then
				depth += 1
			end
			if tokens[p].v == ")" then
				depth -= 1
				if depth == 0 then
					p += 1
					break
				end
			end
			p += 1
		end
		local body = parseArm({ ["end"] = true })
		local close = expectWord("end")
		return { kind = "function", line = token.line, endLine = close.line, cond = "", arms = { { line = token.line, items = body } }, nested = {} }
	end
	local function consumeUntil(word: string)
		while p <= #tokens and tokens[p].v ~= word do
			if tokens[p].v == "function" then
				parseFunction()
			else
				p += 1
			end
		end
	end
	parseArm = function(stops: { [string]: boolean }): { Item }
		local items: { Item } = {}
		while p <= #tokens and not stops[tokens[p].v] do
			local token = tokens[p]
			if token.v == "if" then
				p += 1
				consumeUntil("then")
				expectWord("then")
				local arms: { Arm } = { { line = token.line, items = parseArm({ ["elseif"] = true, ["else"] = true, ["end"] = true }) } }
				while tokens[p] ~= nil and tokens[p].v == "elseif" do
					local middle = tokens[p]
					p += 1
					consumeUntil("then")
					expectWord("then")
					table.insert(arms, { line = middle.line, items = parseArm({ ["elseif"] = true, ["else"] = true, ["end"] = true }) })
				end
				if tokens[p] ~= nil and tokens[p].v == "else" then
					local middle = tokens[p]
					p += 1
					table.insert(arms, { line = middle.line, items = parseArm({ ["end"] = true }) })
				end
				local close = expectWord("end")
				table.insert(items, { kind = "if", line = token.line, endLine = close.line, cond = "", arms = arms, nested = {} })
			elseif token.v == "while" or token.v == "for" then
				p += 1
				consumeUntil("do")
				expectWord("do")
				local body = parseArm({ ["end"] = true })
				local close = expectWord("end")
				table.insert(items, { kind = "loop", line = token.line, endLine = close.line, cond = "", arms = { { line = token.line, items = body } }, nested = {} })
			elseif token.v == "do" then
				p += 1
				local body = parseArm({ ["end"] = true })
				local close = expectWord("end")
				table.insert(items, { kind = "do", line = token.line, endLine = close.line, cond = "", arms = { { line = token.line, items = body } }, nested = {} })
			elseif token.v == "repeat" then
				p += 1
				local body = parseArm({ ["until"] = true })
				local close = expectWord("until")
				local words: { string } = {}
				while p <= #tokens and tokens[p].line == close.line do
					table.insert(words, tokens[p].v)
					p += 1
				end
				table.insert(items, { kind = "repeat", line = token.line, endLine = close.line, cond = table.concat(words, " "), arms = { { line = token.line, items = body } }, nested = {} })
			elseif token.v == "break" or token.v == "continue" then
				p += 1
				table.insert(items, { kind = token.v :: string, line = token.line, endLine = token.line, cond = "", arms = {}, nested = {} })
			elseif token.v == "function" then
				local fn = parseFunction()
				table.insert(items, { kind = "simple", line = token.line, endLine = fn.endLine, cond = "", arms = {}, nested = { fn } })
			else
				local start = p
				local nested: { Item } = {}
				local line = token.line
				local endLine = token.line
				while p <= #tokens and tokens[p].line == line do
					if tokens[p].v == "function" then
						local fn = parseFunction()
						table.insert(nested, fn)
						endLine = fn.endLine
						line = fn.endLine
					elseif (tokens[p].v == "end" or tokens[p].v == "until") and p ~= start then
						break
					else
						p += 1
					end
				end
				table.insert(items, { kind = "simple", line = token.line, endLine = endLine, cond = "", arms = {}, nested = nested })
			end
		end
		return items
	end
	return parseArm({})
end

local function audit(text: string): { Wrapper }
	local lines = string.split(text, "\n")
	local items = parse(lex(text))
	local function textOf(item: Item?): string
		if item == nil then
			return ""
		end
		local raw = lines[item.line + 1]
		return if raw == nil then "" else string.match(raw, "^%s*(.-)%s*$") :: string
	end
	local function indentOf(line: number): number
		return #(string.match(lines[line + 1] or "", "^ *") :: string)
	end
	local function isWrapper(item: Item?): boolean
		return item ~= nil and item.kind == "repeat" and item.cond == "true"
	end
	local function setFlagOf(item: Item?): string?
		if item == nil or item.kind ~= "simple" then
			return nil
		end
		return string.match(textOf(item), "^(__lifter_escape_[%w_]+) = true$")
	end
	local function isBreakItem(item: Item?): boolean
		if item == nil then
			return false
		end
		return item.kind == "break" or (item.kind == "do" and #item.arms[1].items == 1 and item.arms[1].items[1].kind == "break")
	end
	local function consumerOf(item: Item?): Consumer?
		if item == nil or item.kind ~= "if" or #item.arms ~= 1 then
			return nil
		end
		local flag = string.match(textOf(item), "^if (__lifter_escape_[%w_]+) then$")
		if flag == nil then
			return nil
		end
		local body = item.arms[1].items
		local kind = "other"
		if #body == 1 and body[1].kind == "break" then
			kind = "break"
		elseif #body >= 1 then
			local last = body[#body]
			local lastContinues = last.kind == "continue" or (last.kind == "do" and #last.arms[1].items == 1 and last.arms[1].items[1].kind == "continue")
			local restAssigns = true
			for index = 1, #body - 1 do
				local assigned = textOf(body[index])
				if body[index].kind ~= "simple" or (string.match(assigned, "^__lifter_native_iteration_complete_%d+ = true$") == nil and string.match(assigned, "^__lifter_native_iteration_complete_%d+ = false$") == nil) then
					restAssigns = false
				end
			end
			if lastContinues and restAssigns then
				kind = "continue"
			end
		end
		return { flag = flag, kind = kind }
	end
	local function startsWithName(line: string, prefix: string): boolean
		return string.sub(line, 1, #prefix) == prefix and string.match(string.sub(line, #prefix + 1, #prefix + 1), "[%w_]") == nil
	end
	-- Sets and reads of `flag` in `list`, until a declaration of the same name shadows it (each nested list stops at
	-- its own shadowing declaration only).
	local function countUses(list: { Item }, flag: string, reads: boolean): number
		local found = 0
		local word = "%f[%w_]" .. flag .. "%f[^%w_]"
		for _, item in list do
			local line = textOf(item)
			if item.kind == "simple" and startsWithName(line, "local " .. flag) then
				return found
			end
			if reads then
				if string.match(line, word) ~= nil and line ~= flag .. " = true" and line ~= flag .. " = false" then
					found += 1
				end
			elseif item.kind == "simple" and line == flag .. " = true" then
				found += 1
			end
			for _, arm in item.arms do
				found += countUses(arm.items, flag, reads)
			end
			for _, fn in item.nested do
				for _, arm in fn.arms do
					found += countUses(arm.items, flag, reads)
				end
			end
		end
		return found
	end
	local function bindingSites(list: { Item }, sites: { Site }, parentIf: ParentIf?)
		for index, item in list do
			if item.kind == "break" or item.kind == "continue" then
				table.insert(sites, { kind = item.kind :: string, list = list, index = index, bare = true, parentIf = parentIf })
			elseif item.kind == "do" then
				local body = item.arms[1].items
				if #body == 1 and (body[1].kind == "break" or body[1].kind == "continue") then
					table.insert(sites, { kind = body[1].kind :: string, list = list, index = index, bare = false, parentIf = parentIf })
				else
					bindingSites(body, sites, nil)
				end
			elseif item.kind == "if" then
				for _, arm in item.arms do
					bindingSites(arm.items, sites, { item = item, list = list, index = index, arm = arm })
				end
			end
		end
	end
	local function looseSets(list: { Item }, inTail: boolean, out: { { flag: string, tail: boolean } })
		for index, item in list do
			local tail = inTail and index == #list
			local flag = setFlagOf(item)
			if flag ~= nil and not isBreakItem(list[index + 1]) then
				table.insert(out, { flag = flag, tail = tail })
			end
			if item.kind == "do" then
				looseSets(item.arms[1].items, tail, out)
			elseif item.kind == "if" then
				for _, arm in item.arms do
					looseSets(arm.items, tail, out)
				end
			end
		end
	end
	local wrappers: { Wrapper } = {}
	local function describe(list: { Item }, index: number)
		local item = list[index]
		local before = list[index - 1]
		local flag = if before ~= nil and before.kind == "simple" then string.match(textOf(before), "^local (__lifter_escape_[%w_]+) = false$") else nil
		local untilIndent = indentOf(item.endLine)
		local post: { Consumer } = {}
		local postBreak: { [string]: boolean } = {}
		local seen: { [string]: boolean } = {}
		for k = index + 1, #list do
			local consumer = consumerOf(list[k])
			if consumer == nil or indentOf(list[k].line) ~= untilIndent or seen[consumer.flag] then
				break
			end
			seen[consumer.flag] = true
			table.insert(post, consumer)
			if consumer.kind == "break" then
				postBreak[consumer.flag] = true
			end
		end
		local body = item.arms[1].items
		local sites: { Site } = {}
		bindingSites(body, sites, nil)
		local breaks: { string } = {}
		local continues = 0
		for _, site in sites do
			if site.kind == "continue" then
				continues += 1
				continue
			end
			local cls = "other"
			local previous = if site.index > 1 then setFlagOf(site.list[site.index - 1]) else nil
			local parentIf = site.parentIf
			if previous ~= nil then
				cls = if previous == flag then "own" elseif postBreak[previous] then "fwd" else "other-set"
			elseif site.bare and parentIf ~= nil and #parentIf.arm.items == 1 and #parentIf.item.arms == 1 then
				local consumer = consumerOf(parentIf.item)
				if consumer ~= nil then
					local k = parentIf.index - 1
					while k >= 1 and consumerOf(parentIf.list[k]) ~= nil do
						k -= 1
					end
					local anchor = if k >= 1 then parentIf.list[k] else nil
					local after = if isWrapper(anchor) then "wrapper" elseif anchor ~= nil and (anchor.kind == "loop" or anchor.kind == "repeat") then "loop" else "other"
					cls = if consumer.flag == flag then "own" elseif not postBreak[consumer.flag] then "other-consumer" else "relay-" .. after
				end
			end
			table.insert(breaks, cls)
		end
		local loose: { { flag: string, tail: boolean } } = {}
		looseSets(body, true, loose)
		local classified: { { cls: string, tail: boolean } } = {}
		for _, set in loose do
			table.insert(classified, { cls = if set.flag == flag then "own" elseif postBreak[set.flag] then "post" else "unrelated", tail = set.tail })
		end
		local dead = false
		if flag ~= nil then
			local after: { Item } = table.move(list, index + 1, #list, 1, {})
			local from: { Item } = table.move(list, index, #list, 1, {})
			dead = countUses(body, flag, false) == 0 and countUses(after, flag, false) == 0 and countUses(from, flag, true) == 0
		end
		table.insert(wrappers, {
			flag = flag,
			declLine = if before ~= nil then before.line + 1 else 0,
			repeatLine = item.line + 1,
			dead = dead,
			continues = continues,
			breaks = breaks,
			loose = classified,
			post = post,
		})
	end
	local function visit(list: { Item })
		for index, item in list do
			if isWrapper(item) then
				describe(list, index)
			end
			for _, arm in item.arms do
				visit(arm.items)
			end
			for _, fn in item.nested do
				for _, arm in fn.arms do
					visit(arm.items)
				end
			end
		end
	end
	visit(items)
	return wrappers
end

local function forwardsOnly(wrapper: Wrapper): boolean
	if wrapper.flag ~= nil and not wrapper.dead then
		return false
	end
	for _, set in wrapper.loose do
		if set.cls == "own" or (set.cls == "post" and not set.tail) or (wrapper.flag == nil and set.cls == "unrelated") then
			return false
		end
	end
	if wrapper.continues > 0 then
		return false
	end
	for _, consumer in wrapper.post do
		if consumer.kind ~= "break" then
			return false
		end
	end
	for _, cls in wrapper.breaks do
		if cls ~= "fwd" and cls ~= "relay-wrapper" and cls ~= "relay-loop" then
			return false
		end
	end
	return true
end

local counts = process.args[1] == "--counts"
local first = if counts then 2 else 1
assert(process.args[first] ~= nil, "expected at least one generated Luau path")
local findings = 0
local texts = 0
for index = first, #process.args do
	local path = process.args[index]
	texts += 1
	local forwarding = 0
	local dead = 0
	for _, wrapper in audit(fs.readFile(path)) do
		if forwardsOnly(wrapper) then
			forwarding += 1
			if not counts then
				print(`{path} forwarding {wrapper.repeatLine}`)
			end
		end
		if wrapper.flag ~= nil and wrapper.dead then
			dead += 1
			if not counts then
				print(`{path} dead-flag {wrapper.declLine} {wrapper.flag}`)
			end
		end
	end
	if counts then
		print(`{path} forwarding={forwarding} dead={dead}`)
	end
	findings += forwarding + dead
end
if not counts then
	assert(findings == 0, `{findings} transfer wrapper findings in {texts} texts`)
end
