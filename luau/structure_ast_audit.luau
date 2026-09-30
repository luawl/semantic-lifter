--!strict

local process = require("@lune/process")
local serde = require("@lune/serde")

local parserPath = process.args[1]
local fixtureName = process.args[2]
local generatedPath = process.args[3]
assert(parserPath ~= nil and parserPath ~= "", "expected the pinned luau-ast executable")
assert(fixtureName ~= nil and fixtureName ~= "", "expected a fixture name")
assert(generatedPath ~= nil and generatedPath ~= "", "expected generated Luau source")

local parsed = process.exec(parserPath, { generatedPath })
assert(parsed.ok, `luau-ast failed for {fixtureName}: {parsed.stderr}`)
local document: any = serde.decode("json", parsed.stdout)
assert(type(document) == "table" and type(document.root) == "table", "luau-ast returned no root node")

local counts = {
	if_statements = 0,
	while_loops = 0,
	repeat_loops = 0,
	numeric_for_loops = 0,
	generic_for_loops = 0,
}
local programCounterNames: { [string]: boolean } = {}

local function isProgramCounterName(name: string): boolean
	return name == "__lifter_pc" or string.match(name, "^__lifter_pc_%d+$") ~= nil
end

local function walk(node: any, visit: (any) -> ())
	if type(node) ~= "table" then
		return
	end
	visit(node)
	for _, child in node do
		walk(child, visit)
	end
end

walk(document.root, function(node: any)
	if node.type == "AstStatIf" then
		counts.if_statements += 1
	elseif node.type == "AstStatWhile" then
		counts.while_loops += 1
	elseif node.type == "AstStatRepeat" then
		counts.repeat_loops += 1
	elseif node.type == "AstStatFor" then
		counts.numeric_for_loops += 1
	elseif node.type == "AstStatForIn" then
		counts.generic_for_loops += 1
	elseif node.type == "AstStatLocal" then
		for _, variable in node.vars do
			if isProgramCounterName(variable.name) then
				programCounterNames[variable.name] = true
			end
		end
	end
end)

local function referencesLocal(node: any, name: string): boolean
	if type(node) ~= "table" then
		return false
	end
	if node.type == "AstExprLocal" and node["local"] ~= nil and node["local"].name == name then
		return true
	end
	for _, child in node do
		if referencesLocal(child, name) then
			return true
		end
	end
	return false
end

local function hasStateDispatchIf(node: any, name: string): boolean
	if type(node) ~= "table" then
		return false
	end
	if node.type == "AstStatIf" and referencesLocal(node.condition, name) then
		return true
	end
	for _, child in node do
		if hasStateDispatchIf(child, name) then
			return true
		end
	end
	return false
end

local function assignsLocal(node: any, name: string): boolean
	if type(node) ~= "table" then
		return false
	end
	if node.type == "AstStatAssign" then
		for _, target in node.vars do
			if target.type == "AstExprLocal" and target["local"] ~= nil and target["local"].name == name then
				return true
			end
		end
	end
	for _, child in node do
		if assignsLocal(child, name) then
			return true
		end
	end
	return false
end

local function isDispatcherLoop(node: any, name: string): boolean
	return node.type == "AstStatWhile"
		and node.condition.type == "AstExprConstantBool"
		and node.condition.value == true
		and hasStateDispatchIf(node.body, name)
		and assignsLocal(node.body, name)
end

local pcDeclarationCount = 0
local dispatcherLoopCount = 0
local detectedNames: { [string]: boolean } = {}
walk(document.root, function(node: any)
	if node.type == "AstStatLocal" then
		for _, variable in node.vars do
			if isProgramCounterName(variable.name) then
				pcDeclarationCount += 1
			end
		end
	elseif node.type == "AstStatWhile" then
		for name in programCounterNames do
			if isDispatcherLoop(node, name) then
				dispatcherLoopCount += 1
				detectedNames[name] = true
			end
		end
	end
end)

local unclassifiedProgramCounterCount = 0
for name in programCounterNames do
	if not detectedNames[name] then
		unclassifiedProgramCounterCount += 1
	end
end
assert(unclassifiedProgramCounterCount == 0, "AST contains a PC-like local without a recognized dispatcher loop")

if fixtureName == "irreducible-iteration-convergence" then
	assert(counts.numeric_for_loops > 0, "AST has no native numeric for loop")
	assert(counts.generic_for_loops > 0, "AST has no native generic for loop")
	assert(counts.while_loops == 0 and counts.repeat_loops == 0, "iteration AST unexpectedly contains a while/repeat loop")
else
	assert(counts.if_statements > 0, "AST has no structured branch statement")
	assert(counts.while_loops + counts.repeat_loops > 0, "AST has no structured loop statement")
end

local structureClass = if dispatcherLoopCount == 0 then "structured-no-dispatcher" else "dispatcher-present"
print(
	`semantic-lifter-structure fixture={fixtureName} class={structureClass}`
		.. ` pc_declarations={pcDeclarationCount} dispatcher_loops={dispatcherLoopCount}`
		.. ` ast_if={counts.if_statements} ast_while={counts.while_loops}`
		.. ` ast_repeat={counts.repeat_loops} ast_numeric_for={counts.numeric_for_loops}`
		.. ` ast_generic_for={counts.generic_for_loops}`
)
