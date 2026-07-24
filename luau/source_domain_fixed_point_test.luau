--!strict

local AstFrontend = require("./ast_frontend")

local nextLocation = 0

local function node(fields: any): any
	nextLocation += 1
	fields.location = `source-domain:{nextLocation}`
	return fields
end

local function number(value: number): any
	return node({ type = "AstExprConstantNumber", value = value })
end

local function stringValue(value: string): any
	return node({ type = "AstExprConstantString", value = value })
end

local function global(name: string): any
	return node({ type = "AstExprGlobal", global = name })
end

local function localIdentity(name: string): any
	return node({ type = "AstLocal", name = name })
end

local function localExpression(identity: any): any
	return node({ type = "AstExprLocal", ["local"] = identity })
end

local function add(left: any, right: any): any
	return node({ type = "AstExprBinary", op = "Add", left = left, right = right })
end

local function ifExpression(condition: any, trueExpression: any, falseExpression: any): any
	return node({
		type = "AstExprIfElse",
		condition = condition,
		trueExpr = trueExpression,
		falseExpr = falseExpression,
	})
end

local function declare(identity: any, value: any): any
	return node({ type = "AstStatLocal", vars = { identity }, values = { value } })
end

local function assign(identity: any, value: any): any
	return node({ type = "AstStatAssign", vars = { localExpression(identity) }, values = { value } })
end

local function returnValue(value: any): any
	return node({ type = "AstStatReturn", list = { value } })
end

local function closure(body: { any }): any
	return node({
		type = "AstExprFunction",
		args = {},
		vararg = false,
		body = node({ type = "AstStatBlock", body = body }),
	})
end

local function document(body: { any }): any
	return { root = node({ type = "AstStatBlock", body = body }) }
end

local function hasExactPureEffects(effects: any): boolean
	return effects.precision == "exact"
		and not effects.reads_memory
		and not effects.writes_memory
		and not effects.may_throw
		and not effects.may_yield
		and not effects.invokes_unknown_code
end

local function lift(name: string, body: { any }): any
	local result = AstFrontend.tryLift(document(body), { program_id = name, source_name = name })
	assert(result.program ~= nil and #result.diagnostics == 0, `{name} was rejected`)
	return result.program :: any
end

local source = localIdentity("transitive_source")
local derived = localIdentity("transitive_derived")
local placeProgram = lift("frontend-transitive-place-domain", {
	declare(source, number(1)),
	assign(source, number(2)),
	declare(derived, add(localExpression(source), number(0.5))),
	assign(derived, add(localExpression(source), number(1.5))),
	returnValue(add(localExpression(derived), number(1))),
})

local placeAddCount = 0
local placePureAddCount = 0
local placeReturnType: any = nil
local sourceType: any = nil
local derivedType: any = nil
for _, place in placeProgram.places do
	if place.name_hint == "transitive_source" then
		sourceType = place.type
	elseif place.name_hint == "transitive_derived" then
		derivedType = place.type
	end
end
for _, instruction in placeProgram.instructions do
	if instruction.operation.binary ~= nil and instruction.operation.binary.operator == "add" then
		placeAddCount += 1
		placePureAddCount += if hasExactPureEffects(instruction.effects) then 1 else 0
	end
end
for _, block in placeProgram.blocks do
	if block.terminator.return_values ~= nil then
		assert(#block.terminator.return_values == 1, "transitive place result changed arity")
		placeReturnType = placeProgram.values[block.terminator.return_values[1] + 1].type
	end
end
assert(sourceType ~= nil and sourceType.kind == "integer", "transitive source place lost its concrete domain")
assert(derivedType ~= nil and derivedType.kind == "number", "operator-derived place did not reach its concrete domain")
assert(
	placeAddCount == 3 and placePureAddCount == 3 and placeReturnType ~= nil and placeReturnType.kind == "number",
	"transitive place/operator domains did not converge"
)

local joinSource = localIdentity("transitive_join_source")
local joinProgram = lift("frontend-transitive-join-domain", {
	declare(joinSource, number(1)),
	assign(joinSource, number(2)),
	returnValue(add(
		ifExpression(
			global("transitive_join_condition"),
			add(localExpression(joinSource), number(0.5)),
			add(localExpression(joinSource), number(1.5))
		),
		number(1)
	)),
})

local joinType: any = nil
local joinReturnType: any = nil
local joinAddCount = 0
local joinPureAddCount = 0
for _, block in joinProgram.blocks do
	if block.name_hint == "if_value_join" then
		assert(#block.parameters == 1, "transitive control join changed parameter arity")
		joinType = joinProgram.values[block.parameters[1] + 1].type
	end
	if block.terminator.return_values ~= nil then
		assert(#block.terminator.return_values == 1, "transitive control join changed result arity")
		joinReturnType = joinProgram.values[block.terminator.return_values[1] + 1].type
	end
end
for _, instruction in joinProgram.instructions do
	if instruction.operation.binary ~= nil and instruction.operation.binary.operator == "add" then
		joinAddCount += 1
		joinPureAddCount += if hasExactPureEffects(instruction.effects) then 1 else 0
	end
end
assert(
	joinType ~= nil
		and joinType.kind == "number"
		and joinReturnType ~= nil
		and joinReturnType.kind == "number"
		and joinAddCount == 3
		and joinPureAddCount == 3,
	"transitive block-parameter/operator domains did not converge"
)

local capturedSource = localIdentity("captured_source")
local capturedMiddle = localIdentity("captured_middle")
local capturedLeaf = localIdentity("captured_leaf")
local capturedProgram = lift("frontend-captured-alias-domain", {
	declare(capturedSource, number(1)),
	declare(capturedMiddle, closure({
		declare(capturedLeaf, closure({
			assign(capturedSource, number(2)),
			returnValue(add(localExpression(capturedSource), number(0.5))),
		})),
		returnValue(localExpression(capturedLeaf)),
	})),
	returnValue(localExpression(capturedMiddle)),
})

local capturedPlaceCount = 0
local capturedReadCount = 0
local capturedAdd: any = nil
for _, place in capturedProgram.places do
	if place.name_hint == "captured_source" then
		capturedPlaceCount += 1
		assert(place.type.kind == "integer", "captured alias place did not gain its shared concrete domain")
	end
end
for _, instruction in capturedProgram.instructions do
	if instruction.operation.place_read ~= nil
		and capturedProgram.places[instruction.operation.place_read + 1].name_hint == "captured_source"
	then
		capturedReadCount += 1
		assert(
			capturedProgram.values[instruction.results[1] + 1].type.kind == "integer",
			"captured alias read did not gain its shared concrete domain"
		)
	elseif instruction.operation.binary ~= nil and instruction.operation.binary.operator == "add" then
		capturedAdd = instruction
	end
end
assert(capturedPlaceCount == 3, "captured alias test did not traverse all lexical owners")
assert(capturedReadCount == 1, "captured alias test changed its read shape")
assert(
	capturedAdd ~= nil
		and capturedProgram.values[capturedAdd.results[1] + 1].type.kind == "number"
		and hasExactPureEffects(capturedAdd.effects),
	"captured alias domain did not update its downstream operator"
)

local cyclicSource = localIdentity("cyclic_source")
local cyclicProgram = lift("frontend-cyclic-place-domain", {
	declare(cyclicSource, number(0)),
	assign(cyclicSource, add(localExpression(cyclicSource), number(1))),
	returnValue(add(localExpression(cyclicSource), number(0.5))),
})

local cyclicAddCount = 0
local cyclicPureAddCount = 0
for _, instruction in cyclicProgram.instructions do
	if instruction.operation.binary ~= nil and instruction.operation.binary.operator == "add" then
		cyclicAddCount += 1
		cyclicPureAddCount += if hasExactPureEffects(instruction.effects) then 1 else 0
	end
end
assert(
	cyclicProgram.places[1].type.kind == "number" and cyclicAddCount == 2 and cyclicPureAddCount == 2,
	"grounded cyclic place domain did not converge through numeric widening"
)

local cyclicCapturedSource = localIdentity("cyclic_captured_source")
local cyclicCapturedWriter = localIdentity("cyclic_captured_writer")
local cyclicCapturedProgram = lift("frontend-cyclic-captured-domain", {
	declare(cyclicCapturedSource, number(0)),
	declare(cyclicCapturedWriter, closure({
		assign(cyclicCapturedSource, add(localExpression(cyclicCapturedSource), number(1))),
		returnValue(localExpression(cyclicCapturedSource)),
	})),
	returnValue(localExpression(cyclicCapturedWriter)),
})

local cyclicCapturedPlaceCount = 0
local cyclicCapturedPureAdd = false
for _, place in cyclicCapturedProgram.places do
	if place.name_hint == "cyclic_captured_source" then
		cyclicCapturedPlaceCount += 1
		assert(place.type.kind == "number", "grounded captured cycle lost its numeric storage domain")
	end
end
for _, instruction in cyclicCapturedProgram.instructions do
	if instruction.operation.binary ~= nil and instruction.operation.binary.operator == "add" then
		cyclicCapturedPureAdd = hasExactPureEffects(instruction.effects)
	end
end
assert(
	cyclicCapturedPlaceCount == 2 and cyclicCapturedPureAdd,
	"grounded captured cycle did not refine its complete alias class"
)

local dependentCapturedSource = localIdentity("dependent_captured_source")
local dependentCapturedWriter = localIdentity("dependent_captured_writer")
local dependentCapturedProgram = lift("frontend-dependent-captured-domain", {
	declare(dependentCapturedSource, number(0)),
	declare(dependentCapturedWriter, closure({
		assign(dependentCapturedSource, add(localExpression(dependentCapturedSource), global("dynamic_delta"))),
		returnValue(localExpression(dependentCapturedSource)),
	})),
	returnValue(localExpression(dependentCapturedWriter)),
})

local dependentCapturedPlaceCount = 0
local dependentCapturedAdd: any = nil
for _, place in dependentCapturedProgram.places do
	if place.name_hint == "dependent_captured_source" then
		dependentCapturedPlaceCount += 1
		assert(place.type.kind == "dynamic", "external dynamic dependency gained a provisional captured domain")
	end
end
for _, instruction in dependentCapturedProgram.instructions do
	if instruction.operation.binary ~= nil and instruction.operation.binary.operator == "add" then
		dependentCapturedAdd = instruction
	end
end
assert(
	dependentCapturedPlaceCount == 2
		and dependentCapturedAdd ~= nil
		and dependentCapturedProgram.values[dependentCapturedAdd.results[1] + 1].type.kind == "dynamic"
		and not hasExactPureEffects(dependentCapturedAdd.effects),
	"external dynamic dependency escaped the same-alias-class proof boundary"
)

local mixedCapturedSource = localIdentity("mixed_captured_source")
local mixedCapturedWriter = localIdentity("mixed_captured_writer")
local mixedCapturedProgram = lift("frontend-mixed-captured-alias-domain", {
	declare(mixedCapturedSource, number(1)),
	declare(mixedCapturedWriter, closure({
		assign(mixedCapturedSource, stringValue("changed")),
		returnValue(localExpression(mixedCapturedSource)),
	})),
	returnValue(localExpression(mixedCapturedWriter)),
})

local mixedCapturedPlaceCount = 0
for _, place in mixedCapturedProgram.places do
	if place.name_hint == "mixed_captured_source" then
		mixedCapturedPlaceCount += 1
		assert(place.type.kind == "dynamic", "mixed captured alias class gained a false concrete domain")
	end
end
assert(mixedCapturedPlaceCount == 2, "mixed captured alias test did not cover both lexical owners")

return true
