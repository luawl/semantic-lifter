--!strict

local Support = require("./temporal_test_support")
local InvocationSupport = require("./temporal_invocation_test_support")

type Record = Support.Record

local assignmentValue = Support.assignmentValue
local callExpression = Support.callExpression
local callStatement = Support.callStatement
local declaration = Support.declaration
local differentTarget = InvocationSupport.differentTarget
local document = Support.document
local expectFailure = Support.expectFailure
local globalExpression = Support.globalExpression
local invocationFromBody = Support.invocationFromBody
local localExpression = Support.localExpression
local localStatement = Support.localStatement
local verifyOrigin = Support.verifyOrigin

local function returnStatement(value: Record, prefix: string): Record
	return { type = "AstStatReturn", location = prefix .. "-return", list = { value } }
end

local function closureValue(prefix: string): Record
	local value, _ = invocationFromBody({
		returnStatement(globalExpression("result", prefix .. "-result"), prefix),
	}, prefix, nil, nil)
	return value
end

local function localFunctionFactory(prefix: string): (Record, Record, Record, Record)
	local target = declaration(prefix .. "LocalFunction", prefix .. "-local-function")
	local allocation = closureValue(prefix .. "-allocation")
	local statement: Record = {
		type = "AstStatLocalFunction",
		location = prefix .. "-local-function-statement",
		name = target,
		func = allocation,
	}
	local outer, call = invocationFromBody({
		statement,
		returnStatement(localExpression(target, prefix .. "-returned-read"), prefix),
	}, prefix .. "-factory", nil, nil)
	return call, allocation, statement, outer
end

local function targetDocument(prefix: string, value: Record): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-target-read")
	return document({
		localStatement(target, prefix .. "-target-declaration"),
		assignmentValue(target, prefix .. "-current", value),
		callStatement(call, prefix .. "-call-statement"),
		assignmentValue(target, prefix .. "-future", differentTarget(prefix .. "-future-value")),
	}), call, target
end

local function closureOrigin(allocation: Record): Record
	return { kind = "closure_value", expression = allocation }
end

local function expectProof(prefix: string, value: Record, allocation: Record)
	local fixture, call, target = targetDocument(prefix, value)
	local proof = verifyOrigin(fixture, call, target, closureOrigin(allocation))
	assert(proof.definition_count == 1, `{prefix} local function produced a definition set`)
	assert(proof.definition_location == prefix .. "-current", `{prefix} lost the factory-result write`)
end

local function expectRejection(prefix: string, value: Record, allocation: Record)
	local fixture, call, target = targetDocument(prefix, value)
	expectFailure(function()
		verifyOrigin(fixture, call, target, closureOrigin(allocation))
	end, "temporal target definition " .. target.location)
end

local directCall, directAllocation = localFunctionFactory("local-function-return")
expectProof("local-function-return", directCall, directAllocation)

local aliasCall, aliasAllocation, aliasStatement, aliasOuter = localFunctionFactory("local-function-return-alias")
local alias = declaration("localFunctionReturnAlias", "local-function-return-alias-local")
table.insert(aliasOuter.body.body, 2, localStatement(
	alias,
	"local-function-return-alias-statement",
	localExpression(aliasStatement.name, "local-function-return-alias-value")
))
aliasOuter.body.body[3].list = { localExpression(alias, "local-function-return-alias-read") }
expectProof("local-function-return-alias", aliasCall, aliasAllocation)

expectRejection(
	"local-function-return-wrong-allocation",
	directCall,
	closureValue("local-function-return-wrong-allocation")
)

local reassignedCall, reassignedAllocation, reassignedStatement, reassignedOuter =
	localFunctionFactory("local-function-return-reassigned")
table.insert(reassignedOuter.body.body, 2, assignmentValue(
	reassignedStatement.name,
	"local-function-return-reassigned-write",
	differentTarget("local-function-return-reassigned-value")
))
expectRejection("local-function-return-reassigned", reassignedCall, reassignedAllocation)

local malformedCall, malformedAllocation, malformedStatement = localFunctionFactory("local-function-return-malformed")
malformedStatement.func = differentTarget("local-function-return-malformed-value")
expectRejection("local-function-return-malformed", malformedCall, malformedAllocation)

return true
