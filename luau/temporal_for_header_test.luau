--!strict

local Support = require("./temporal_test_support")

type Record = Support.Record

local assignment = Support.assignment
local assignmentValue = Support.assignmentValue
local block = Support.block
local callExpression = Support.callExpression
local callStatement = Support.callStatement
local declaration = Support.declaration
local document = Support.document
local expectFailure = Support.expectFailure
local localExpression = Support.localExpression
local localStatement = Support.localStatement
local verifyOrigin = Support.verifyOrigin

local function constantNumber(value: number, location: string): Record
	return { type = "AstExprConstantNumber", location = location, value = value }
end

local function differentTarget(location: string): Record
	return { type = "AstExprGlobal", location = location, global = "different_target" }
end

local function numericFor(prefix: string, initial: Record, body: { Record }): Record
	return {
		type = "AstStatFor",
		location = prefix .. "-for",
		var = declaration(prefix .. "Index", prefix .. "-index"),
		from = initial,
		to = constantNumber(1, prefix .. "-limit"),
		step = nil,
		body = block(body, prefix .. "-body"),
	}
end

local function genericFor(prefix: string, iterator: Record, body: { Record }): Record
	return {
		type = "AstStatForIn",
		location = prefix .. "-for",
		vars = { declaration(prefix .. "Value", prefix .. "-value") },
		values = { iterator },
		body = block(body, prefix .. "-body"),
	}
end

local numericTarget = declaration("numericTarget", "for-header-numeric-target")
local numericCall = callExpression(numericTarget, "for-header-numeric-call")
local numericProof = verifyOrigin(
	document({
		localStatement(numericTarget, "for-header-numeric-declaration"),
		assignment(numericTarget, "for-header-numeric-current"),
		numericFor("for-header-numeric", numericCall, {
			assignmentValue(
				numericTarget,
				"for-header-numeric-body-write",
				differentTarget("for-header-numeric-body-value")
			),
		}),
	}),
	numericCall,
	numericTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(numericProof.definition_location == "for-header-numeric-current", "numeric for header observed a body write")

local genericTarget = declaration("genericTarget", "for-header-generic-target")
local genericCall = callExpression(genericTarget, "for-header-generic-call")
local genericProof = verifyOrigin(
	document({
		localStatement(genericTarget, "for-header-generic-declaration"),
		assignment(genericTarget, "for-header-generic-current"),
		genericFor("for-header-generic", genericCall, {
			assignmentValue(
				genericTarget,
				"for-header-generic-body-write",
				differentTarget("for-header-generic-body-value")
			),
		}),
	}),
	genericCall,
	genericTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(genericProof.definition_location == "for-header-generic-current", "generic for header observed a body write")

local aliasStable = declaration("forHeaderStable", "for-header-alias-stable")
local aliasTarget = declaration("forHeaderAlias", "for-header-alias-target")
local aliasCall = callExpression(aliasTarget, "for-header-alias-call")
local aliasProof = verifyOrigin(
	document({
		localStatement(aliasStable, "for-header-alias-stable-declaration", {
			type = "AstExprGlobal",
			location = "for-header-alias-stable-value",
			global = "authenticated_target",
		}),
		localStatement(aliasTarget, "for-header-alias-target-declaration", localExpression(aliasStable, "for-header-alias-value")),
		numericFor("for-header-alias", aliasCall, {
			assignmentValue(aliasTarget, "for-header-alias-body-write", differentTarget("for-header-alias-body-value")),
		}),
	}),
	aliasCall,
	aliasTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(aliasProof.alias_depth == 1, "for header lost the incoming alias identity")

local whileTarget = declaration("whileTarget", "for-header-while-target")
local whileCall = callExpression(whileTarget, "for-header-while-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(whileTarget, "for-header-while-declaration"),
			assignment(whileTarget, "for-header-while-current"),
			{
				type = "AstStatWhile",
				location = "for-header-while",
				condition = whileCall,
				body = block({
					assignmentValue(
						whileTarget,
						"for-header-while-body-write",
						differentTarget("for-header-while-body-value")
					),
				}, "for-header-while-body"),
			},
		}),
		whileCall,
		whileTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
	end, "has an unauthenticated feasible definition")

local bodyTarget = declaration("bodyTarget", "for-header-body-target")
local bodyCall = callExpression(bodyTarget, "for-header-body-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(bodyTarget, "for-header-body-declaration"),
			assignment(bodyTarget, "for-header-body-current"),
			numericFor("for-header-body", constantNumber(1, "for-header-body-initial"), {
				callStatement(bodyCall, "for-header-body-call-statement"),
				assignmentValue(bodyTarget, "for-header-body-write", differentTarget("for-header-body-value")),
			}),
		}),
		bodyCall,
		bodyTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
	end, "has an unauthenticated feasible definition")

local postTarget = declaration("postTarget", "for-header-post-target")
local postCall = callExpression(postTarget, "for-header-post-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(postTarget, "for-header-post-declaration"),
			assignment(postTarget, "for-header-post-current"),
			numericFor("for-header-post", constantNumber(1, "for-header-post-initial"), {
				assignmentValue(postTarget, "for-header-post-write", differentTarget("for-header-post-value")),
			}),
			callStatement(postCall, "for-header-post-call-statement"),
		}),
		postCall,
		postTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has an unauthenticated feasible definition")

local capturedTarget = declaration("headerCapturedTarget", "for-header-captured-target")
local capturedCall = callExpression(capturedTarget, "for-header-captured-call")
local capturedFunction: Record = {
	type = "AstExprFunction",
	location = "for-header-captured-function",
	args = {},
	body = block({ callStatement(capturedCall, "for-header-captured-call-statement") }, "for-header-captured-function-body"),
}
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(capturedTarget, "for-header-captured-declaration"),
			assignment(capturedTarget, "for-header-captured-current"),
			numericFor("for-header-captured", capturedFunction, {
				assignmentValue(capturedTarget, "for-header-captured-write", differentTarget("for-header-captured-value")),
			}),
		}),
		capturedCall,
		capturedTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
	end, "has a write after or inside its closure snapshot")
