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
local whileStatement = Support.whileStatement

local function globalExpression(name: string, location: string): Record
	return { type = "AstExprGlobal", location = location, global = name }
end

local function conditional(prefix: string, condition: Record, thenBody: { Record }, elseBody: Record?): Record
	return {
		type = "AstStatIf",
		location = prefix .. "-if",
		condition = condition,
		thenbody = block(thenBody, prefix .. "-then"),
		elsebody = elseBody,
	}
end

local function repeatedWrite(target: Record, prefix: string): Record
	return whileStatement(prefix, {
		assignmentValue(target, prefix .. "-write", globalExpression("different_target", prefix .. "-value")),
	})
end

local guardTarget = declaration("guardTarget", "guard-target")
local guardCall = callExpression(guardTarget, "guard-call")
local guardProof = verifyOrigin(
	document({
		localStatement(guardTarget, "guard-declaration"),
		assignment(guardTarget, "guard-current"),
		conditional("guard", guardCall, { repeatedWrite(guardTarget, "guard-loop") }, nil),
	}),
	guardCall,
	guardTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(guardProof.definition_location == "guard-current", "if guard observed a repeated branch write")

local elseifTarget = declaration("elseifTarget", "guard-elseif-target")
local elseifCall = callExpression(elseifTarget, "guard-elseif-call")
local elseifNode = conditional("guard-elseif-inner", elseifCall, { repeatedWrite(elseifTarget, "guard-elseif-inner-loop") }, nil)
local elseifProof = verifyOrigin(
	document({
		localStatement(elseifTarget, "guard-elseif-declaration"),
		assignment(elseifTarget, "guard-elseif-current"),
		conditional(
			"guard-elseif-outer",
			globalExpression("first_condition", "guard-elseif-first-condition"),
			{ repeatedWrite(elseifTarget, "guard-elseif-outer-loop") },
			elseifNode
		),
	}),
	elseifCall,
	elseifTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(elseifProof.definition_location == "guard-elseif-current", "elseif guard observed a mutually exclusive branch write")

local aliasStable = declaration("guardStable", "guard-alias-stable")
local aliasTarget = declaration("guardAlias", "guard-alias-target")
local aliasCall = callExpression(aliasTarget, "guard-alias-call")
local aliasProof = verifyOrigin(
	document({
		localStatement(aliasStable, "guard-alias-stable-declaration", globalExpression("authenticated_target", "guard-alias-stable-value")),
		localStatement(aliasTarget, "guard-alias-target-declaration", localExpression(aliasStable, "guard-alias-target-value")),
		conditional("guard-alias", aliasCall, { repeatedWrite(aliasTarget, "guard-alias-loop") }, nil),
	}),
	aliasCall,
	aliasTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(aliasProof.alias_depth == 1, "if guard lost the incoming alias identity")

local bodyTarget = declaration("guardBodyTarget", "guard-body-target")
local bodyCall = callExpression(bodyTarget, "guard-body-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(bodyTarget, "guard-body-declaration"),
			assignment(bodyTarget, "guard-body-current"),
			conditional(
				"guard-body",
				globalExpression("condition", "guard-body-condition"),
				{ repeatedWrite(bodyTarget, "guard-body-loop"), callStatement(bodyCall, "guard-body-call-statement") },
				nil
			),
		}),
		bodyCall,
		bodyTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has an unauthenticated feasible definition")

local postTarget = declaration("guardPostTarget", "guard-post-target")
local postCall = callExpression(postTarget, "guard-post-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(postTarget, "guard-post-declaration"),
			assignment(postTarget, "guard-post-current"),
			conditional(
				"guard-post",
				globalExpression("condition", "guard-post-condition"),
				{ repeatedWrite(postTarget, "guard-post-loop") },
				nil
			),
			callStatement(postCall, "guard-post-call-statement"),
		}),
		postCall,
		postTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has an unauthenticated feasible definition")

local whileTarget = declaration("guardWhileTarget", "guard-while-target")
local whileCall = callExpression(whileTarget, "guard-while-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(whileTarget, "guard-while-declaration"),
			assignment(whileTarget, "guard-while-current"),
			{
				type = "AstStatWhile",
				location = "guard-while",
				condition = whileCall,
				body = block({ assignmentValue(whileTarget, "guard-while-write", globalExpression("different_target", "guard-while-value")) }, "guard-while-body"),
			},
		}),
		whileCall,
		whileTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
	end, "has an unauthenticated feasible definition")

local capturedTarget = declaration("guardCapturedTarget", "guard-captured-target")
local capturedCall = callExpression(capturedTarget, "guard-captured-call")
local capturedFunction: Record = {
	type = "AstExprFunction",
	location = "guard-captured-function",
	args = {},
	body = block({ callStatement(capturedCall, "guard-captured-call-statement") }, "guard-captured-function-body"),
}
local consumingCondition: Record = {
	type = "AstExprCall",
	location = "guard-captured-consumer-call",
	func = globalExpression("consume", "guard-captured-consumer"),
	args = { capturedFunction },
	self = false,
}
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(capturedTarget, "guard-captured-declaration"),
			assignment(capturedTarget, "guard-captured-current"),
			conditional("guard-captured", consumingCondition, { repeatedWrite(capturedTarget, "guard-captured-loop") }, nil),
		}),
		capturedCall,
		capturedTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has a write after or inside its closure snapshot")
