--!strict

local Support = require("./temporal_test_support")

local assignment = Support.assignment
local assignmentValue = Support.assignmentValue
local block = Support.block
local branchStatement = Support.branchStatement
local callExpression = Support.callExpression
local callStatement = Support.callStatement
local declaration = Support.declaration
local document = Support.document
local expectFailure = Support.expectFailure
local localExpression = Support.localExpression
local localStatement = Support.localStatement
local verifyOrigin = Support.verifyOrigin
local whileStatement = Support.whileStatement

local futureLoopTarget = declaration("futureLoopTarget", "future-loop-target")
local futureLoopCall = callExpression(futureLoopTarget, "future-loop-call")
local futureLoopProof = verifyOrigin(
	document({
		localStatement(futureLoopTarget, "future-loop-declaration"),
		assignment(futureLoopTarget, "future-loop-current-write"),
		callStatement(futureLoopCall, "future-loop-call-statement"),
		whileStatement("future-loop", {
			assignmentValue(futureLoopTarget, "future-loop-later-write", {
				type = "AstExprGlobal",
				location = "future-loop-later-value",
				global = "different_target",
			}),
		}),
	}),
	futureLoopCall,
	futureLoopTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(futureLoopProof.definition_location == "future-loop-current-write", "later loop write blocked an earlier direct use")

local futureAliasStable = declaration("futureAliasStable", "future-alias-stable")
local futureAliasPlace = declaration("futureAliasPlace", "future-alias-place")
local futureAliasTarget = declaration("futureAliasTarget", "future-alias-target")
local futureAliasCall = callExpression(futureAliasTarget, "future-alias-call")
local futureAliasProof = verifyOrigin(
	document({
		localStatement(futureAliasStable, "future-alias-stable-declaration", {
			type = "AstExprGlobal",
			location = "future-alias-stable-value",
			global = "authenticated_target",
		}),
		localStatement(futureAliasPlace, "future-alias-place-declaration"),
		branchStatement(
			"future-alias-current",
			{ assignmentValue(futureAliasPlace, "future-alias-then-write", localExpression(futureAliasStable, "future-alias-then-value")) },
			block({
				assignmentValue(futureAliasPlace, "future-alias-else-write", localExpression(futureAliasStable, "future-alias-else-value")),
			}, "future-alias-else")
		),
		localStatement(futureAliasTarget, "future-alias-target-declaration", localExpression(futureAliasPlace, "future-alias-target-value")),
		callStatement(futureAliasCall, "future-alias-call-statement"),
		whileStatement("future-alias-loop", { assignment(futureAliasPlace, "future-alias-later-write") }),
	}),
	futureAliasCall,
	futureAliasTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(futureAliasProof.alias_depth == 2, "later loop write blocked an earlier alias snapshot")

local sameLoopTarget = declaration("sameLoopTarget", "same-loop-target")
local sameLoopCall = callExpression(sameLoopTarget, "same-loop-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(sameLoopTarget, "same-loop-declaration"),
			whileStatement("same-loop", {
				callStatement(sameLoopCall, "same-loop-call-statement"),
				assignment(sameLoopTarget, "same-loop-write"),
			}),
		}),
		sameLoopCall,
		sameLoopTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
	end, "has an unauthenticated feasible definition")

local nestedLoopTarget = declaration("nestedLoopTarget", "nested-loop-target")
local nestedLoopCall = callExpression(nestedLoopTarget, "nested-loop-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(nestedLoopTarget, "nested-loop-declaration"),
			assignment(nestedLoopTarget, "nested-loop-current-write"),
			whileStatement("nested-loop-outer", {
				callStatement(nestedLoopCall, "nested-loop-call-statement"),
				whileStatement("nested-loop-inner", { assignment(nestedLoopTarget, "nested-loop-write") }),
			}),
		}),
		nestedLoopCall,
		nestedLoopTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
	end, "depends on a repeated dynamic evaluation")

local capturedLoopTarget = declaration("capturedLoopTarget", "captured-loop-target")
local capturedLoopCall = callExpression(capturedLoopTarget, "captured-loop-call")
local capturedLoopFunction = {
	type = "AstExprFunction",
	location = "captured-loop-function",
	args = {},
	body = block({ callStatement(capturedLoopCall, "captured-loop-call-statement") }, "captured-loop-function-body"),
}
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(capturedLoopTarget, "captured-loop-declaration"),
			assignment(capturedLoopTarget, "captured-loop-current-write"),
			localStatement(declaration("capturedLoopHolder", "captured-loop-holder"), "captured-loop-closure", capturedLoopFunction),
			whileStatement("captured-loop-later", { assignment(capturedLoopTarget, "captured-loop-later-write") }),
		}),
		capturedLoopCall,
		capturedLoopTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has a write after or inside its closure snapshot")
