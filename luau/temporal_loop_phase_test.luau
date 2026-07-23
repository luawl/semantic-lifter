--!strict

local Support = require("./temporal_test_support")

type Record = Support.Record

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

local function globalExpression(name: string, location: string): Record
	return { type = "AstExprGlobal", location = location, global = name }
end

local function transfer(kind: string, prefix: string): Record
	local statement: Record = { type = kind, location = prefix .. "-transfer" }
	if kind == "AstStatReturn" then
		statement.list = {}
	end
	return statement
end

local function repeatStatement(prefix: string, body: { Record }, condition: Record): Record
	return {
		type = "AstStatRepeat",
		location = prefix .. "-repeat",
		body = block(body, prefix .. "-body"),
		condition = condition,
	}
end

local conditionStable = declaration("conditionStable", "loop-phase-condition-stable")
local conditionTarget = declaration("conditionTarget", "loop-phase-condition-target")
local conditionCall = callExpression(conditionTarget, "loop-phase-condition-call")
local conditionProof = verifyOrigin(
	document({
		localStatement(
			conditionStable,
			"loop-phase-condition-stable-declaration",
			globalExpression("authenticated_target", "loop-phase-condition-stable-value")
		),
		localStatement(
			conditionTarget,
			"loop-phase-condition-target-declaration",
			localExpression(conditionStable, "loop-phase-condition-incoming")
		),
		{
			type = "AstStatWhile",
			location = "loop-phase-condition-while",
			condition = conditionCall,
			body = block({
				assignmentValue(
					conditionTarget,
					"loop-phase-condition-write",
					localExpression(conditionStable, "loop-phase-condition-write-value")
				),
			}, "loop-phase-condition-body"),
		},
	}),
	conditionCall,
	conditionTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(conditionProof.alias_depth == 1 and conditionProof.definition_count == 2, "while condition lost a first or later evaluation")

local beforeStable = declaration("beforeStable", "loop-phase-before-stable")
local beforeTarget = declaration("beforeTarget", "loop-phase-before-target")
local beforeCall = callExpression(beforeTarget, "loop-phase-before-call")
local beforeProof = verifyOrigin(
	document({
		localStatement(
			beforeStable,
			"loop-phase-before-stable-declaration",
			globalExpression("authenticated_target", "loop-phase-before-stable-value")
		),
		localStatement(beforeTarget, "loop-phase-before-target-declaration", localExpression(beforeStable, "loop-phase-before-incoming")),
		whileStatement("loop-phase-before", {
			callStatement(beforeCall, "loop-phase-before-call-statement"),
			assignmentValue(beforeTarget, "loop-phase-before-write", localExpression(beforeStable, "loop-phase-before-write-value")),
		}),
	}),
	beforeCall,
	beforeTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(beforeProof.alias_depth == 1 and beforeProof.definition_count == 2, "body entry lost a prior iteration")

local afterStable = declaration("afterStable", "loop-phase-after-stable")
local afterTarget = declaration("afterTarget", "loop-phase-after-target")
local afterCall = callExpression(afterTarget, "loop-phase-after-call")
local afterProof = verifyOrigin(
	document({
		localStatement(afterStable, "loop-phase-after-stable-declaration", globalExpression("authenticated_target", "loop-phase-after-stable-value")),
		localStatement(afterTarget, "loop-phase-after-target-declaration", localExpression(afterStable, "loop-phase-after-incoming")),
		whileStatement("loop-phase-after", {
			assignmentValue(afterTarget, "loop-phase-after-write", localExpression(afterStable, "loop-phase-after-write-value")),
			callStatement(afterCall, "loop-phase-after-call-statement"),
		}),
	}),
	afterCall,
	afterTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(afterProof.alias_depth == 1 and afterProof.definition_count == 1, "body prefix did not commit its current write")

local sameStatementTarget = declaration("sameStatementTarget", "loop-phase-same-statement-target")
local sameStatementResult = declaration("sameStatementResult", "loop-phase-same-statement-result")
local sameStatementCall = callExpression(sameStatementTarget, "loop-phase-same-statement-call")
local sameStatementWrite: Record = {
	type = "AstStatAssign",
	location = "loop-phase-same-statement-write",
	vars = {
		localExpression(sameStatementTarget, "loop-phase-same-statement-target-write"),
		localExpression(sameStatementResult, "loop-phase-same-statement-result-write"),
	},
	values = {
		globalExpression("different_target", "loop-phase-same-statement-value"),
		sameStatementCall,
	},
}
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(
				sameStatementTarget,
				"loop-phase-same-statement-target-declaration",
				globalExpression("authenticated_target", "loop-phase-same-statement-incoming")
			),
			localStatement(sameStatementResult, "loop-phase-same-statement-result-declaration"),
			whileStatement("loop-phase-same-statement", { sameStatementWrite }),
		}),
		sameStatementCall,
		sameStatementTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has an unauthenticated feasible definition")

local guardTarget = declaration("phaseGuardTarget", "loop-phase-guard-target")
local guardCall = callExpression(guardTarget, "loop-phase-guard-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(
				guardTarget,
				"loop-phase-guard-target-declaration",
				globalExpression("authenticated_target", "loop-phase-guard-incoming")
			),
			whileStatement("loop-phase-guard", {
				{
					type = "AstStatIf",
					location = "loop-phase-guard-if",
					condition = guardCall,
					thenbody = block({
						assignmentValue(
							guardTarget,
							"loop-phase-guard-write",
							globalExpression("different_target", "loop-phase-guard-write-value")
						),
					}, "loop-phase-guard-then"),
					elsebody = nil,
				},
			}),
		}),
		guardCall,
		guardTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has an unauthenticated feasible definition")

local repeatStable = declaration("phaseRepeatStable", "loop-phase-repeat-stable")
local repeatTarget = declaration("phaseRepeatTarget", "loop-phase-repeat-target")
local repeatCall = callExpression(repeatTarget, "loop-phase-repeat-call")
local repeatProof = verifyOrigin(
	document({
		localStatement(repeatStable, "loop-phase-repeat-stable-declaration", globalExpression("authenticated_target", "loop-phase-repeat-stable-value")),
		localStatement(repeatTarget, "loop-phase-repeat-target-declaration"),
		repeatStatement("loop-phase-repeat", {
			assignmentValue(repeatTarget, "loop-phase-repeat-write", localExpression(repeatStable, "loop-phase-repeat-write-value")),
		}, repeatCall),
	}),
	repeatCall,
	repeatTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(repeatProof.alias_depth == 1 and repeatProof.definition_count == 1, "repeat condition observed its pre-body state")

local continueTarget = declaration("phaseContinueTarget", "loop-phase-continue-target")
local continueCall = callExpression(continueTarget, "loop-phase-continue-call")
local continueProof = verifyOrigin(
	document({
		localStatement(
			continueTarget,
			"loop-phase-continue-target-declaration",
			globalExpression("authenticated_target", "loop-phase-continue-incoming")
		),
		repeatStatement("loop-phase-continue", {
			transfer("AstStatContinue", "loop-phase-continue"),
			assignmentValue(
				continueTarget,
				"loop-phase-continue-unreachable-write",
				globalExpression("different_target", "loop-phase-continue-unreachable-value")
			),
		}, continueCall),
	}),
	continueCall,
	continueTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(continueProof.definition_count == 1, "repeat continue did not flow directly to its condition")

local branchStable = declaration("phaseBranchStable", "loop-phase-branch-stable")
local branchTarget = declaration("phaseBranchTarget", "loop-phase-branch-target")
local branchCall = callExpression(branchTarget, "loop-phase-branch-call")
local branchProof = verifyOrigin(
	document({
		localStatement(branchStable, "loop-phase-branch-stable-declaration", globalExpression("authenticated_target", "loop-phase-branch-stable-value")),
		localStatement(branchTarget, "loop-phase-branch-target-declaration"),
		repeatStatement("loop-phase-branch", {
			branchStatement(
				"loop-phase-branch-choice",
				{
					assignmentValue(
						branchTarget,
						"loop-phase-branch-break-write",
						globalExpression("different_target", "loop-phase-branch-break-value")
					),
					transfer("AstStatBreak", "loop-phase-branch-break"),
				},
				block({
					assignmentValue(
						branchTarget,
						"loop-phase-branch-normal-write",
						localExpression(branchStable, "loop-phase-branch-normal-value")
					),
				}, "loop-phase-branch-else")
			),
		}, branchCall),
	}),
	branchCall,
	branchTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(branchProof.alias_depth == 1 and branchProof.definition_count == 1, "break state leaked into the repeat condition")

local transferKinds: { string } = { "AstStatBreak", "AstStatContinue", "AstStatReturn" }
for _, kind in transferKinds do
	local prefix = "loop-phase-unreachable-" .. kind
	local target = declaration("unreachableTarget", prefix .. "-target")
	local call = callExpression(target, prefix .. "-call")
	expectFailure(function()
		verifyOrigin(
			document({
				localStatement(target, prefix .. "-target-declaration", globalExpression("authenticated_target", prefix .. "-incoming")),
				whileStatement(prefix, {
					transfer(kind, prefix),
					callStatement(call, prefix .. "-call-statement"),
					assignmentValue(
						target,
						prefix .. "-unreachable-write",
						globalExpression("different_target", prefix .. "-unreachable-value")
					),
				}),
			}),
			call,
			target,
			{ kind = "environment", name = "authenticated_target" }
		)
	end, "has no feasible structured definition set")
end

local nestedTarget = declaration("phaseNestedTarget", "loop-phase-nested-target")
local nestedCall = callExpression(nestedTarget, "loop-phase-nested-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(
				nestedTarget,
				"loop-phase-nested-target-declaration",
				globalExpression("authenticated_target", "loop-phase-nested-incoming")
			),
			whileStatement("loop-phase-nested-outer", {
				whileStatement("loop-phase-nested-inner", { callStatement(nestedCall, "loop-phase-nested-call-statement") }),
				assignmentValue(
					nestedTarget,
					"loop-phase-nested-outer-write",
					globalExpression("different_target", "loop-phase-nested-outer-value")
				),
			}),
		}),
		nestedCall,
		nestedTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has an unauthenticated feasible definition")

local capturedTarget = declaration("phaseCapturedTarget", "loop-phase-captured-target")
local capturedCall = callExpression(capturedTarget, "loop-phase-captured-call")
local capturedHolder = declaration("phaseCapturedHolder", "loop-phase-captured-holder")
local capturedFunction: Record = {
	type = "AstExprFunction",
	location = "loop-phase-captured-function",
	args = {},
	body = block({ callStatement(capturedCall, "loop-phase-captured-call-statement") }, "loop-phase-captured-function-body"),
}
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(
				capturedTarget,
				"loop-phase-captured-target-declaration",
				globalExpression("authenticated_target", "loop-phase-captured-incoming")
			),
			whileStatement("loop-phase-captured", {
				localStatement(capturedHolder, "loop-phase-captured-holder-declaration", capturedFunction),
				assignmentValue(
					capturedTarget,
					"loop-phase-captured-write",
					globalExpression("different_target", "loop-phase-captured-value")
				),
			}),
		}),
		capturedCall,
		capturedTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has an unauthenticated feasible definition")
