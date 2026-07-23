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

local function repeatStatement(prefix: string, body: { Record }): Record
	return {
		type = "AstStatRepeat",
		location = prefix .. "-repeat",
		body = block(body, prefix .. "-body"),
		condition = { type = "AstExprConstantBool", location = prefix .. "-condition", value = true },
	}
end

local function numericForStatement(prefix: string, body: { Record }): Record
	return {
		type = "AstStatFor",
		location = prefix .. "-for",
		var = declaration(prefix .. "Index", prefix .. "-index"),
		from = globalExpression("start", prefix .. "-start"),
		to = globalExpression("limit", prefix .. "-limit"),
		step = nil,
		body = block(body, prefix .. "-body"),
	}
end

local function genericForStatement(prefix: string, body: { Record }): Record
	return {
		type = "AstStatForIn",
		location = prefix .. "-for",
		vars = { declaration(prefix .. "Value", prefix .. "-value") },
		values = { globalExpression("iterator", prefix .. "-iterator") },
		body = block(body, prefix .. "-body"),
	}
end

type LoopFactory = (string, { Record }) -> Record

local function verifyZeroOrMoreLoop(prefix: string, makeLoop: LoopFactory)
	local stable = declaration(prefix .. "Stable", prefix .. "-stable")
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-call")
	local proof = verifyOrigin(
		document({
			localStatement(stable, prefix .. "-stable-declaration", globalExpression("authenticated_target", prefix .. "-stable-value")),
			localStatement(target, prefix .. "-target-declaration", localExpression(stable, prefix .. "-incoming")),
			makeLoop(prefix, {
				assignmentValue(target, prefix .. "-write", localExpression(stable, prefix .. "-write-value")),
			}),
			callStatement(call, prefix .. "-call-statement"),
		}),
		call,
		target,
		{ kind = "environment", name = "authenticated_target" }
	)
	assert(proof.alias_depth == 1 and proof.definition_count == 2, prefix .. " lost its zero-or-more fixed point")
end

local repeatStable = declaration("repeatStable", "loop-fixed-repeat-stable")
local repeatTarget = declaration("repeatTarget", "loop-fixed-repeat-target")
local repeatCall = callExpression(repeatTarget, "loop-fixed-repeat-call")
local repeatProof = verifyOrigin(
	document({
		localStatement(
			repeatStable,
			"loop-fixed-repeat-stable-declaration",
			globalExpression("authenticated_target", "loop-fixed-repeat-stable-value")
		),
		localStatement(repeatTarget, "loop-fixed-repeat-target-declaration"),
		repeatStatement("loop-fixed-repeat", {
			assignmentValue(
				repeatTarget,
				"loop-fixed-repeat-write",
				localExpression(repeatStable, "loop-fixed-repeat-write-value")
			),
		}),
		callStatement(repeatCall, "loop-fixed-repeat-call-statement"),
	}),
	repeatCall,
	repeatTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(repeatProof.alias_depth == 1 and repeatProof.definition_count == 1, "repeat fixed point lost its stable alias")

local whileStable = declaration("whileStable", "loop-fixed-while-stable")
local whileTarget = declaration("whileTarget", "loop-fixed-while-target")
local whileCall = callExpression(whileTarget, "loop-fixed-while-call")
local whileProof = verifyOrigin(
	document({
		localStatement(
			whileStable,
			"loop-fixed-while-stable-declaration",
			globalExpression("authenticated_target", "loop-fixed-while-stable-value")
		),
		localStatement(whileTarget, "loop-fixed-while-target-declaration", localExpression(whileStable, "loop-fixed-while-incoming")),
		whileStatement("loop-fixed-while", {
			assignmentValue(whileTarget, "loop-fixed-while-write", localExpression(whileStable, "loop-fixed-while-write-value")),
		}),
		callStatement(whileCall, "loop-fixed-while-call-statement"),
	}),
	whileCall,
	whileTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(whileProof.alias_depth == 1 and whileProof.definition_count == 2, "zero-or-more loop lost its convergent candidates")

verifyZeroOrMoreLoop("loop-fixed-numeric", numericForStatement)
verifyZeroOrMoreLoop("loop-fixed-generic", genericForStatement)

local branchStable = declaration("branchStable", "loop-fixed-branch-stable")
local branchTarget = declaration("branchTarget", "loop-fixed-branch-target")
local branchCall = callExpression(branchTarget, "loop-fixed-branch-call")
local branchProof = verifyOrigin(
	document({
		localStatement(
			branchStable,
			"loop-fixed-branch-stable-declaration",
			globalExpression("authenticated_target", "loop-fixed-branch-stable-value")
		),
		localStatement(branchTarget, "loop-fixed-branch-target-declaration", localExpression(branchStable, "loop-fixed-branch-incoming")),
		whileStatement("loop-fixed-branch", {
			branchStatement(
				"loop-fixed-branch-choice",
				{
					assignmentValue(
						branchTarget,
						"loop-fixed-branch-then-write",
						localExpression(branchStable, "loop-fixed-branch-then-value")
					),
				},
				block({
					assignmentValue(
						branchTarget,
						"loop-fixed-branch-else-write",
						localExpression(branchStable, "loop-fixed-branch-else-value")
					),
				}, "loop-fixed-branch-else")
			),
		}),
		callStatement(branchCall, "loop-fixed-branch-call-statement"),
	}),
	branchCall,
	branchTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(branchProof.definition_count == 3, "branch loop fixed point lost a feasible identity-preserving path")

local dynamicTarget = declaration("dynamicTarget", "loop-fixed-dynamic-target")
local dynamicCall = callExpression(dynamicTarget, "loop-fixed-dynamic-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(dynamicTarget, "loop-fixed-dynamic-declaration"),
			repeatStatement("loop-fixed-dynamic", {
				assignmentValue(
					dynamicTarget,
					"loop-fixed-dynamic-write",
					globalExpression("authenticated_target", "loop-fixed-dynamic-value")
				),
			}),
			callStatement(dynamicCall, "loop-fixed-dynamic-call-statement"),
		}),
		dynamicCall,
		dynamicTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "depends on a repeated dynamic evaluation")

local divergentStable = declaration("divergentStable", "loop-fixed-divergent-stable")
local divergentOther = declaration("divergentOther", "loop-fixed-divergent-other")
local divergentTarget = declaration("divergentTarget", "loop-fixed-divergent-target")
local divergentCall = callExpression(divergentTarget, "loop-fixed-divergent-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(
				divergentStable,
				"loop-fixed-divergent-stable-declaration",
				globalExpression("authenticated_target", "loop-fixed-divergent-stable-value")
			),
			localStatement(
				divergentOther,
				"loop-fixed-divergent-other-declaration",
				globalExpression("different_target", "loop-fixed-divergent-other-value")
			),
			localStatement(
				divergentTarget,
				"loop-fixed-divergent-target-declaration",
				localExpression(divergentStable, "loop-fixed-divergent-incoming")
			),
			whileStatement("loop-fixed-divergent", {
				assignmentValue(
					divergentTarget,
					"loop-fixed-divergent-write",
					localExpression(divergentOther, "loop-fixed-divergent-write-value")
				),
			}),
			callStatement(divergentCall, "loop-fixed-divergent-call-statement"),
		}),
		divergentCall,
		divergentTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "unauthenticated feasible definition")
