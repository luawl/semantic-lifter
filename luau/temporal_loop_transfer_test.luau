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

local function transfer(kind: string, prefix: string): Record
	return { type = kind, location = prefix .. "-transfer" }
end

local function authenticatedStable(prefix: string): Record
	return globalExpression("authenticated_target", prefix .. "-stable-value")
end

for _, transferKind in { "AstStatBreak", "AstStatContinue" } do
	local prefix = "loop-transfer-after-write-" .. transferKind
	local stable = declaration("transferStable", prefix .. "-stable")
	local target = declaration("transferTarget", prefix .. "-target")
	local call = callExpression(target, prefix .. "-call")
	local proof = verifyOrigin(
		document({
			localStatement(stable, prefix .. "-stable-declaration", authenticatedStable(prefix)),
			localStatement(target, prefix .. "-target-declaration"),
			repeatStatement(prefix, {
				assignmentValue(target, prefix .. "-write", localExpression(stable, prefix .. "-write-value")),
				transfer(transferKind, prefix),
			}),
			callStatement(call, prefix .. "-call-statement"),
		}),
		call,
		target,
		{ kind = "environment", name = "authenticated_target" }
	)
	assert(proof.alias_depth == 1 and proof.definition_count == 1, prefix .. " lost its transferred definition")
end

local mixedPrefix = "loop-transfer-mixed-branch"
local mixedStable = declaration("mixedStable", mixedPrefix .. "-stable")
local mixedTarget = declaration("mixedTarget", mixedPrefix .. "-target")
local mixedCall = callExpression(mixedTarget, mixedPrefix .. "-call")
local mixedProof = verifyOrigin(
	document({
		localStatement(mixedStable, mixedPrefix .. "-stable-declaration", authenticatedStable(mixedPrefix)),
		localStatement(mixedTarget, mixedPrefix .. "-target-declaration", localExpression(mixedStable, mixedPrefix .. "-incoming")),
		whileStatement(mixedPrefix, {
			branchStatement(
				mixedPrefix .. "-choice",
				{
					assignmentValue(mixedTarget, mixedPrefix .. "-break-write", localExpression(mixedStable, mixedPrefix .. "-break-value")),
					transfer("AstStatBreak", mixedPrefix .. "-break"),
				},
				block({
					assignmentValue(mixedTarget, mixedPrefix .. "-continue-write", localExpression(mixedStable, mixedPrefix .. "-continue-value")),
					transfer("AstStatContinue", mixedPrefix .. "-continue"),
				}, mixedPrefix .. "-else")
			),
			assignmentValue(mixedTarget, mixedPrefix .. "-unreachable-write", globalExpression("different_target", mixedPrefix .. "-unreachable-value")),
		}),
		callStatement(mixedCall, mixedPrefix .. "-call-statement"),
	}),
	mixedCall,
	mixedTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(mixedProof.alias_depth == 1 and mixedProof.definition_count == 3, "mixed break/continue flow lost a feasible identity")

for _, transferKind in { "AstStatBreak", "AstStatContinue" } do
	local prefix = "loop-transfer-before-write-" .. transferKind
	local stable = declaration("beforeStable", prefix .. "-stable")
	local target = declaration("beforeTarget", prefix .. "-target")
	local call = callExpression(target, prefix .. "-call")
	local proof = verifyOrigin(
		document({
			localStatement(stable, prefix .. "-stable-declaration", authenticatedStable(prefix)),
			localStatement(target, prefix .. "-target-declaration", localExpression(stable, prefix .. "-incoming")),
			whileStatement(prefix, {
				transfer(transferKind, prefix),
				assignmentValue(target, prefix .. "-unreachable-write", globalExpression("different_target", prefix .. "-unreachable-value")),
			}),
			callStatement(call, prefix .. "-call-statement"),
		}),
		call,
		target,
		{ kind = "environment", name = "authenticated_target" }
	)
	assert(proof.alias_depth == 1 and proof.definition_count == 1, prefix .. " inherited a write after transfer")
end

for _, transferKind in { "AstStatBreak", "AstStatContinue" } do
	local prefix = "loop-transfer-divergent-" .. transferKind
	local stable = declaration("divergentStable", prefix .. "-stable")
	local target = declaration("divergentTarget", prefix .. "-target")
	local call = callExpression(target, prefix .. "-call")
	expectFailure(function()
		verifyOrigin(
			document({
				localStatement(stable, prefix .. "-stable-declaration", authenticatedStable(prefix)),
				localStatement(target, prefix .. "-target-declaration", localExpression(stable, prefix .. "-incoming")),
				whileStatement(prefix, {
					assignmentValue(target, prefix .. "-write", globalExpression("different_target", prefix .. "-write-value")),
					transfer(transferKind, prefix),
				}),
				callStatement(call, prefix .. "-call-statement"),
			}),
			call,
			target,
			{ kind = "environment", name = "authenticated_target" }
		)
	end, "has an unauthenticated feasible definition")
end

for _, loopKind in { "AstStatFor", "AstStatForIn" } do
	local prefix = "loop-transfer-for-continue-" .. loopKind
	local stable = declaration("forStable", prefix .. "-stable")
	local target = declaration("forTarget", prefix .. "-target")
	local call = callExpression(target, prefix .. "-call")
	local body = block({
		assignmentValue(target, prefix .. "-write", localExpression(stable, prefix .. "-write-value")),
		transfer("AstStatContinue", prefix),
	}, prefix .. "-body")
	local loop: Record = if loopKind == "AstStatFor"
		then {
			type = loopKind,
			location = prefix .. "-for",
			var = declaration("forIndex", prefix .. "-index"),
			from = globalExpression("start", prefix .. "-start"),
			to = globalExpression("limit", prefix .. "-limit"),
			step = nil,
			body = body,
		}
		else {
			type = loopKind,
			location = prefix .. "-for",
			vars = { declaration("forValue", prefix .. "-value") },
			values = { globalExpression("iterator", prefix .. "-iterator") },
			body = body,
		}
	local proof = verifyOrigin(
		document({
			localStatement(stable, prefix .. "-stable-declaration", authenticatedStable(prefix)),
			localStatement(target, prefix .. "-target-declaration", localExpression(stable, prefix .. "-incoming")),
			loop,
			callStatement(call, prefix .. "-call-statement"),
		}),
		call,
		target,
		{ kind = "environment", name = "authenticated_target" }
	)
	assert(proof.alias_depth == 1 and proof.definition_count == 2, prefix .. " lost its continue backedge")
end

for _, transferKind in { "AstStatBreak", "AstStatContinue" } do
	local prefix = "loop-transfer-nested-" .. transferKind
	local stable = declaration("nestedStable", prefix .. "-stable")
	local target = declaration("nestedTarget", prefix .. "-target")
	local call = callExpression(target, prefix .. "-call")
	local proof = verifyOrigin(
		document({
			localStatement(stable, prefix .. "-stable-declaration", authenticatedStable(prefix)),
			localStatement(target, prefix .. "-target-declaration"),
			repeatStatement(prefix .. "-outer", {
				repeatStatement(prefix .. "-inner", { transfer(transferKind, prefix .. "-inner") }),
				assignmentValue(target, prefix .. "-write", localExpression(stable, prefix .. "-write-value")),
			}),
			callStatement(call, prefix .. "-call-statement"),
		}),
		call,
		target,
		{ kind = "environment", name = "authenticated_target" }
	)
	assert(proof.alias_depth == 1 and proof.definition_count == 1, prefix .. " escaped its nearest loop")
end

for _, transferKind in { "AstStatBreak", "AstStatContinue" } do
	local prefix = "loop-transfer-repeat-entry-" .. transferKind
	local stable = declaration("entryStable", prefix .. "-stable")
	local target = declaration("entryTarget", prefix .. "-target")
	local call = callExpression(target, prefix .. "-call")
	expectFailure(function()
		verifyOrigin(
			document({
				localStatement(stable, prefix .. "-stable-declaration", authenticatedStable(prefix)),
				localStatement(target, prefix .. "-target-declaration"),
				repeatStatement(prefix, {
					transfer(transferKind, prefix),
					assignmentValue(target, prefix .. "-unreachable-write", localExpression(stable, prefix .. "-write-value")),
				}),
				callStatement(call, prefix .. "-call-statement"),
			}),
			call,
			target,
			{ kind = "environment", name = "authenticated_target" }
		)
	end, "has an unauthenticated feasible definition")
end

local closurePrefix = "loop-transfer-closure"
local closureStable = declaration("closureStable", closurePrefix .. "-stable")
local closureTarget = declaration("closureTarget", closurePrefix .. "-target")
local closureCall = callExpression(closureTarget, closurePrefix .. "-call")
local closureHolder = declaration("closureHolder", closurePrefix .. "-holder")
local closureValue: Record = {
	type = "AstExprFunction",
	location = closurePrefix .. "-function",
	args = {},
	body = block({ whileStatement(closurePrefix .. "-inner-loop", { transfer("AstStatBreak", closurePrefix .. "-inner") }) }, closurePrefix .. "-function-body"),
}
local closureProof = verifyOrigin(
	document({
		localStatement(closureStable, closurePrefix .. "-stable-declaration", authenticatedStable(closurePrefix)),
		localStatement(closureTarget, closurePrefix .. "-target-declaration"),
		repeatStatement(closurePrefix, {
			localStatement(closureHolder, closurePrefix .. "-holder-declaration", closureValue),
			assignmentValue(closureTarget, closurePrefix .. "-write", localExpression(closureStable, closurePrefix .. "-write-value")),
		}),
		callStatement(closureCall, closurePrefix .. "-call-statement"),
	}),
	closureCall,
	closureTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(closureProof.alias_depth == 1 and closureProof.definition_count == 1, "closure-local transfer escaped its owner")
