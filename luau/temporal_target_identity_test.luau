--!strict

local TemporalTargetIdentity = require("./temporal_target_identity")

local Support = require("./temporal_test_support")

type Record = Support.Record

local aliasJoinDocument = Support.aliasJoinDocument
local assignment = Support.assignment
local assignmentValue = Support.assignmentValue
local block = Support.block
local branchStatement = Support.branchStatement
local callExpression = Support.callExpression
local callStatement = Support.callStatement
local declaration = Support.declaration
local document = Support.document
local environmentAliasChain = Support.environmentAliasChain
local expectFailure = Support.expectFailure
local localExpression = Support.localExpression
local localStatement = Support.localStatement
local verify = Support.verify
local verifyOrigin = Support.verifyOrigin

local immutable = declaration("snapshot", "immutable")
local immutableCall = callExpression(immutable, "immutable-call")
local immutableProof = verify(
	document({ localStatement(immutable, "immutable-declaration"), callStatement(immutableCall, "immutable-call-statement") }),
	immutableCall,
	immutable,
	"local_value"
)
assert(
	immutableProof.binding_kind == "value" and immutableProof.definition_kind == "declaration",
	"immutable temporal target lost its declaration proof"
)

local mutable = declaration("mutable", "mutable")
local mutableCall = callExpression(mutable, "mutable-call")
local mutableProof = verifyOrigin(
	document({
		localStatement(mutable, "mutable-declaration"),
		assignment(mutable, "mutable-write"),
		callStatement(mutableCall, "mutable-call-statement"),
	}),
	mutableCall,
	mutable,
	{ kind = "environment", name = "authenticated_target" }
)
assert(
	mutableProof.binding_kind == "place" and mutableProof.definition_kind == "assignment",
	"mutable temporal target lost its reaching-write proof"
)

local overwritten = declaration("overwritten", "overwritten")
local overwrittenCall = callExpression(overwritten, "overwritten-call")
local overwrittenProof = verifyOrigin(
	document({
		localStatement(overwritten, "overwritten-declaration"),
		{
			type = "AstStatIf",
			location = "overwritten-if",
			condition = { type = "AstExprGlobal", location = "overwritten-condition", global = "condition" },
			thenbody = block({ assignment(overwritten, "conditional-write") }, "conditional-block"),
			elsebody = nil,
		},
		assignment(overwritten, "dominating-write"),
		callStatement(overwrittenCall, "overwritten-call-statement"),
	}),
	overwrittenCall,
	overwritten,
	{ kind = "environment", name = "authenticated_target" }
)
assert(overwrittenProof.definition_location == "dominating-write", "later dominating write did not replace conditional definitions")

local sharedSnapshot = declaration("sharedSnapshot", "shared-snapshot")
local joinedTarget = declaration("joinedTarget", "joined-target")
local joinedTargetCall = callExpression(joinedTarget, "joined-target-call")
local joinedTargetProof = verifyOrigin(
	document({
		localStatement(sharedSnapshot, "shared-snapshot-declaration", {
			type = "AstExprGlobal",
			location = "shared-snapshot-value",
			global = "authenticated_target",
		}),
		localStatement(joinedTarget, "joined-target-declaration"),
		branchStatement(
			"joined-target",
			{ assignmentValue(joinedTarget, "joined-target-then-write", localExpression(sharedSnapshot, "joined-target-then-value")) },
			block({
				assignmentValue(joinedTarget, "joined-target-else-write", localExpression(sharedSnapshot, "joined-target-else-value")),
			}, "joined-target-else")
		),
		callStatement(joinedTargetCall, "joined-target-call-statement"),
	}),
	joinedTargetCall,
	joinedTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(
	joinedTargetProof.binding_kind == "place"
		and joinedTargetProof.definition_kind == "definition_set"
		and joinedTargetProof.definition_count == 2
		and joinedTargetProof.alias_depth == 1,
	"equivalent branch writes did not retain one shared snapshot identity"
)

local nestedSnapshot = declaration("nestedSnapshot", "nested-snapshot")
local nestedTarget = declaration("nestedTarget", "nested-target")
local nestedTargetCall = callExpression(nestedTarget, "nested-target-call")
local nestedTargetProof = verifyOrigin(
	document({
		localStatement(nestedSnapshot, "nested-snapshot-declaration", {
			type = "AstExprGlobal",
			location = "nested-snapshot-value",
			global = "authenticated_target",
		}),
		localStatement(nestedTarget, "nested-target-declaration"),
		branchStatement(
			"nested-target-outer",
			{ assignmentValue(nestedTarget, "nested-target-first-write", localExpression(nestedSnapshot, "nested-target-first-value")) },
			branchStatement(
				"nested-target-inner",
				{ assignmentValue(nestedTarget, "nested-target-second-write", localExpression(nestedSnapshot, "nested-target-second-value")) },
				block({
					assignmentValue(nestedTarget, "nested-target-third-write", localExpression(nestedSnapshot, "nested-target-third-value")),
				}, "nested-target-final-else")
			)
		),
		callStatement(nestedTargetCall, "nested-target-call-statement"),
	}),
	nestedTargetCall,
	nestedTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(nestedTargetProof.definition_count == 3, "nested structured branches lost a feasible target definition")

local directAliasJoinDocument, directAliasJoinCall, directAliasJoinTarget = aliasJoinDocument(1, 2, "direct-alias-join")
local directAliasJoinProof = verifyOrigin(
	directAliasJoinDocument,
	directAliasJoinCall,
	directAliasJoinTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(
	directAliasJoinProof.binding_kind == "value" and directAliasJoinProof.alias_depth == 2,
	"intermediate structured alias join did not converge on its stable anchor"
)

local nestedAliasJoinDocument, nestedAliasJoinCall, nestedAliasJoinTarget = aliasJoinDocument(2, 2, "nested-alias-join")
local nestedAliasJoinProof = verifyOrigin(
	nestedAliasJoinDocument,
	nestedAliasJoinCall,
	nestedAliasJoinTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(nestedAliasJoinProof.alias_depth == 3, "nested structured alias joins lost their common stable anchor")

local returnedSnapshot = declaration("returnedSnapshot", "returned-snapshot")
local returnedTarget = declaration("returnedTarget", "returned-target")
local returnedTargetCall = callExpression(returnedTarget, "returned-target-call")
local returnedTargetProof = verifyOrigin(
	document({
		localStatement(returnedSnapshot, "returned-snapshot-declaration", {
			type = "AstExprGlobal",
			location = "returned-snapshot-value",
			global = "authenticated_target",
		}),
		localStatement(returnedTarget, "returned-target-declaration"),
		branchStatement(
			"returned-target",
			{ assignmentValue(returnedTarget, "returned-target-write", localExpression(returnedSnapshot, "returned-target-value")) },
			block({ { type = "AstStatReturn", location = "returned-target-return", list = {} } }, "returned-target-else")
		),
		callStatement(returnedTargetCall, "returned-target-call-statement"),
	}),
	returnedTargetCall,
	returnedTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(
	returnedTargetProof.definition_kind == "definition_set" and returnedTargetProof.definition_count == 1,
	"terminated branch remained in the feasible target definition set"
)

local ambiguous = declaration("ambiguous", "ambiguous")
local ambiguousCall = callExpression(ambiguous, "ambiguous-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(ambiguous, "ambiguous-declaration"),
			{
				type = "AstStatIf",
				location = "ambiguous-if",
				condition = { type = "AstExprGlobal", location = "ambiguous-condition", global = "condition" },
				thenbody = block({ assignment(ambiguous, "ambiguous-write") }, "ambiguous-block"),
				elsebody = nil,
			},
			callStatement(ambiguousCall, "ambiguous-call-statement"),
		}),
		ambiguousCall,
		ambiguous,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has an unauthenticated feasible definition")

local firstSnapshot = declaration("firstSnapshot", "first-snapshot")
local secondSnapshot = declaration("secondSnapshot", "second-snapshot")
local divergentTarget = declaration("divergentTarget", "divergent-target")
local divergentAlias = declaration("divergentAlias", "divergent-alias")
local divergentTargetCall = callExpression(divergentAlias, "divergent-target-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(firstSnapshot, "first-snapshot-declaration", {
				type = "AstExprGlobal",
				location = "first-snapshot-value",
				global = "authenticated_target",
			}),
			localStatement(secondSnapshot, "second-snapshot-declaration", {
				type = "AstExprGlobal",
				location = "second-snapshot-value",
				global = "authenticated_target",
			}),
			localStatement(divergentTarget, "divergent-target-declaration"),
			branchStatement(
				"divergent-target",
				{ assignmentValue(divergentTarget, "divergent-target-then-write", localExpression(firstSnapshot, "divergent-target-then-value")) },
				block({
					assignmentValue(divergentTarget, "divergent-target-else-write", localExpression(secondSnapshot, "divergent-target-else-value")),
				}, "divergent-target-else")
			),
			localStatement(
				divergentAlias,
				"divergent-alias-declaration",
				localExpression(divergentTarget, "divergent-alias-value")
			),
			callStatement(divergentTargetCall, "divergent-target-call-statement"),
		}),
		divergentTargetCall,
		divergentAlias,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "does not share one stable authenticated identity")

local lookupNamespace = declaration("lookupNamespace", "lookup-namespace")
local lookupTarget = declaration("lookupTarget", "lookup-target")
local lookupAlias = declaration("lookupAlias", "lookup-alias")
local lookupTargetCall = callExpression(lookupAlias, "lookup-target-call")
local function lookupExpression(location: string): Record
	return {
		type = "AstExprIndexName",
		location = location,
		expr = localExpression(lookupNamespace, location .. ":table"),
		index = "dispatch",
	}
end
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(lookupNamespace, "lookup-namespace-declaration", {
				type = "AstExprGlobal",
				location = "lookup-namespace-value",
				global = "namespace",
			}),
			localStatement(lookupTarget, "lookup-target-declaration"),
			branchStatement(
				"lookup-target",
				{ assignmentValue(lookupTarget, "lookup-target-then-write", lookupExpression("lookup-target-then-value")) },
				block({
					assignmentValue(lookupTarget, "lookup-target-else-write", lookupExpression("lookup-target-else-value")),
				}, "lookup-target-else")
			),
			localStatement(
				lookupAlias,
				"lookup-alias-declaration",
				localExpression(lookupTarget, "lookup-alias-value")
			),
			callStatement(lookupTargetCall, "lookup-target-call-statement"),
		}),
		lookupTargetCall,
		lookupAlias,
		{
			kind = "table_get",
			table_origin = { kind = "local_value", declaration = lookupNamespace },
			key_origin = { kind = "constant_string", value = "dispatch" },
		}
	)
end, "does not share one stable authenticated identity")

local loopSnapshot = declaration("loopSnapshot", "loop-snapshot")
local loopTarget = declaration("loopTarget", "loop-target")
local loopTargetCall = callExpression(loopTarget, "loop-target-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(loopSnapshot, "loop-snapshot-declaration", {
				type = "AstExprGlobal",
				location = "loop-snapshot-value",
				global = "authenticated_target",
			}),
			localStatement(loopTarget, "loop-target-declaration"),
			{
				type = "AstStatWhile",
				location = "loop-target-while",
				condition = { type = "AstExprGlobal", location = "loop-target-condition", global = "condition" },
				body = block({
					assignmentValue(loopTarget, "loop-target-write", localExpression(loopSnapshot, "loop-target-value")),
				}, "loop-target-body"),
			},
			callStatement(loopTargetCall, "loop-target-call-statement"),
		}),
		loopTargetCall,
		loopTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has an unauthenticated feasible definition")

local capturedMutable = declaration("capturedMutable", "captured-mutable")
local capturedMutableCall = callExpression(capturedMutable, "captured-mutable-call")
local capturedFunction = {
	type = "AstExprFunction",
	location = "captured-mutable-function",
	args = {},
	body = block({ callStatement(capturedMutableCall, "captured-mutable-call-statement") }, "captured-mutable-body"),
}
local capturedMutableProof = verifyOrigin(
	document({
		localStatement(capturedMutable, "captured-mutable-declaration"),
		assignment(capturedMutable, "captured-mutable-write"),
		{ type = "AstStatReturn", location = "captured-mutable-return", list = { capturedFunction } },
	}),
	capturedMutableCall,
	capturedMutable,
	{ kind = "environment", name = "authenticated_target" }
)
assert(capturedMutableProof.binding_kind == "place", "stable captured temporal place lost its binding proof")

local mutationSnapshot = declaration("mutationSnapshot", "mutation-snapshot")
local mutatedAfterCapture = declaration("mutatedAfterCapture", "mutated-after-capture")
local mutatedAfterCaptureCall = callExpression(mutatedAfterCapture, "mutated-after-capture-call")
local mutationClosure = {
	type = "AstExprFunction",
	location = "mutation-closure",
	args = {},
	body = block({ callStatement(mutatedAfterCaptureCall, "mutation-call-statement") }, "mutation-body"),
}
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(mutationSnapshot, "mutation-snapshot-declaration", {
				type = "AstExprGlobal",
				location = "mutation-snapshot-value",
				global = "authenticated_target",
			}),
			localStatement(mutatedAfterCapture, "mutation-declaration"),
			branchStatement(
				"mutation-before-capture",
				{ assignmentValue(mutatedAfterCapture, "mutation-then-write", localExpression(mutationSnapshot, "mutation-then-value")) },
				block({
					assignmentValue(mutatedAfterCapture, "mutation-else-write", localExpression(mutationSnapshot, "mutation-else-value")),
				}, "mutation-else")
			),
			{
				type = "AstStatLocal",
				location = "mutation-closure-declaration",
				vars = { declaration("holder", "mutation-holder") },
				values = { mutationClosure },
			},
			assignment(mutatedAfterCapture, "mutation-after-capture-write"),
		}),
		mutatedAfterCaptureCall,
		mutatedAfterCapture,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has a write after or inside its closure snapshot")

local capturedValue = declaration("capturedValue", "captured-value")
local capturedValueCall = callExpression(capturedValue, "captured-value-call")
local capturedValueFunction = {
	type = "AstExprFunction",
	location = "captured-value-function",
	args = {},
	body = block({ callStatement(capturedValueCall, "captured-value-call-statement") }, "captured-value-body"),
}
local capturedValueProof = verify(
	document({
		localStatement(capturedValue, "captured-value-declaration"),
		{ type = "AstStatReturn", location = "captured-value-return", list = { capturedValueFunction } },
	}),
	capturedValueCall,
	capturedValue,
	"local_value"
)
assert(capturedValueProof.binding_kind == "value", "captured immutable temporal target lost lexical dominance")

local intrinsicAlias = declaration("intrinsicAlias", "intrinsic-alias")
local intrinsicAliasCall = callExpression(intrinsicAlias, "intrinsic-alias-call")
local intrinsicAliasProof = verifyOrigin(
	document({
		localStatement(intrinsicAlias, "intrinsic-alias-declaration", {
			type = "AstExprGlobal",
			location = "intrinsic-alias-value",
			global = "pcall",
		}),
		callStatement(intrinsicAliasCall, "intrinsic-alias-call-statement"),
	}),
	intrinsicAliasCall,
	intrinsicAlias,
	{ kind = "intrinsic", path = "pcall" }
)
assert(intrinsicAliasProof.binding_kind == "value", "authenticated intrinsic alias lost its temporal binding")

local intrinsicHopOne = declaration("intrinsicHopOne", "intrinsic-hop-one")
local intrinsicHopTwo = declaration("intrinsicHopTwo", "intrinsic-hop-two")
local intrinsicChain = declaration("intrinsicChain", "intrinsic-chain")
local intrinsicChainCall = callExpression(intrinsicChain, "intrinsic-chain-call")
local intrinsicChainProof = verifyOrigin(
	document({
		localStatement(intrinsicHopOne, "intrinsic-hop-one-declaration", {
			type = "AstExprGlobal",
			location = "intrinsic-hop-one-value",
			global = "pcall",
		}),
		localStatement(
			intrinsicHopTwo,
			"intrinsic-hop-two-declaration",
			localExpression(intrinsicHopOne, "intrinsic-hop-two-value")
		),
		localStatement(
			intrinsicChain,
			"intrinsic-chain-declaration",
			localExpression(intrinsicHopTwo, "intrinsic-chain-value")
		),
		callStatement(intrinsicChainCall, "intrinsic-chain-call-statement"),
	}),
	intrinsicChainCall,
	intrinsicChain,
	{ kind = "intrinsic", path = "pcall" }
)
assert(intrinsicChainProof.alias_depth == 2, "two-hop intrinsic identity lost its bounded alias proof")

local environmentChainDocument, environmentChainCall, environmentChain = environmentAliasChain(2, "environment-chain")
local environmentChainProof = verifyOrigin(
	environmentChainDocument,
	environmentChainCall,
	environmentChain,
	{ kind = "environment", name = "authenticated_target" }
)
assert(environmentChainProof.alias_depth == 2, "two-hop environment identity lost its bounded alias proof")

local maxAliasDepth: number = TemporalTargetIdentity.maxAliasDepth
local boundedChainDocument, boundedChainCall, boundedChain = environmentAliasChain(maxAliasDepth, "bounded-chain")
local boundedChainProof = verifyOrigin(
	boundedChainDocument,
	boundedChainCall,
	boundedChain,
	{ kind = "environment", name = "authenticated_target" }
)
assert(boundedChainProof.alias_depth == maxAliasDepth, "maximum temporal alias depth was rejected")

local excessiveChainDocument, excessiveChainCall, excessiveChain = environmentAliasChain(maxAliasDepth + 1, "excessive-chain")
expectFailure(function()
	verifyOrigin(
		excessiveChainDocument,
		excessiveChainCall,
		excessiveChain,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "alias chain exceeds the depth limit")

local maxAliasCandidates: number = TemporalTargetIdentity.maxAliasCandidates
local boundedAliasCandidateCount = math.floor((maxAliasCandidates - 1) / 2)
local boundedAliasJoinDocument, boundedAliasJoinCall, boundedAliasJoinTarget = aliasJoinDocument(
	1,
	boundedAliasCandidateCount,
	"bounded-alias-candidates"
)
local boundedAliasJoinProof = verifyOrigin(
	boundedAliasJoinDocument,
	boundedAliasJoinCall,
	boundedAliasJoinTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(boundedAliasJoinProof.alias_depth == 2, "bounded alias candidate expansion was rejected")

local excessiveAliasJoinDocument, excessiveAliasJoinCall, excessiveAliasJoinTarget = aliasJoinDocument(
	1,
	boundedAliasCandidateCount + 1,
	"excessive-alias-candidates"
)
expectFailure(function()
	verifyOrigin(
		excessiveAliasJoinDocument,
		excessiveAliasJoinCall,
		excessiveAliasJoinTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "alias candidate expansion exceeds the limit")

local mismatchedAlias = declaration("mismatchedAlias", "mismatched-alias")
local mismatchedAliasCall = callExpression(mismatchedAlias, "mismatched-alias-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(mismatchedAlias, "mismatched-alias-declaration", {
				type = "AstExprGlobal",
				location = "mismatched-alias-value",
				global = "actual_target",
			}),
			callStatement(mismatchedAliasCall, "mismatched-alias-call-statement"),
		}),
		mismatchedAliasCall,
		mismatchedAlias,
		{ kind = "environment", name = "claimed_target" }
	)
end, "does not match its authenticated origin")

local cyclicAlias = declaration("cyclicAlias", "cyclic-alias")
local cyclicAliasCall = callExpression(cyclicAlias, "cyclic-alias-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(cyclicAlias, "cyclic-alias-declaration"),
			assignmentValue(
				cyclicAlias,
				"cyclic-alias-write",
				localExpression(cyclicAlias, "cyclic-alias-value")
			),
			callStatement(cyclicAliasCall, "cyclic-alias-call-statement"),
		}),
		cyclicAliasCall,
		cyclicAlias,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "alias chain contains a cycle")

local setCycleStable = declaration("setCycleStable", "set-cycle-stable")
local setCycleAlias = declaration("setCycleAlias", "set-cycle-alias")
local setCycleTarget = declaration("setCycleTarget", "set-cycle-target")
local setCycleCall = callExpression(setCycleTarget, "set-cycle-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(setCycleStable, "set-cycle-stable-declaration", {
				type = "AstExprGlobal",
				location = "set-cycle-stable-value",
				global = "authenticated_target",
			}),
			localStatement(setCycleAlias, "set-cycle-alias-declaration"),
			assignmentValue(setCycleAlias, "set-cycle-alias-write", localExpression(setCycleAlias, "set-cycle-alias-value")),
			localStatement(setCycleTarget, "set-cycle-target-declaration"),
			branchStatement(
				"set-cycle-target",
				{ assignmentValue(setCycleTarget, "set-cycle-target-then-write", localExpression(setCycleAlias, "set-cycle-target-then-value")) },
				block({
					assignmentValue(setCycleTarget, "set-cycle-target-else-write", localExpression(setCycleStable, "set-cycle-target-else-value")),
				}, "set-cycle-target-else")
			),
			callStatement(setCycleCall, "set-cycle-call-statement"),
		}),
		setCycleCall,
		setCycleTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "alias chain contains a cycle")

local ambiguousIntermediate = declaration("ambiguousIntermediate", "ambiguous-intermediate")
local ambiguousTarget = declaration("ambiguousTarget", "ambiguous-target")
local ambiguousTargetCall = callExpression(ambiguousTarget, "ambiguous-target-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(ambiguousIntermediate, "ambiguous-intermediate-declaration"),
			{
				type = "AstStatIf",
				location = "ambiguous-intermediate-if",
				condition = { type = "AstExprGlobal", location = "ambiguous-intermediate-condition", global = "condition" },
				thenbody = block({ assignment(ambiguousIntermediate, "ambiguous-intermediate-write") }, "ambiguous-intermediate-block"),
				elsebody = nil,
			},
			localStatement(
				ambiguousTarget,
				"ambiguous-target-declaration",
				localExpression(ambiguousIntermediate, "ambiguous-target-value")
			),
			callStatement(ambiguousTargetCall, "ambiguous-target-call-statement"),
		}),
		ambiguousTargetCall,
		ambiguousTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "temporal alias place ambiguous-intermediate has an unauthenticated feasible definition")

local capturedIntermediate = declaration("capturedIntermediate", "captured-intermediate")
local capturedAliasTarget = declaration("capturedAliasTarget", "captured-alias-target")
local capturedAliasCall = callExpression(capturedAliasTarget, "captured-alias-call")
local capturedAliasFunction = {
	type = "AstExprFunction",
	location = "captured-alias-function",
	args = {},
	body = block({
		localStatement(
			capturedAliasTarget,
			"captured-alias-target-declaration",
			localExpression(capturedIntermediate, "captured-alias-target-value")
		),
		callStatement(capturedAliasCall, "captured-alias-call-statement"),
	}, "captured-alias-body"),
}
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(capturedIntermediate, "captured-intermediate-declaration"),
			assignment(capturedIntermediate, "captured-intermediate-write"),
			localStatement(declaration("capturedAliasHolder", "captured-alias-holder"), "captured-alias-closure", capturedAliasFunction),
			assignment(capturedIntermediate, "captured-intermediate-later-write"),
		}),
		capturedAliasCall,
		capturedAliasTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "temporal alias place captured-intermediate has a write after or inside its closure snapshot")
