--!strict

local TargetRecovery = require("./target_recovery")
local Support = require("./temporal_test_support")
local TemporalTargetIdentity = require("./temporal_target_identity")

type Record = Support.Record

local assignment = Support.assignment
local assignmentValue = Support.assignmentValue
local block = Support.block
local callExpression = Support.callExpression
local callStatement = Support.callStatement
local declaration = Support.declaration
local document = Support.document
local expectFailure = Support.expectFailure
local globalExpression = Support.globalExpression
local invocationFromBody = Support.invocationFromBody
local localExpression = Support.localExpression
local localStatement = Support.localStatement
local verifyOrigin = Support.verifyOrigin
local whileStatement = Support.whileStatement

local function immediateInvocation(innerCall: Record, prefix: string, wrappers: { string }?): (Record, Record)
	return invocationFromBody({ callStatement(innerCall, prefix .. "-inner-call-statement") }, prefix, wrappers, nil)
end

local function mutationInvocation(target: Record, prefix: string, wrappers: { string }?): (Record, Record)
	return invocationFromBody({
		assignmentValue(target, prefix .. "-write", globalExpression("different_target", prefix .. "-value")),
	}, prefix, wrappers, nil)
end

local function mutationInvocationChain(target: Record, prefix: string, depth: number): Record
	assert(depth >= 1)
	local _, invocation = mutationInvocation(target, prefix .. "-1", nil)
	for index = 2, depth do
		local _, outer = invocationFromBody({
			callStatement(invocation, `{prefix}-{index - 1}-statement`),
		}, `{prefix}-{index}`, nil, nil)
		invocation = outer
	end
	return invocation
end

local function verifySynchronous(prefix: string, wrappers: { string }?)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local innerCall = callExpression(target, prefix .. "-target-call")
	local _, invocation = immediateInvocation(innerCall, prefix, wrappers)
	local proof = verifyOrigin(
		document({
			localStatement(target, prefix .. "-target-declaration"),
			assignment(target, prefix .. "-current-write"),
			callStatement(invocation, prefix .. "-invocation-statement"),
			assignmentValue(target, prefix .. "-later-write", globalExpression("different_target", prefix .. "-later-value")),
		}),
		innerCall,
		target,
		{ kind = "environment", name = "authenticated_target" }
	)
	assert(proof.definition_location == prefix .. "-current-write", prefix .. " did not use its synchronous invocation point")
end

verifySynchronous("immediate-direct", nil)
verifySynchronous("immediate-wrapped", { "AstExprGroup", "AstExprTypeAssertion", "AstExprInstantiate" })

local futureTarget = declaration("futureTarget", "immediate-future-target")
local futureCall = callExpression(futureTarget, "immediate-future-call")
local _, futureInvocation = invocationFromBody({
	callStatement(futureCall, "immediate-future-call-statement"),
	assignmentValue(
		futureTarget,
		"immediate-future-write",
		globalExpression("different_target", "immediate-future-write-value")
	),
}, "immediate-future", nil, nil)
local futureProof = verifyOrigin(
	document({
		localStatement(futureTarget, "immediate-future-target-declaration"),
		assignment(futureTarget, "immediate-future-current-write"),
		callStatement(futureInvocation, "immediate-future-invocation-statement"),
	}),
	futureCall,
	futureTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(futureProof.definition_location == "immediate-future-current-write", "later invocation-local write stayed committed")

local guardFutureTarget = declaration("guardFutureTarget", "immediate-guard-future-target")
local guardFutureCall = callExpression(guardFutureTarget, "immediate-guard-future-call")
local guardFutureStatement: Record = {
	type = "AstStatIf",
	location = "immediate-guard-future-if",
	condition = guardFutureCall,
	thenbody = block({
		assignmentValue(
			guardFutureTarget,
			"immediate-guard-future-then-write",
			globalExpression("different_target", "immediate-guard-future-then-value")
		),
	}, "immediate-guard-future-then"),
	elsebody = block({
		assignmentValue(
			guardFutureTarget,
			"immediate-guard-future-else-write",
			globalExpression("different_target", "immediate-guard-future-else-value")
		),
	}, "immediate-guard-future-else"),
}
local _, guardFutureInvocation = invocationFromBody({ guardFutureStatement }, "immediate-guard-future", nil, nil)
local guardFutureProof = verifyOrigin(
	document({
		localStatement(guardFutureTarget, "immediate-guard-future-target-declaration"),
		assignment(guardFutureTarget, "immediate-guard-future-current-write"),
		callStatement(guardFutureInvocation, "immediate-guard-future-invocation-statement"),
	}),
	guardFutureCall,
	guardFutureTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(guardFutureProof.definition_count == 1, "guarded invocation-local writes stayed committed")

local precommitFutureTarget = declaration("precommitFutureTarget", "immediate-precommit-future-target")
local precommitFutureCall = callExpression(precommitFutureTarget, "immediate-precommit-future-call")
local _, precommitFutureInvocation = invocationFromBody({
	assignmentValue(precommitFutureTarget, "immediate-precommit-future-write", precommitFutureCall),
}, "immediate-precommit-future", nil, nil)
local precommitFutureProof = verifyOrigin(
	document({
		localStatement(precommitFutureTarget, "immediate-precommit-future-target-declaration"),
		assignment(precommitFutureTarget, "immediate-precommit-future-current-write"),
		callStatement(precommitFutureInvocation, "immediate-precommit-future-invocation-statement"),
	}),
	precommitFutureCall,
	precommitFutureTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(precommitFutureProof.definition_count == 1, "same-statement invocation-local write committed before its RHS")

local nestedFutureTarget = declaration("nestedFutureTarget", "nested-future-target")
local nestedFutureCall = callExpression(nestedFutureTarget, "nested-future-call")
local _, nestedFutureMutation = mutationInvocation(
	nestedFutureTarget,
	"nested-future-mutation",
	{ "AstExprGroup", "AstExprTypeAssertion", "AstExprInstantiate" }
)
local _, nestedFutureOuter = invocationFromBody({
	callStatement(nestedFutureCall, "nested-future-call-statement"),
	callStatement(nestedFutureMutation, "nested-future-mutation-statement"),
}, "nested-future-outer", nil, nil)
local nestedFutureProof = verifyOrigin(
	document({
		localStatement(nestedFutureTarget, "nested-future-target-declaration"),
		assignment(nestedFutureTarget, "nested-future-current-write"),
		callStatement(nestedFutureOuter, "nested-future-outer-statement"),
	}),
	nestedFutureCall,
	nestedFutureTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(nestedFutureProof.definition_location == "nested-future-current-write", "later nested IIFE write stayed committed")

local boundedNestedTarget = declaration("boundedNestedTarget", "bounded-nested-target")
local boundedNestedCall = callExpression(boundedNestedTarget, "bounded-nested-call")
local boundedNestedMutation = mutationInvocationChain(
	boundedNestedTarget,
	"bounded-nested-mutation",
	TemporalTargetIdentity.maxInvocationDepth
)
local _, boundedNestedOuter = invocationFromBody({
	callStatement(boundedNestedCall, "bounded-nested-call-statement"),
	callStatement(boundedNestedMutation, "bounded-nested-mutation-statement"),
}, "bounded-nested-outer", nil, nil)
local boundedNestedProof = verifyOrigin(
	document({
		localStatement(boundedNestedTarget, "bounded-nested-target-declaration"),
		assignment(boundedNestedTarget, "bounded-nested-current-write"),
		callStatement(boundedNestedOuter, "bounded-nested-outer-statement"),
	}),
	boundedNestedCall,
	boundedNestedTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(boundedNestedProof.definition_count == 1, "maximum direct-invocation chain did not compose")

local excessiveNestedTarget = declaration("excessiveNestedTarget", "excessive-nested-target")
local excessiveNestedCall = callExpression(excessiveNestedTarget, "excessive-nested-call")
local excessiveNestedMutation = mutationInvocationChain(
	excessiveNestedTarget,
	"excessive-nested-mutation",
	TemporalTargetIdentity.maxInvocationDepth + 1
)
local _, excessiveNestedOuter = invocationFromBody({
	callStatement(excessiveNestedCall, "excessive-nested-call-statement"),
	callStatement(excessiveNestedMutation, "excessive-nested-mutation-statement"),
}, "excessive-nested-outer", nil, nil)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(excessiveNestedTarget, "excessive-nested-target-declaration"),
			assignment(excessiveNestedTarget, "excessive-nested-current-write"),
			callStatement(excessiveNestedOuter, "excessive-nested-outer-statement"),
		}),
		excessiveNestedCall,
		excessiveNestedTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has no feasible structured definition set")

local nestedGuardTarget = declaration("nestedGuardTarget", "nested-guard-target")
local nestedGuardCall = callExpression(nestedGuardTarget, "nested-guard-call")
local _, nestedGuardThenMutation = mutationInvocation(nestedGuardTarget, "nested-guard-then-mutation", nil)
local _, nestedGuardElseMutation = mutationInvocation(nestedGuardTarget, "nested-guard-else-mutation", nil)
local nestedGuardStatement: Record = {
	type = "AstStatIf",
	location = "nested-guard-if",
	condition = nestedGuardCall,
	thenbody = block({
		callStatement(nestedGuardThenMutation, "nested-guard-then-statement"),
	}, "nested-guard-then"),
	elsebody = block({
		callStatement(nestedGuardElseMutation, "nested-guard-else-statement"),
	}, "nested-guard-else"),
}
local _, nestedGuardOuter = invocationFromBody({ nestedGuardStatement }, "nested-guard-outer", nil, nil)
local nestedGuardProof = verifyOrigin(
	document({
		localStatement(nestedGuardTarget, "nested-guard-target-declaration"),
		assignment(nestedGuardTarget, "nested-guard-current-write"),
		callStatement(nestedGuardOuter, "nested-guard-outer-statement"),
	}),
	nestedGuardCall,
	nestedGuardTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(nestedGuardProof.definition_count == 1, "guarded nested IIFE writes stayed committed")

local nestedEarlierTarget = declaration("nestedEarlierTarget", "nested-earlier-target")
local nestedEarlierCall = callExpression(nestedEarlierTarget, "nested-earlier-call")
local _, nestedEarlierMutation = mutationInvocation(nestedEarlierTarget, "nested-earlier-mutation", nil)
local _, nestedEarlierOuter = invocationFromBody({
	callStatement(nestedEarlierMutation, "nested-earlier-mutation-statement"),
	callStatement(nestedEarlierCall, "nested-earlier-call-statement"),
}, "nested-earlier-outer", nil, nil)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(nestedEarlierTarget, "nested-earlier-target-declaration"),
			assignment(nestedEarlierTarget, "nested-earlier-current-write"),
			callStatement(nestedEarlierOuter, "nested-earlier-outer-statement"),
		}),
		nestedEarlierCall,
		nestedEarlierTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has no feasible structured definition set")

local nestedArgumentTarget = declaration("nestedArgumentTarget", "nested-argument-target")
local nestedArgumentCall = callExpression(nestedArgumentTarget, "nested-argument-call")
local _, nestedArgumentMutation = mutationInvocation(nestedArgumentTarget, "nested-argument-mutation", nil)
local nestedArgumentConsumer: Record = {
	type = "AstExprCall",
	location = "nested-argument-consumer-call",
	func = globalExpression("consume", "nested-argument-consumer"),
	args = { nestedArgumentCall, nestedArgumentMutation },
	self = false,
}
local _, nestedArgumentOuter = invocationFromBody({
	callStatement(nestedArgumentConsumer, "nested-argument-consumer-statement"),
}, "nested-argument-outer", nil, nil)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(nestedArgumentTarget, "nested-argument-target-declaration"),
			assignment(nestedArgumentTarget, "nested-argument-current-write"),
			callStatement(nestedArgumentOuter, "nested-argument-outer-statement"),
		}),
		nestedArgumentCall,
		nestedArgumentTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has no feasible structured definition set")

local nestedLoopTarget = declaration("nestedLoopTarget", "nested-loop-write-target")
local nestedLoopCall = callExpression(nestedLoopTarget, "nested-loop-write-call")
local _, nestedLoopMutation = mutationInvocation(nestedLoopTarget, "nested-loop-write-mutation", nil)
local _, nestedLoopOuter = invocationFromBody({
	whileStatement("nested-loop-write", {
		callStatement(nestedLoopCall, "nested-loop-write-call-statement"),
		callStatement(nestedLoopMutation, "nested-loop-write-mutation-statement"),
	}),
}, "nested-loop-write-outer", nil, nil)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(nestedLoopTarget, "nested-loop-write-target-declaration"),
			assignment(nestedLoopTarget, "nested-loop-write-current-write"),
			callStatement(nestedLoopOuter, "nested-loop-write-outer-statement"),
		}),
		nestedLoopCall,
		nestedLoopTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has no feasible structured definition set")

local storedTarget = declaration("storedTarget", "immediate-stored-target")
local storedCall = callExpression(storedTarget, "immediate-stored-call")
local storedFunction, _ = immediateInvocation(storedCall, "immediate-stored", nil)
local storedHolder = declaration("storedHolder", "immediate-stored-holder")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(storedTarget, "immediate-stored-target-declaration"),
			assignment(storedTarget, "immediate-stored-current-write"),
			localStatement(storedHolder, "immediate-stored-holder-declaration", storedFunction),
			assignment(storedTarget, "immediate-stored-later-write"),
		}),
		storedCall,
		storedTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has a write after or inside its closure snapshot")

local passedTarget = declaration("passedTarget", "immediate-passed-target")
local passedCall = callExpression(passedTarget, "immediate-passed-call")
local passedFunction, _ = immediateInvocation(passedCall, "immediate-passed", nil)
local consumerCall: Record = {
	type = "AstExprCall",
	location = "immediate-passed-consumer-call",
	func = globalExpression("consume", "immediate-passed-consumer"),
	args = { passedFunction },
	self = false,
}
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(passedTarget, "immediate-passed-target-declaration"),
			assignment(passedTarget, "immediate-passed-current-write"),
			callStatement(consumerCall, "immediate-passed-consumer-statement"),
			assignment(passedTarget, "immediate-passed-later-write"),
		}),
		passedCall,
		passedTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has a write after or inside its closure snapshot")

local internalTarget = declaration("internalTarget", "immediate-internal-target")
local internalCall = callExpression(internalTarget, "immediate-internal-call")
local internalFunction: Record = {
	type = "AstExprFunction",
	location = "immediate-internal-function",
	args = {},
	body = block({
		assignmentValue(
			internalTarget,
			"immediate-internal-write",
			globalExpression("different_target", "immediate-internal-write-value")
		),
		callStatement(internalCall, "immediate-internal-call-statement"),
	}, "immediate-internal-body"),
}
local internalInvocation: Record = {
	type = "AstExprCall",
	location = "immediate-internal-invocation",
	func = internalFunction,
	args = {},
	self = false,
}
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(internalTarget, "immediate-internal-target-declaration"),
			assignment(internalTarget, "immediate-internal-current-write"),
			callStatement(internalInvocation, "immediate-internal-invocation-statement"),
		}),
		internalCall,
		internalTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has no feasible structured definition set")

local nestedTarget = declaration("nestedTarget", "immediate-nested-target")
local nestedCall = callExpression(nestedTarget, "immediate-nested-call")
local nestedInner: Record = {
	type = "AstExprFunction",
	location = "immediate-nested-inner-function",
	args = {},
	body = block({ callStatement(nestedCall, "immediate-nested-call-statement") }, "immediate-nested-inner-body"),
}
local nestedHolder = declaration("nestedHolder", "immediate-nested-holder")
local nestedOuter: Record = {
	type = "AstExprFunction",
	location = "immediate-nested-outer-function",
	args = {},
	body = block({
		localStatement(nestedHolder, "immediate-nested-holder-declaration", nestedInner),
	}, "immediate-nested-outer-body"),
}
local nestedInvocation: Record = {
	type = "AstExprCall",
	location = "immediate-nested-outer-invocation",
	func = nestedOuter,
	args = {},
	self = false,
}
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(nestedTarget, "immediate-nested-target-declaration"),
			assignment(nestedTarget, "immediate-nested-current-write"),
			callStatement(nestedInvocation, "immediate-nested-invocation-statement"),
			assignment(nestedTarget, "immediate-nested-later-write"),
		}),
		nestedCall,
		nestedTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has a write after or inside its closure snapshot")

local loopTarget = declaration("loopTarget", "immediate-loop-target")
local loopCall = callExpression(loopTarget, "immediate-loop-call")
local _, loopInvocation = immediateInvocation(loopCall, "immediate-loop", nil)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(loopTarget, "immediate-loop-target-declaration"),
			assignment(loopTarget, "immediate-loop-current-write"),
			whileStatement("immediate-loop", {
				callStatement(loopInvocation, "immediate-loop-invocation-statement"),
				assignmentValue(loopTarget, "immediate-loop-later-write", globalExpression("different_target", "immediate-loop-later-value")),
			}),
		}),
		loopCall,
		loopTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has an unauthenticated feasible definition")

local resetStable = declaration("resetStable", "immediate-reset-stable")
local resetTarget = declaration("resetTarget", "immediate-reset-target")
local resetCall = callExpression(resetTarget, "immediate-reset-call")
local _, resetInvocation = immediateInvocation(resetCall, "immediate-reset", nil)
local resetProof = verifyOrigin(
	document({
		localStatement(
			resetStable,
			"immediate-reset-stable-declaration",
			globalExpression("authenticated_target", "immediate-reset-stable-value")
		),
		localStatement(resetTarget, "immediate-reset-target-declaration"),
		whileStatement("immediate-reset", {
			assignmentValue(resetTarget, "immediate-reset-current-write", localExpression(resetStable, "immediate-reset-current-value")),
			callStatement(resetInvocation, "immediate-reset-invocation-statement"),
			assignmentValue(resetTarget, "immediate-reset-later-write", globalExpression("different_target", "immediate-reset-later-value")),
		}),
	}),
	resetCall,
	resetTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(resetProof.alias_depth == 1 and resetProof.definition_count == 1, "current loop prefix did not bound immediate invocation")

local innerLoopTarget = declaration("innerLoopTarget", "immediate-inner-loop-target")
local innerLoopCall = callExpression(innerLoopTarget, "immediate-inner-loop-call")
local _, innerLoopInvocation = invocationFromBody({
	whileStatement("immediate-inner-loop", {
		callStatement(innerLoopCall, "immediate-inner-loop-call-statement"),
		assignmentValue(
			innerLoopTarget,
			"immediate-inner-loop-later-write",
			globalExpression("different_target", "immediate-inner-loop-later-value")
		),
	}),
}, "immediate-inner-loop", nil, nil)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(innerLoopTarget, "immediate-inner-loop-target-declaration"),
			assignment(innerLoopTarget, "immediate-inner-loop-current-write"),
			callStatement(innerLoopInvocation, "immediate-inner-loop-invocation-statement"),
		}),
		innerLoopCall,
		innerLoopTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has no feasible structured definition set")

local repeatedInvocationTarget = declaration("repeatedInvocationTarget", "immediate-repeated-invocation-target")
local repeatedInvocationCall = callExpression(repeatedInvocationTarget, "immediate-repeated-invocation-call")
local _, repeatedInvocation = invocationFromBody({
	callStatement(repeatedInvocationCall, "immediate-repeated-invocation-call-statement"),
	assignmentValue(
		repeatedInvocationTarget,
		"immediate-repeated-invocation-write",
		globalExpression("different_target", "immediate-repeated-invocation-value")
	),
}, "immediate-repeated-invocation", nil, nil)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(repeatedInvocationTarget, "immediate-repeated-invocation-target-declaration"),
			assignment(repeatedInvocationTarget, "immediate-repeated-invocation-current-write"),
			whileStatement("immediate-repeated-invocation-outer-loop", {
				callStatement(repeatedInvocation, "immediate-repeated-invocation-statement"),
			}),
		}),
		repeatedInvocationCall,
		repeatedInvocationTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has no feasible structured definition set")

local argumentTarget = declaration("argumentTarget", "immediate-argument-target")
local argumentCall = callExpression(argumentTarget, "immediate-argument-call")
local argumentMutator: Record = {
	type = "AstExprFunction",
	location = "immediate-argument-mutator-function",
	args = {},
	body = block({
		assignmentValue(
			argumentTarget,
			"immediate-argument-mutator-write",
			globalExpression("different_target", "immediate-argument-mutator-value")
		),
	}, "immediate-argument-mutator-body"),
}
local argumentMutatorHolder = declaration("argumentMutator", "immediate-argument-mutator-holder")
local argumentMutatorCall = callExpression(argumentMutatorHolder, "immediate-argument-mutator-call")
local _, argumentInvocation = invocationFromBody({
	callStatement(argumentCall, "immediate-argument-call-statement"),
}, "immediate-argument", nil, { argumentMutatorCall })
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(argumentTarget, "immediate-argument-target-declaration"),
			assignment(argumentTarget, "immediate-argument-current-write"),
			localStatement(
				argumentMutatorHolder,
				"immediate-argument-mutator-declaration",
				argumentMutator
			),
			callStatement(argumentInvocation, "immediate-argument-invocation-statement"),
		}),
		argumentCall,
		argumentTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "has no feasible structured definition set")

local selectorTarget = declaration("unresolved_selector", "immediate-selector-target")
local selectorInnerCall = callExpression(selectorTarget, "immediate-selector-inner-call")
local _, selectorOuterCall = immediateInvocation(selectorInnerCall, "immediate-selector", nil)
local selectorProof = TargetRecovery.verify(document({
	callStatement(selectorOuterCall, "immediate-selector-outer-statement"),
}), "abc", {
	source_sha256 = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
	call_site_count = 2,
	unresolved_call_count = 1,
	lowered_unresolved_call_count = 1,
	unresolved_target_selectors = { { kind = "local_name", value = "unresolved_selector" } },
	detail = "selected callee identity remains unresolved",
	evidence = {
		kind = "structural_derivation",
		locator = "fixture:immediate-selector-boundary",
		digest = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
	},
} :: any)
assert(selectorProof.by_call_location[selectorInnerCall.location] ~= nil, "selector lost the nested target call")
assert(selectorProof.by_call_location[selectorOuterCall.location] == nil, "selector entered a deferred function body")
