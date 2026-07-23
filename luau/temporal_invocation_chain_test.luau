--!strict

local Support = require("./temporal_test_support")
local InvocationSupport = require("./temporal_invocation_test_support")
local TemporalTargetIdentity = require("./temporal_target_identity")

type Record = Support.Record
type BindingKind = InvocationSupport.BindingKind
type AliasBindingKind = InvocationSupport.AliasBindingKind

local assignment = Support.assignment
local assignmentValue = Support.assignmentValue
local block = Support.block
local branchStatement = Support.branchStatement
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

local authenticatedOrigin: Record = { kind = "environment", name = "authenticated_target" }

local aliasedFutureWriteChain = InvocationSupport.aliasedFutureWriteChain
local differentTarget = InvocationSupport.differentTarget
local futureWriteChain = InvocationSupport.futureWriteChain
local localFunctionStatement = InvocationSupport.localFunctionStatement
local localInvocation = InvocationSupport.localInvocation
local readInvocation = InvocationSupport.readInvocation
local singleUseFutureWriteChain = InvocationSupport.singleUseFutureWriteChain
local wrappedExpression = InvocationSupport.wrappedExpression

local function expectBoundClosureFailure(bindingKind: BindingKind, mode: string)
	assert(bindingKind ~= "local")
	local prefix = `read-chain-{bindingKind}-{mode}`
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-call")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local functionBody = { callStatement(call, prefix .. "-read-statement") }
	if mode == "recursive" then
		table.insert(
			functionBody,
			callStatement(localInvocation(holder, prefix .. "-recursive", false), prefix .. "-recursive-statement")
		)
	end
	local functionValue, _ = invocationFromBody(functionBody, prefix .. "-function", nil, nil)
	local outerBody: { Record } = {}
	local holderAssignment = assignmentValue(holder, prefix .. "-assignment", functionValue)
	if bindingKind == "local_function" then
		table.insert(outerBody, localFunctionStatement(holder, functionValue, prefix .. "-declaration"))
	else
		table.insert(outerBody, localStatement(holder, prefix .. "-declaration"))
		if mode == "call-before-assignment" then
			table.insert(
				outerBody,
				callStatement(localInvocation(holder, prefix .. "-early", false), prefix .. "-early-statement")
			)
			table.insert(outerBody, holderAssignment)
		elseif mode == "different-block" then
			table.insert(outerBody, block({ holderAssignment }, prefix .. "-assignment-block"))
		else
			table.insert(outerBody, holderAssignment)
		end
	end
	if mode == "passed" then
		table.insert(outerBody, callStatement({
			type = "AstExprCall",
			location = prefix .. "-consumer",
			func = globalExpression("consume", prefix .. "-consumer-callee"),
			args = { localExpression(holder, prefix .. "-argument") },
			self = false,
		}, prefix .. "-consumer-statement"))
	elseif mode == "captured" then
		local _, caller = invocationFromBody({
			callStatement(
				localInvocation(holder, prefix .. "-captured-call", false),
				prefix .. "-captured-statement"
			),
		}, prefix .. "-caller", nil, nil)
		table.insert(outerBody, callStatement(caller, prefix .. "-caller-statement"))
	elseif mode == "repeated" then
		table.insert(outerBody, whileStatement(prefix .. "-loop", {
			callStatement(localInvocation(holder, prefix .. "-loop-call", false), prefix .. "-loop-call-statement"),
		}))
	elseif mode == "call-before-assignment" then
		assert(bindingKind == "assignment")
	elseif mode == "different-block" then
		assert(bindingKind == "assignment")
		table.insert(
			outerBody,
			callStatement(localInvocation(holder, prefix .. "-entry", false), prefix .. "-entry-statement")
		)
	else
		assert(mode == "recursive")
		table.insert(
			outerBody,
			callStatement(localInvocation(holder, prefix .. "-entry", false), prefix .. "-entry-statement")
		)
	end
	table.insert(outerBody, assignmentValue(target, prefix .. "-write", differentTarget(prefix .. "-value")))
	local _, outer = invocationFromBody(outerBody, prefix .. "-outer", nil, nil)
	expectFailure(function()
		verifyOrigin(
			document({
				localStatement(target, prefix .. "-target-declaration"),
				assignment(target, prefix .. "-current"),
				callStatement(outer, prefix .. "-outer-statement"),
			}),
			call,
			target,
			authenticatedOrigin
		)
	end, "has no feasible structured definition set")
end

local laterTarget = declaration("laterTarget", "read-chain-later-target")
local laterCall = callExpression(laterTarget, "read-chain-later-call")
local _, laterInner = readInvocation(laterCall, "read-chain-later-inner")
local _, laterOuter = invocationFromBody({
	callStatement(laterInner, "read-chain-later-inner-statement"),
	assignmentValue(laterTarget, "read-chain-later-write", differentTarget("read-chain-later-value")),
}, "read-chain-later-outer", nil, nil)
local laterProof = verifyOrigin(
	document({
		localStatement(laterTarget, "read-chain-later-declaration"),
		assignment(laterTarget, "read-chain-later-current"),
		callStatement(laterOuter, "read-chain-later-outer-statement"),
	}),
	laterCall,
	laterTarget,
	authenticatedOrigin
)
assert(laterProof.definition_location == "read-chain-later-current", "intermediate future write stayed committed")

local guardTarget = declaration("guardTarget", "read-chain-guard-target")
local guardCall = callExpression(guardTarget, "read-chain-guard-call")
local _, guardInner = readInvocation(guardCall, "read-chain-guard-inner")
local guardStatement: Record = {
	type = "AstStatIf",
	location = "read-chain-guard-if",
	condition = guardInner,
	thenbody = block({
		assignmentValue(guardTarget, "read-chain-guard-then-write", differentTarget("read-chain-guard-then-value")),
	}, "read-chain-guard-then"),
	elsebody = block({
		assignmentValue(guardTarget, "read-chain-guard-else-write", differentTarget("read-chain-guard-else-value")),
	}, "read-chain-guard-else"),
}
local _, guardOuter = invocationFromBody({ guardStatement }, "read-chain-guard-outer", nil, nil)
local guardProof = verifyOrigin(
	document({
		localStatement(guardTarget, "read-chain-guard-declaration"),
		assignment(guardTarget, "read-chain-guard-current"),
		callStatement(guardOuter, "read-chain-guard-outer-statement"),
	}),
	guardCall,
	guardTarget,
	authenticatedOrigin
)
assert(guardProof.definition_count == 1, "guarded intermediate future writes stayed committed")

local boundedTarget = declaration("boundedTarget", "read-chain-bounded-target")
local boundedCall = callExpression(boundedTarget, "read-chain-bounded-call")
local boundedInvocation = futureWriteChain(
	boundedTarget,
	boundedCall,
	"read-chain-bounded",
	TemporalTargetIdentity.maxInvocationDepth
)
local boundedProof = verifyOrigin(
	document({
		localStatement(boundedTarget, "read-chain-bounded-declaration"),
		assignment(boundedTarget, "read-chain-bounded-current"),
		callStatement(boundedInvocation, "read-chain-bounded-invocation-statement"),
		assignmentValue(boundedTarget, "read-chain-bounded-root-write", differentTarget("read-chain-bounded-root-value")),
	}),
	boundedCall,
	boundedTarget,
	authenticatedOrigin
)
assert(boundedProof.definition_location == "read-chain-bounded-current", "maximum read invocation chain was rejected")

local excessiveTarget = declaration("excessiveTarget", "read-chain-excessive-target")
local excessiveCall = callExpression(excessiveTarget, "read-chain-excessive-call")
local excessiveInvocation = futureWriteChain(
	excessiveTarget,
	excessiveCall,
	"read-chain-excessive",
	TemporalTargetIdentity.maxInvocationDepth + 1
)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(excessiveTarget, "read-chain-excessive-declaration"),
			assignment(excessiveTarget, "read-chain-excessive-current"),
			callStatement(excessiveInvocation, "read-chain-excessive-invocation-statement"),
		}),
		excessiveCall,
		excessiveTarget,
		authenticatedOrigin
	)
end, "has no feasible structured definition set")

local localTarget = declaration("localTarget", "read-chain-local-target")
local localCall = callExpression(localTarget, "read-chain-local-call")
local localOuter = singleUseFutureWriteChain(localTarget, localCall, "read-chain-local", 2, true, "local")
local localProof = verifyOrigin(
	document({
		localStatement(localTarget, "read-chain-local-declaration"),
		assignment(localTarget, "read-chain-local-current"),
		callStatement(localOuter, "read-chain-local-outer-statement"),
	}),
	localCall,
	localTarget,
	authenticatedOrigin
)
assert(localProof.definition_location == "read-chain-local-current", "single-use local invocation was not bounded")

local mixedBoundedTarget = declaration("mixedBoundedTarget", "read-chain-mixed-bounded-target")
local mixedBoundedCall = callExpression(mixedBoundedTarget, "read-chain-mixed-bounded-call")
local mixedBoundedInvocation = singleUseFutureWriteChain(
	mixedBoundedTarget,
	mixedBoundedCall,
	"read-chain-mixed-bounded",
	TemporalTargetIdentity.maxInvocationDepth,
	false,
	"local"
)
local mixedBoundedProof = verifyOrigin(
	document({
		localStatement(mixedBoundedTarget, "read-chain-mixed-bounded-declaration"),
		assignment(mixedBoundedTarget, "read-chain-mixed-bounded-current"),
		callStatement(mixedBoundedInvocation, "read-chain-mixed-bounded-statement"),
	}),
	mixedBoundedCall,
	mixedBoundedTarget,
	authenticatedOrigin
)
assert(mixedBoundedProof.definition_count == 1, "maximum mixed local invocation chain was rejected")

local mixedExcessiveTarget = declaration("mixedExcessiveTarget", "read-chain-mixed-excessive-target")
local mixedExcessiveCall = callExpression(mixedExcessiveTarget, "read-chain-mixed-excessive-call")
local mixedExcessiveInvocation = singleUseFutureWriteChain(
	mixedExcessiveTarget,
	mixedExcessiveCall,
	"read-chain-mixed-excessive",
	TemporalTargetIdentity.maxInvocationDepth + 1,
	false,
	"local"
)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(mixedExcessiveTarget, "read-chain-mixed-excessive-declaration"),
			assignment(mixedExcessiveTarget, "read-chain-mixed-excessive-current"),
			callStatement(mixedExcessiveInvocation, "read-chain-mixed-excessive-statement"),
		}),
		mixedExcessiveCall,
		mixedExcessiveTarget,
		authenticatedOrigin
	)
end, "has no feasible structured definition set")

local localFunctionTarget = declaration("localFunctionTarget", "read-chain-local-function-target")
local localFunctionCall = callExpression(localFunctionTarget, "read-chain-local-function-call")
local localFunctionValue, _ = readInvocation(localFunctionCall, "read-chain-local-function-value")
local localFunctionHolder = declaration("localFunctionHolder", "read-chain-local-function-holder")
local localFunctionProof = verifyOrigin(
	document({
		localStatement(localFunctionTarget, "read-chain-local-function-target-declaration"),
		assignment(localFunctionTarget, "read-chain-local-function-current"),
		localFunctionStatement(localFunctionHolder, localFunctionValue, "read-chain-local-function-declaration"),
		callStatement(
			localInvocation(localFunctionHolder, "read-chain-local-function-invocation", true),
			"read-chain-local-function-invocation-statement"
		),
		assignmentValue(
			localFunctionTarget,
			"read-chain-local-function-write",
			differentTarget("read-chain-local-function-value")
		),
	}),
	localFunctionCall,
	localFunctionTarget,
	authenticatedOrigin
)
assert(
	localFunctionProof.definition_location == "read-chain-local-function-current",
	"single-use local function was not bounded"
)

local localFunctionBoundedTarget = declaration("localFunctionBoundedTarget", "read-chain-local-function-bounded-target")
local localFunctionBoundedCall = callExpression(localFunctionBoundedTarget, "read-chain-local-function-bounded-call")
local localFunctionBoundedInvocation = singleUseFutureWriteChain(
	localFunctionBoundedTarget,
	localFunctionBoundedCall,
	"read-chain-local-function-bounded",
	TemporalTargetIdentity.maxInvocationDepth,
	false,
	"local_function"
)
local localFunctionBoundedProof = verifyOrigin(
	document({
		localStatement(localFunctionBoundedTarget, "read-chain-local-function-bounded-declaration"),
		assignment(localFunctionBoundedTarget, "read-chain-local-function-bounded-current"),
		callStatement(localFunctionBoundedInvocation, "read-chain-local-function-bounded-statement"),
	}),
	localFunctionBoundedCall,
	localFunctionBoundedTarget,
	authenticatedOrigin
)
assert(localFunctionBoundedProof.definition_count == 1, "maximum mixed local function chain was rejected")

local localFunctionExcessiveTarget = declaration("localFunctionExcessiveTarget", "read-chain-local-function-excessive-target")
local localFunctionExcessiveCall = callExpression(localFunctionExcessiveTarget, "read-chain-local-function-excessive-call")
local localFunctionExcessiveInvocation = singleUseFutureWriteChain(
	localFunctionExcessiveTarget,
	localFunctionExcessiveCall,
	"read-chain-local-function-excessive",
	TemporalTargetIdentity.maxInvocationDepth + 1,
	false,
	"local_function"
)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(localFunctionExcessiveTarget, "read-chain-local-function-excessive-declaration"),
			assignment(localFunctionExcessiveTarget, "read-chain-local-function-excessive-current"),
			callStatement(localFunctionExcessiveInvocation, "read-chain-local-function-excessive-statement"),
		}),
		localFunctionExcessiveCall,
		localFunctionExcessiveTarget,
		authenticatedOrigin
	)
end, "has no feasible structured definition set")

for _, mode in { "recursive", "passed", "repeated" } do
	expectBoundClosureFailure("local_function", mode)
end

local assignedTarget = declaration("assignedTarget", "read-chain-assigned-target")
local assignedCall = callExpression(assignedTarget, "read-chain-assigned-call")
local assignedFunction, _ = readInvocation(assignedCall, "read-chain-assigned-function")
local assignedHolder = declaration("assignedHolder", "read-chain-assigned-holder")
local assignedProof = verifyOrigin(
	document({
		localStatement(assignedTarget, "read-chain-assigned-target-declaration"),
		assignment(assignedTarget, "read-chain-assigned-current"),
		localStatement(assignedHolder, "read-chain-assigned-holder-declaration"),
		assignmentValue(
			assignedHolder,
			"read-chain-assigned-holder-assignment",
			wrappedExpression(assignedFunction, "read-chain-assigned-initializer")
		),
		callStatement(localInvocation(assignedHolder, "read-chain-assigned-invocation", true), "read-chain-assigned-statement"),
		assignmentValue(assignedTarget, "read-chain-assigned-write", differentTarget("read-chain-assigned-value")),
	}),
	assignedCall,
	assignedTarget,
	authenticatedOrigin
)
assert(assignedProof.definition_location == "read-chain-assigned-current", "single reaching assignment was not bounded")

local assignedBoundedTarget = declaration("assignedBoundedTarget", "read-chain-assigned-bounded-target")
local assignedBoundedCall = callExpression(assignedBoundedTarget, "read-chain-assigned-bounded-call")
local assignedBoundedInvocation = singleUseFutureWriteChain(
	assignedBoundedTarget,
	assignedBoundedCall,
	"read-chain-assigned-bounded",
	TemporalTargetIdentity.maxInvocationDepth,
	false,
	"assignment"
)
local assignedBoundedProof = verifyOrigin(
	document({
		localStatement(assignedBoundedTarget, "read-chain-assigned-bounded-declaration"),
		assignment(assignedBoundedTarget, "read-chain-assigned-bounded-current"),
		callStatement(assignedBoundedInvocation, "read-chain-assigned-bounded-statement"),
	}),
	assignedBoundedCall,
	assignedBoundedTarget,
	authenticatedOrigin
)
assert(assignedBoundedProof.definition_count == 1, "maximum mixed assignment invocation chain was rejected")

local assignedExcessiveTarget = declaration("assignedExcessiveTarget", "read-chain-assigned-excessive-target")
local assignedExcessiveCall = callExpression(assignedExcessiveTarget, "read-chain-assigned-excessive-call")
local assignedExcessiveInvocation = singleUseFutureWriteChain(
	assignedExcessiveTarget,
	assignedExcessiveCall,
	"read-chain-assigned-excessive",
	TemporalTargetIdentity.maxInvocationDepth + 1,
	false,
	"assignment"
)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(assignedExcessiveTarget, "read-chain-assigned-excessive-declaration"),
			assignment(assignedExcessiveTarget, "read-chain-assigned-excessive-current"),
			callStatement(assignedExcessiveInvocation, "read-chain-assigned-excessive-statement"),
		}),
		assignedExcessiveCall,
		assignedExcessiveTarget,
		authenticatedOrigin
	)
end, "has no feasible structured definition set")

for _, mode in {
	"recursive",
	"passed",
	"repeated",
	"call-before-assignment",
	"different-block",
} do
	expectBoundClosureFailure("assignment", mode)
end

local function expectAliasSuccess(
	sourceBinding: BindingKind,
	aliasBinding: AliasBindingKind,
	aliasDepth: number,
	wrapped: boolean,
	prefix: string
)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local outer = aliasedFutureWriteChain(target, call, prefix, aliasDepth, sourceBinding, aliasBinding, wrapped)
	local proof = verifyOrigin(
		document({
			localStatement(target, prefix .. "-target-declaration"),
			assignment(target, prefix .. "-current"),
			callStatement(outer, prefix .. "-outer-statement"),
		}),
		call,
		target,
		authenticatedOrigin
	)
	assert(proof.definition_location == prefix .. "-current", `{prefix} alias chain was not bounded`)
end

expectAliasSuccess("local", "local", 1, true, "read-chain-alias-local")
expectAliasSuccess("local_function", "local", 2, true, "read-chain-alias-local-function")
expectAliasSuccess("assignment", "local", 2, true, "read-chain-alias-assigned-source")
expectAliasSuccess("assignment", "assignment", 2, true, "read-chain-alias-assigned-transfer")
expectAliasSuccess(
	"local",
	"assignment",
	TemporalTargetIdentity.maxInvocationDepth,
	false,
	"read-chain-alias-bounded"
)

local aliasExcessiveTarget = declaration("aliasExcessiveTarget", "read-chain-alias-excessive-target")
local aliasExcessiveCall = callExpression(aliasExcessiveTarget, "read-chain-alias-excessive-read")
local aliasExcessiveOuter = aliasedFutureWriteChain(
	aliasExcessiveTarget,
	aliasExcessiveCall,
	"read-chain-alias-excessive",
	TemporalTargetIdentity.maxInvocationDepth + 1,
	"local",
	"local",
	false
)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(aliasExcessiveTarget, "read-chain-alias-excessive-declaration"),
			assignment(aliasExcessiveTarget, "read-chain-alias-excessive-current"),
			callStatement(aliasExcessiveOuter, "read-chain-alias-excessive-statement"),
		}),
		aliasExcessiveCall,
		aliasExcessiveTarget,
		authenticatedOrigin
	)
end, "has no feasible structured definition set")

local function expectAliasFailure(mode: string)
	local prefix = "read-chain-alias-" .. mode
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local alias = declaration(prefix .. "Alias", prefix .. "-alias")
	local body: { Record } = {}
	local aliasCall = localInvocation(alias, prefix .. "-call", false)
	local transfer = assignmentValue(holder, prefix .. "-holder-definition", functionValue)
	local aliasTransfer = assignmentValue(
		alias,
		prefix .. "-alias-transfer",
		localExpression(holder, prefix .. "-alias-source")
	)
	if mode == "transfer-before-definition" then
		table.insert(body, localStatement(holder, prefix .. "-holder-declaration"))
		table.insert(body, localStatement(alias, prefix .. "-alias-declaration"))
		table.insert(body, aliasTransfer)
		table.insert(body, transfer)
		table.insert(body, callStatement(aliasCall, prefix .. "-call-statement"))
	else
		table.insert(body, localStatement(holder, prefix .. "-holder-declaration", functionValue))
		if mode == "call-before-transfer" then
			table.insert(body, localStatement(alias, prefix .. "-alias-declaration"))
			table.insert(body, callStatement(aliasCall, prefix .. "-call-statement"))
			table.insert(body, aliasTransfer)
		elseif mode == "different-block" then
			table.insert(body, localStatement(alias, prefix .. "-alias-declaration"))
			table.insert(body, block({ aliasTransfer }, prefix .. "-transfer-block"))
			table.insert(body, callStatement(aliasCall, prefix .. "-call-statement"))
		elseif mode == "branch-only" then
			table.insert(body, localStatement(alias, prefix .. "-alias-declaration"))
			table.insert(body, branchStatement(prefix .. "-branch", { aliasTransfer }, nil))
			table.insert(body, callStatement(aliasCall, prefix .. "-call-statement"))
		else
			table.insert(
				body,
				localStatement(alias, prefix .. "-alias-declaration", localExpression(holder, prefix .. "-alias-source"))
			)
			if mode == "extra-write" then
				table.insert(body, assignmentValue(alias, prefix .. "-write", differentTarget(prefix .. "-write-value")))
				table.insert(body, callStatement(aliasCall, prefix .. "-call-statement"))
			elseif mode == "passed" then
				table.insert(body, callStatement({
					type = "AstExprCall",
					location = prefix .. "-consumer",
					func = globalExpression("consume", prefix .. "-consumer-callee"),
					args = { localExpression(alias, prefix .. "-argument") },
					self = false,
				}, prefix .. "-consumer-statement"))
			elseif mode == "captured" then
				local _, caller = invocationFromBody({
					callStatement(aliasCall, prefix .. "-captured-call-statement"),
				}, prefix .. "-caller", nil, nil)
				table.insert(body, callStatement(caller, prefix .. "-caller-statement"))
			elseif mode == "repeated" then
				table.insert(body, whileStatement(prefix .. "-loop", {
					callStatement(aliasCall, prefix .. "-loop-call-statement"),
				}))
			elseif mode == "recursive" then
				table.insert(functionValue.body.body, callStatement(aliasCall, prefix .. "-recursive-statement"))
				table.insert(body, callStatement(localInvocation(alias, prefix .. "-entry-call", false), prefix .. "-entry-statement"))
			else
				assert(mode == "cycle-shaped")
				table.insert(body, assignmentValue(holder, prefix .. "-cycle-write", localExpression(alias, prefix .. "-cycle-source")))
				table.insert(body, callStatement(aliasCall, prefix .. "-call-statement"))
			end
		end
	end
	table.insert(body, assignmentValue(target, prefix .. "-target-write", differentTarget(prefix .. "-target-value")))
	local _, outer = invocationFromBody(body, prefix .. "-outer", nil, nil)
	expectFailure(function()
		verifyOrigin(
			document({
				localStatement(target, prefix .. "-target-declaration"),
				assignment(target, prefix .. "-current"),
				callStatement(outer, prefix .. "-outer-statement"),
			}),
			call,
			target,
			authenticatedOrigin
		)
	end, "has no feasible structured definition set")
end

for _, mode in {
	"transfer-before-definition",
	"call-before-transfer",
	"different-block",
	"branch-only",
	"extra-write",
	"passed",
	"repeated",
	"recursive",
	"cycle-shaped",
} do
	expectAliasFailure(mode)
end

local secondUseTarget = declaration("secondUseTarget", "read-chain-second-use-target")
local secondUseCall = callExpression(secondUseTarget, "read-chain-second-use-call")
local secondUseFunction, _ = readInvocation(secondUseCall, "read-chain-second-use-function")
local secondUseHolder = declaration("secondUseHolder", "read-chain-second-use-holder")
local _, secondUseOuter = invocationFromBody({
	localStatement(secondUseHolder, "read-chain-second-use-holder-declaration", secondUseFunction),
	callStatement(localInvocation(secondUseHolder, "read-chain-second-use-first", false), "read-chain-second-use-first-statement"),
	callStatement(localInvocation(secondUseHolder, "read-chain-second-use-second", false), "read-chain-second-use-second-statement"),
	assignmentValue(secondUseTarget, "read-chain-second-use-write", differentTarget("read-chain-second-use-value")),
}, "read-chain-second-use-outer", nil, nil)
local secondUseProof = verifyOrigin(
	document({
		localStatement(secondUseTarget, "read-chain-second-use-declaration"),
		assignment(secondUseTarget, "read-chain-second-use-current"),
		callStatement(secondUseOuter, "read-chain-second-use-outer-statement"),
	}),
	secondUseCall,
	secondUseTarget,
	authenticatedOrigin
)
assert(secondUseProof.definition_location == "read-chain-second-use-current", "finite exact calls stayed unbounded")

local reassignedTarget = declaration("reassignedTarget", "read-chain-reassigned-target")
local reassignedCall = callExpression(reassignedTarget, "read-chain-reassigned-call")
local reassignedFunction, _ = readInvocation(reassignedCall, "read-chain-reassigned-function")
local reassignedHolder = declaration("reassignedHolder", "read-chain-reassigned-holder")
local _, reassignedOuter = invocationFromBody({
	localStatement(reassignedHolder, "read-chain-reassigned-holder-declaration", reassignedFunction),
	callStatement(localInvocation(reassignedHolder, "read-chain-reassigned-call-site", false), "read-chain-reassigned-call-statement"),
	assignmentValue(reassignedHolder, "read-chain-reassigned-holder-write", differentTarget("read-chain-reassigned-holder-value")),
	assignmentValue(reassignedTarget, "read-chain-reassigned-write", differentTarget("read-chain-reassigned-value")),
}, "read-chain-reassigned-outer", nil, nil)
local reassignedProof = verifyOrigin(
	document({
		localStatement(reassignedTarget, "read-chain-reassigned-declaration"),
		assignment(reassignedTarget, "read-chain-reassigned-current"),
		callStatement(reassignedOuter, "read-chain-reassigned-outer-statement"),
	}),
	reassignedCall,
	reassignedTarget,
	authenticatedOrigin
)
assert(reassignedProof.definition_location == "read-chain-reassigned-current", "linear callee kill stayed unknown")

local passedTarget = declaration("passedTarget", "read-chain-passed-target")
local passedCall = callExpression(passedTarget, "read-chain-passed-call")
local passedFunction, _ = readInvocation(passedCall, "read-chain-passed-function")
local passedHolder = declaration("passedHolder", "read-chain-passed-holder")
local passedConsumer: Record = {
	type = "AstExprCall",
	location = "read-chain-passed-consumer",
	func = globalExpression("consume", "read-chain-passed-consumer-callee"),
	args = { localExpression(passedHolder, "read-chain-passed-argument") },
	self = false,
}
local _, passedOuter = invocationFromBody({
	localStatement(passedHolder, "read-chain-passed-holder-declaration", passedFunction),
	callStatement(passedConsumer, "read-chain-passed-consumer-statement"),
	assignmentValue(passedTarget, "read-chain-passed-write", differentTarget("read-chain-passed-value")),
}, "read-chain-passed-outer", nil, nil)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(passedTarget, "read-chain-passed-declaration"),
			assignment(passedTarget, "read-chain-passed-current"),
			callStatement(passedOuter, "read-chain-passed-outer-statement"),
		}),
		passedCall,
		passedTarget,
		authenticatedOrigin
	)
end, "has no feasible structured definition set")

local capturedTarget = declaration("capturedTarget", "read-chain-captured-target")
local capturedCall = callExpression(capturedTarget, "read-chain-captured-call")
local capturedFunction, _ = readInvocation(capturedCall, "read-chain-captured-function")
local capturedHolder = declaration("capturedHolder", "read-chain-captured-holder")
local _, capturedCaller = invocationFromBody({
	callStatement(localInvocation(capturedHolder, "read-chain-captured-holder-call", false), "read-chain-captured-holder-statement"),
}, "read-chain-captured-caller", nil, nil)
local _, capturedOuter = invocationFromBody({
	localStatement(capturedHolder, "read-chain-captured-holder-declaration", capturedFunction),
	callStatement(capturedCaller, "read-chain-captured-caller-statement"),
	assignmentValue(capturedTarget, "read-chain-captured-write", differentTarget("read-chain-captured-value")),
}, "read-chain-captured-outer", nil, nil)
local capturedProof = verifyOrigin(
	document({
		localStatement(capturedTarget, "read-chain-captured-declaration"),
		assignment(capturedTarget, "read-chain-captured-current"),
		callStatement(capturedOuter, "read-chain-captured-outer-statement"),
	}),
	capturedCall,
	capturedTarget,
	authenticatedOrigin
)
assert(capturedProof.definition_location == "read-chain-captured-current", "synchronous captured call stayed unbounded")

local repeatedLocalTarget = declaration("repeatedLocalTarget", "read-chain-repeated-local-target")
local repeatedLocalCall = callExpression(repeatedLocalTarget, "read-chain-repeated-local-call")
local repeatedLocalFunction, _ = invocationFromBody({
	callStatement(repeatedLocalCall, "read-chain-repeated-local-read-statement"),
	assignmentValue(
		repeatedLocalTarget,
		"read-chain-repeated-local-write",
		differentTarget("read-chain-repeated-local-value")
	),
}, "read-chain-repeated-local-function", nil, nil)
local repeatedLocalHolder = declaration("repeatedLocalHolder", "read-chain-repeated-local-holder")
local _, repeatedLocalOuter = invocationFromBody({
	localStatement(repeatedLocalHolder, "read-chain-repeated-local-holder-declaration", repeatedLocalFunction),
	whileStatement("read-chain-repeated-local-loop", {
		callStatement(
			localInvocation(repeatedLocalHolder, "read-chain-repeated-local-call-site", false),
			"read-chain-repeated-local-call-statement"
		),
	}),
}, "read-chain-repeated-local-outer", nil, nil)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(repeatedLocalTarget, "read-chain-repeated-local-declaration"),
			assignment(repeatedLocalTarget, "read-chain-repeated-local-current"),
			callStatement(repeatedLocalOuter, "read-chain-repeated-local-outer-statement"),
		}),
		repeatedLocalCall,
		repeatedLocalTarget,
		authenticatedOrigin
	)
end, "has no feasible structured definition set")

local earlierTarget = declaration("earlierTarget", "read-chain-earlier-target")
local earlierCall = callExpression(earlierTarget, "read-chain-earlier-call")
local _, earlierInner = readInvocation(earlierCall, "read-chain-earlier-inner")
local _, earlierOuter = invocationFromBody({
	assignmentValue(earlierTarget, "read-chain-earlier-write", differentTarget("read-chain-earlier-value")),
	callStatement(earlierInner, "read-chain-earlier-inner-statement"),
}, "read-chain-earlier-outer", nil, nil)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(earlierTarget, "read-chain-earlier-declaration"),
			assignment(earlierTarget, "read-chain-earlier-current"),
			callStatement(earlierOuter, "read-chain-earlier-outer-statement"),
		}),
		earlierCall,
		earlierTarget,
		authenticatedOrigin
	)
end, "has no feasible structured definition set")

local repeatedTarget = declaration("repeatedTarget", "read-chain-repeated-target")
local repeatedCall = callExpression(repeatedTarget, "read-chain-repeated-call")
local _, repeatedInner = invocationFromBody({
	callStatement(repeatedCall, "read-chain-repeated-read-statement"),
	assignmentValue(repeatedTarget, "read-chain-repeated-write", differentTarget("read-chain-repeated-value")),
}, "read-chain-repeated-inner", nil, nil)
local _, repeatedOuter = invocationFromBody({
	whileStatement("read-chain-repeated-loop", {
		callStatement(repeatedInner, "read-chain-repeated-inner-statement"),
	}),
}, "read-chain-repeated-outer", nil, nil)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(repeatedTarget, "read-chain-repeated-declaration"),
			assignment(repeatedTarget, "read-chain-repeated-current"),
			callStatement(repeatedOuter, "read-chain-repeated-outer-statement"),
		}),
		repeatedCall,
		repeatedTarget,
		authenticatedOrigin
	)
end, "has no feasible structured definition set")

local storedTarget = declaration("storedTarget", "read-chain-stored-target")
local storedCall = callExpression(storedTarget, "read-chain-stored-call")
local storedFunction, _ = readInvocation(storedCall, "read-chain-stored-inner")
local storedHolder = declaration("storedHolder", "read-chain-stored-holder")
local storedInvocation: Record = {
	type = "AstExprCall",
	location = "read-chain-stored-invocation",
	func = localExpression(storedHolder, "read-chain-stored-callee"),
	args = {},
	self = false,
}
local _, storedOuter = invocationFromBody({
	localStatement(storedHolder, "read-chain-stored-holder-declaration", storedFunction),
	callStatement(storedInvocation, "read-chain-stored-invocation-statement"),
	assignmentValue(storedTarget, "read-chain-stored-write", differentTarget("read-chain-stored-value")),
}, "read-chain-stored-outer", nil, nil)
local storedProof = verifyOrigin(
	document({
		localStatement(storedTarget, "read-chain-stored-declaration"),
		assignment(storedTarget, "read-chain-stored-current"),
		callStatement(storedOuter, "read-chain-stored-outer-statement"),
	}),
	storedCall,
	storedTarget,
	authenticatedOrigin
)
assert(storedProof.definition_location == "read-chain-stored-current", "single-use stored closure stayed unbounded")

local argumentTarget = declaration("argumentTarget", "read-chain-argument-target")
local argumentCall = callExpression(argumentTarget, "read-chain-argument-call")
local _, argumentRead = readInvocation(argumentCall, "read-chain-argument-read")
local _, argumentWrite = invocationFromBody({
	assignmentValue(argumentTarget, "read-chain-argument-write", differentTarget("read-chain-argument-value")),
}, "read-chain-argument-mutation", nil, nil)
local argumentConsumer: Record = {
	type = "AstExprCall",
	location = "read-chain-argument-consumer",
	func = globalExpression("consume", "read-chain-argument-consumer-callee"),
	args = { argumentRead, argumentWrite },
	self = false,
}
local _, argumentOuter = invocationFromBody({
	callStatement(argumentConsumer, "read-chain-argument-consumer-statement"),
}, "read-chain-argument-outer", nil, nil)
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(argumentTarget, "read-chain-argument-declaration"),
			assignment(argumentTarget, "read-chain-argument-current"),
			callStatement(argumentOuter, "read-chain-argument-outer-statement"),
		}),
		argumentCall,
		argumentTarget,
		authenticatedOrigin
	)
end, "has no feasible structured definition set")
