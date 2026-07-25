--!strict

local Support = require("./temporal_test_support")
local InvocationSupport = require("./temporal_invocation_test_support")

type Record = Support.Record
type BindingKind = InvocationSupport.BindingKind
type AliasBindingKind = InvocationSupport.AliasBindingKind

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

local appendAliasBinding = InvocationSupport.appendAliasBinding
local appendFunctionBinding = InvocationSupport.appendFunctionBinding
local differentTarget = InvocationSupport.differentTarget
local localInvocation = InvocationSupport.localInvocation
local readInvocation = InvocationSupport.readInvocation

local authenticatedOrigin: Record = { kind = "environment", name = "authenticated_target" }

local function expectProof(documentValue: Record, call: Record, target: Record, location: string)
	local proof = verifyOrigin(documentValue, call, target, authenticatedOrigin)
	assert(proof.definition_location == location, `{location} synchronous capture chain stayed unbounded`)
end

local function expectOriginFailure(documentValue: Record, call: Record, target: Record)
	local location = target.location
	assert(type(location) == "string" and location ~= "")
	expectFailure(function()
		verifyOrigin(documentValue, call, target, authenticatedOrigin)
	end, "temporal target place " .. location)
end

local function capturedDocument(
	prefix: string,
	holderBinding: BindingKind,
	aliasDepth: number,
	aliasBinding: AliasBindingKind,
	callerDepth: number,
	wrapped: boolean,
	typeOnlyHolderUse: boolean?
): (Record, Record, Record)
	assert(callerDepth >= 1)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-holder-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
	}
	appendFunctionBinding(
		body,
		holder,
		functionValue,
		prefix .. "-holder",
		holderBinding ~= "local_function" and wrapped,
		holderBinding
	)
	if typeOnlyHolderUse == true then
		table.insert(body, {
			type = "AstStatTypeAlias",
			location = prefix .. "-type-alias",
			value = {
				type = "AstTypeTypeof",
				expr = localExpression(holder, prefix .. "-type-only-holder-use"),
			},
		})
	end
	local callee = holder
	for index = 1, aliasDepth do
		callee = appendAliasBinding(body, callee, `{prefix}-alias-{index}`, wrapped, aliasBinding)
	end
	local _, callerInvocation = invocationFromBody({
		callStatement(localInvocation(callee, prefix .. "-captured-call", wrapped), prefix .. "-captured-statement"),
	}, prefix .. "-caller-1", nil, nil)
	for index = 2, callerDepth do
		_, callerInvocation = invocationFromBody({
			callStatement(callerInvocation, `{prefix}-caller-{index - 1}-statement`),
		}, `{prefix}-caller-{index}`, nil, nil)
	end
	table.insert(body, callStatement(callerInvocation, prefix .. "-outer-caller-statement"))
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local function expectCapturedSuccess(
	prefix: string,
	holderBinding: BindingKind,
	aliasDepth: number,
	aliasBinding: AliasBindingKind,
	callerDepth: number,
	wrapped: boolean
)
	local documentValue, call, target = capturedDocument(
		prefix,
		holderBinding,
		aliasDepth,
		aliasBinding,
		callerDepth,
		wrapped
	)
	expectProof(documentValue, call, target, prefix .. "-current")
end

expectCapturedSuccess("capture-local", "local", 0, "local", 1, true)
expectCapturedSuccess("capture-local-function", "local_function", 0, "local", 1, false)
expectCapturedSuccess("capture-assignment", "assignment", 0, "local", 1, true)
expectCapturedSuccess("capture-multi-level", "local", 0, "local", 3, true)
expectCapturedSuccess("capture-mixed-alias", "assignment", 2, "assignment", 2, true)
expectCapturedSuccess("capture-depth-64", "local", 0, "local", 63, false)

local typeOnlyDocument, typeOnlyCall, typeOnlyTarget = capturedDocument(
	"capture-type-only-use",
	"local",
	0,
	"local",
	1,
	false,
	true
)
expectProof(typeOnlyDocument, typeOnlyCall, typeOnlyTarget, "capture-type-only-use-current")

local excessiveDocument, excessiveCall, excessiveTarget = capturedDocument(
	"capture-depth-65",
	"local",
	0,
	"local",
	64,
	false
)
expectOriginFailure(excessiveDocument, excessiveCall, excessiveTarget)

local function boundCallerDocument(prefix: string, callerBinding: BindingKind): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local holderFunction, _ = readInvocation(call, prefix .. "-holder-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local caller = declaration(prefix .. "Caller", prefix .. "-caller")
	local callerFunction, _ = invocationFromBody({
		callStatement(localInvocation(holder, prefix .. "-holder-call", false), prefix .. "-holder-statement"),
	}, prefix .. "-caller-function", nil, nil)
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration", holderFunction),
	}
	appendFunctionBinding(body, caller, callerFunction, prefix .. "-caller", false, callerBinding)
	table.insert(body, callStatement(localInvocation(caller, prefix .. "-caller-call", false), prefix .. "-caller-statement"))
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local function expectBoundCallerSuccess(prefix: string, binding: BindingKind)
	local documentValue, call, target = boundCallerDocument(prefix, binding)
	expectProof(documentValue, call, target, prefix .. "-current")
end

expectBoundCallerSuccess("capture-bound-local", "local")
expectBoundCallerSuccess("capture-bound-local-function", "local_function")
expectBoundCallerSuccess("capture-bound-assignment", "assignment")

local function internalWriteDocument(prefix: string, writeFirst: boolean): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local holderFunction, _ = readInvocation(call, prefix .. "-holder-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local holderCall = callStatement(localInvocation(holder, prefix .. "-holder-call", false), prefix .. "-holder-statement")
	local write = assignmentValue(target, prefix .. "-inner-write", differentTarget(prefix .. "-inner-value"))
	local callerBody = if writeFirst then { write, holderCall } else { holderCall, write }
	local _, callerInvocation = invocationFromBody(callerBody, prefix .. "-caller", nil, nil)
	return document({
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration", holderFunction),
		callStatement(callerInvocation, prefix .. "-caller-statement"),
	}), call, target
end

local afterDocument, afterCall, afterTarget = internalWriteDocument("capture-inner-after", false)
expectProof(afterDocument, afterCall, afterTarget, "capture-inner-after-current")
local beforeDocument, beforeCall, beforeTarget = internalWriteDocument("capture-inner-before", true)
expectOriginFailure(beforeDocument, beforeCall, beforeTarget)

local argumentTarget = declaration("capture-argumentTarget", "capture-argument-target")
local argumentCall = callExpression(argumentTarget, "capture-argument-read")
local argumentHolderFunction, _ = readInvocation(argumentCall, "capture-argument-holder-function")
local argumentHolder = declaration("capture-argumentHolder", "capture-argument-holder")
local _, argumentMutation = invocationFromBody({
	assignmentValue(argumentTarget, "capture-argument-write", differentTarget("capture-argument-value")),
}, "capture-argument-mutation", nil, nil)
local _, argumentCaller = invocationFromBody({
	callStatement(
		localInvocation(argumentHolder, "capture-argument-holder-call", false),
		"capture-argument-holder-statement"
	),
}, "capture-argument-caller", nil, { argumentMutation })
expectOriginFailure(
	document({
		localStatement(argumentTarget, "capture-argument-target-declaration"),
		assignment(argumentTarget, "capture-argument-current"),
		localStatement(argumentHolder, "capture-argument-holder-declaration", argumentHolderFunction),
		callStatement(argumentCaller, "capture-argument-caller-statement"),
	}),
	argumentCall,
	argumentTarget
)

local calleeArgumentTarget = declaration("capture-calleeArgumentTarget", "capture-callee-argument-target")
local calleeArgumentCall = callExpression(calleeArgumentTarget, "capture-callee-argument-read")
local calleeArgumentHolderFunction, _ = readInvocation(calleeArgumentCall, "capture-callee-argument-holder-function")
local calleeArgumentHolder = declaration("capture-calleeArgumentHolder", "capture-callee-argument-holder")
local _, calleeArgumentMutation = invocationFromBody({
	assignmentValue(
		calleeArgumentTarget,
		"capture-callee-argument-write",
		differentTarget("capture-callee-argument-value")
	),
}, "capture-callee-argument-mutation", nil, nil)
local calleeArgumentInvocation = localInvocation(calleeArgumentHolder, "capture-callee-argument-holder-call", false)
calleeArgumentInvocation.args = { calleeArgumentMutation }
local _, calleeArgumentCaller = invocationFromBody({
	callStatement(calleeArgumentInvocation, "capture-callee-argument-holder-statement"),
}, "capture-callee-argument-caller", nil, nil)
expectOriginFailure(
	document({
		localStatement(calleeArgumentTarget, "capture-callee-argument-target-declaration"),
		assignment(calleeArgumentTarget, "capture-callee-argument-current"),
		localStatement(
			calleeArgumentHolder,
			"capture-callee-argument-holder-declaration",
			calleeArgumentHolderFunction
		),
		callStatement(calleeArgumentCaller, "capture-callee-argument-caller-statement"),
	}),
	calleeArgumentCall,
	calleeArgumentTarget
)

local function callerModeDocument(prefix: string, mode: string): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local holderFunction, _ = readInvocation(call, prefix .. "-holder-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local caller = declaration(prefix .. "Caller", prefix .. "-caller")
	local callerBody = {
		callStatement(localInvocation(holder, prefix .. "-holder-call", false), prefix .. "-holder-statement"),
	}
	if mode == "recursive" then
		table.insert(callerBody, callStatement(localInvocation(caller, prefix .. "-recursive-call", false), prefix .. "-recursive-statement"))
	end
	local callerFunction, directCallerInvocation = invocationFromBody(callerBody, prefix .. "-caller-function", nil, nil)
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration", holderFunction),
	}
	if mode == "repeated-direct" then
		table.insert(body, whileStatement(prefix .. "-loop", {
			callStatement(directCallerInvocation, prefix .. "-caller-statement"),
		}))
	else
		if mode == "recursive" then
			table.insert(body, InvocationSupport.localFunctionStatement(caller, callerFunction, prefix .. "-caller-declaration"))
		else
			table.insert(body, localStatement(caller, prefix .. "-caller-declaration", callerFunction))
		end
		local callerInvocation = localInvocation(caller, prefix .. "-caller-call", false)
		if mode == "uninvoked" then
			-- The function value is retained but never executed.
		elseif mode == "second-call" then
			table.insert(body, callStatement(callerInvocation, prefix .. "-first-caller-statement"))
			table.insert(
				body,
				callStatement(localInvocation(caller, prefix .. "-second-caller-call", false), prefix .. "-second-caller-statement")
			)
		elseif mode == "passed" then
			table.insert(body, callStatement({
				type = "AstExprCall",
				location = prefix .. "-consumer",
				func = globalExpression("consume", prefix .. "-consumer-callee"),
				args = { localExpression(caller, prefix .. "-argument") },
				self = false,
			}, prefix .. "-consumer-statement"))
		elseif mode == "repeated" then
			table.insert(body, whileStatement(prefix .. "-loop", {
				callStatement(callerInvocation, prefix .. "-caller-statement"),
			}))
		else
			assert(mode == "recursive")
			table.insert(body, callStatement(callerInvocation, prefix .. "-caller-statement"))
		end
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

for _, mode in { "uninvoked", "passed", "repeated", "recursive" } do
	local prefix = "capture-caller-" .. mode
	local documentValue, call, target = callerModeDocument(prefix, mode)
	expectOriginFailure(documentValue, call, target)
end

local secondCallerDocument, secondCallerCall, secondCallerTarget = callerModeDocument(
	"capture-caller-second-call",
	"second-call"
)
expectProof(secondCallerDocument, secondCallerCall, secondCallerTarget, "capture-caller-second-call-current")

local repeatedDirectDocument, repeatedDirectCall, repeatedDirectTarget = callerModeDocument(
	"capture-caller-repeated-direct",
	"repeated-direct"
)
expectProof(
	repeatedDirectDocument,
	repeatedDirectCall,
	repeatedDirectTarget,
	"capture-caller-repeated-direct-current"
)

local function assignmentOrderDocument(prefix: string, mode: string): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local holderFunction, _ = readInvocation(call, prefix .. "-holder-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local alias = declaration(prefix .. "Alias", prefix .. "-alias")
	local _, callerInvocation = invocationFromBody({
		callStatement(
			localInvocation(if mode == "alias-after-call" or mode == "snapshot-before-definition" then alias else holder, prefix .. "-call", false),
			prefix .. "-call-statement"
		),
	}, prefix .. "-caller", nil, nil)
	local holderAssignment = assignmentValue(holder, prefix .. "-holder-assignment", holderFunction)
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration"),
	}
	if mode == "assignment-after-call" then
		table.insert(body, callStatement(callerInvocation, prefix .. "-caller-statement"))
		table.insert(body, holderAssignment)
	elseif mode == "different-block" then
		table.insert(body, block({ holderAssignment }, prefix .. "-assignment-block"))
		table.insert(body, callStatement(callerInvocation, prefix .. "-caller-statement"))
	elseif mode == "snapshot-before-definition" then
		table.insert(body, localStatement(alias, prefix .. "-alias-declaration", localExpression(holder, prefix .. "-alias-source")))
		table.insert(body, holderAssignment)
		table.insert(body, callStatement(callerInvocation, prefix .. "-caller-statement"))
	else
		assert(mode == "alias-after-call")
		table.insert(body, holderAssignment)
		table.insert(body, localStatement(alias, prefix .. "-alias-declaration"))
		table.insert(body, callStatement(callerInvocation, prefix .. "-caller-statement"))
		table.insert(body, assignmentValue(alias, prefix .. "-alias-assignment", localExpression(holder, prefix .. "-alias-source")))
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

for _, mode in { "assignment-after-call", "different-block", "snapshot-before-definition", "alias-after-call" } do
	local prefix = "capture-order-" .. mode
	local documentValue, call, target = assignmentOrderDocument(prefix, mode)
	expectOriginFailure(documentValue, call, target)
end
