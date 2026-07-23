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

local appendAliasBinding = InvocationSupport.appendAliasBinding
local appendFunctionBinding = InvocationSupport.appendFunctionBinding
local differentTarget = InvocationSupport.differentTarget
local localFunctionStatement = InvocationSupport.localFunctionStatement
local localInvocation = InvocationSupport.localInvocation
local readInvocation = InvocationSupport.readInvocation

local authenticatedOrigin: Record = { kind = "environment", name = "authenticated_target" }

local function expectProof(documentValue: Record, call: Record, target: Record, location: string)
	local proof = verifyOrigin(documentValue, call, target, authenticatedOrigin)
	assert(proof.definition_count == 1, `{location} produced a definition set`)
	assert(proof.definition_location == location, `{location} did not remain the common invocation definition`)
end

local function expectOriginFailure(documentValue: Record, call: Record, target: Record)
	local location = target.location
	assert(type(location) == "string" and location ~= "")
	expectFailure(function()
		verifyOrigin(documentValue, call, target, authenticatedOrigin)
	end, "temporal target place " .. location)
end

local function multiSiteDocument(
	prefix: string,
	siteCount: number,
	sourceBinding: BindingKind,
	aliasDepth: number,
	aliasBinding: AliasBindingKind,
	wrapped: boolean,
	writeAfterSite: number?
): (Record, Record, Record)
	assert(siteCount >= 2)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
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
		sourceBinding ~= "local_function" and wrapped,
		sourceBinding
	)
	local callee = holder
	for aliasIndex = 1, aliasDepth do
		callee = appendAliasBinding(body, callee, `{prefix}-alias-{aliasIndex}`, wrapped, aliasBinding)
	end
	for siteIndex = 1, siteCount do
		table.insert(
			body,
			callStatement(
				localInvocation(callee, `{prefix}-call-{siteIndex}`, wrapped),
				`{prefix}-call-{siteIndex}-statement`
			)
		)
		if writeAfterSite == siteIndex then
			table.insert(
				body,
				assignmentValue(target, prefix .. "-between-write", differentTarget(prefix .. "-between-value"))
			)
		end
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local sequentialDocument, sequentialCall, sequentialTarget = multiSiteDocument(
	"invoke-set-sequential",
	2,
	"local",
	0,
	"local",
	true,
	nil
)
expectProof(sequentialDocument, sequentialCall, sequentialTarget, "invoke-set-sequential-current")

local aliasDocument, aliasCall, aliasTarget = multiSiteDocument(
	"invoke-set-alias",
	2,
	"assignment",
	2,
	"assignment",
	true,
	nil
)
expectProof(aliasDocument, aliasCall, aliasTarget, "invoke-set-alias-current")

local betweenDocument, betweenCall, betweenTarget = multiSiteDocument(
	"invoke-set-between",
	2,
	"local_function",
	0,
	"local",
	false,
	1
)
expectOriginFailure(betweenDocument, betweenCall, betweenTarget)

local boundedDocument, boundedCall, boundedTarget = multiSiteDocument(
	"invoke-set-bounded",
	TemporalTargetIdentity.maxInvocationSites,
	"local",
	0,
	"local",
	false,
	nil
)
expectProof(boundedDocument, boundedCall, boundedTarget, "invoke-set-bounded-current")

local excessiveDocument, excessiveCall, excessiveTarget = multiSiteDocument(
	"invoke-set-excessive",
	TemporalTargetIdentity.maxInvocationSites + 1,
	"local",
	0,
	"local",
	false,
	nil
)
expectOriginFailure(excessiveDocument, excessiveCall, excessiveTarget)

local function branchDocument(prefix: string, divergent: boolean): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local thenBody: { Record } = {}
	local elseBody: { Record } = {}
	if divergent then
		table.insert(thenBody, assignment(target, prefix .. "-then-current"))
		table.insert(elseBody, assignment(target, prefix .. "-else-current"))
	end
	table.insert(
		thenBody,
		callStatement(localInvocation(holder, prefix .. "-then-call", false), prefix .. "-then-statement")
	)
	table.insert(
		elseBody,
		callStatement(localInvocation(holder, prefix .. "-else-call", false), prefix .. "-else-statement")
	)
	return document({
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration", functionValue),
		branchStatement(prefix, thenBody, block(elseBody, prefix .. "-else")),
		assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")),
	}), call, target
end

local branchSetDocument, branchSetCall, branchSetTarget = branchDocument("invoke-set-branch", false)
expectProof(branchSetDocument, branchSetCall, branchSetTarget, "invoke-set-branch-current")

local divergentDocument, divergentCall, divergentTarget = branchDocument("invoke-set-divergent", true)
expectOriginFailure(divergentDocument, divergentCall, divergentTarget)

local function boundCallerDocument(prefix: string, escapeCaller: boolean): (Record, Record, Record)
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
	appendFunctionBinding(body, caller, callerFunction, prefix .. "-caller", true, "assignment")
	local callerAlias = appendAliasBinding(body, caller, prefix .. "-caller-alias", true, "local")
	if escapeCaller then
		table.insert(body, callStatement({
			type = "AstExprCall",
			location = prefix .. "-consumer",
			func = globalExpression("consume", prefix .. "-consumer-callee"),
			args = { localExpression(callerAlias, prefix .. "-argument") },
			self = false,
		}, prefix .. "-consumer-statement"))
	else
		for siteIndex = 1, 2 do
			table.insert(
				body,
				callStatement(
					localInvocation(callerAlias, `{prefix}-caller-call-{siteIndex}`, true),
					`{prefix}-caller-statement-{siteIndex}`
				)
			)
		end
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local callerDocument, callerCall, callerTarget = boundCallerDocument("invoke-set-caller", false)
expectProof(callerDocument, callerCall, callerTarget, "invoke-set-caller-current")

local callerEscapeDocument, callerEscapeCall, callerEscapeTarget = boundCallerDocument(
	"invoke-set-caller-escape",
	true
)
expectOriginFailure(callerEscapeDocument, callerEscapeCall, callerEscapeTarget)

local argumentTarget = declaration("invokeSetArgumentTarget", "invoke-set-argument-target")
local argumentCall = callExpression(argumentTarget, "invoke-set-argument-read")
local argumentFunction, _ = readInvocation(argumentCall, "invoke-set-argument-function")
local argumentHolder = declaration("invokeSetArgumentHolder", "invoke-set-argument-holder")
local _, argumentMutation = invocationFromBody({
	assignmentValue(argumentTarget, "invoke-set-argument-write", differentTarget("invoke-set-argument-value")),
}, "invoke-set-argument-mutation", nil, nil)
local mutatingInvocation = localInvocation(argumentHolder, "invoke-set-argument-call-2", false)
mutatingInvocation.args = { argumentMutation }
expectOriginFailure(
	document({
		localStatement(argumentTarget, "invoke-set-argument-target-declaration"),
		assignment(argumentTarget, "invoke-set-argument-current"),
		localStatement(argumentHolder, "invoke-set-argument-holder-declaration", argumentFunction),
		callStatement(localInvocation(argumentHolder, "invoke-set-argument-call-1", false), "invoke-set-argument-statement-1"),
		callStatement(mutatingInvocation, "invoke-set-argument-statement-2"),
	}),
	argumentCall,
	argumentTarget
)

local escapeTarget = declaration("invokeSetEscapeTarget", "invoke-set-escape-target")
local escapeCall = callExpression(escapeTarget, "invoke-set-escape-read")
local escapeFunction, _ = readInvocation(escapeCall, "invoke-set-escape-function")
local escapeHolder = declaration("invokeSetEscapeHolder", "invoke-set-escape-holder")
expectOriginFailure(
	document({
		localStatement(escapeTarget, "invoke-set-escape-target-declaration"),
		assignment(escapeTarget, "invoke-set-escape-current"),
		localStatement(escapeHolder, "invoke-set-escape-holder-declaration", escapeFunction),
		callStatement(localInvocation(escapeHolder, "invoke-set-escape-call", false), "invoke-set-escape-statement"),
		callStatement({
			type = "AstExprCall",
			location = "invoke-set-escape-consumer",
			func = globalExpression("consume", "invoke-set-escape-consumer-callee"),
			args = { localExpression(escapeHolder, "invoke-set-escape-argument") },
			self = false,
		}, "invoke-set-escape-consumer-statement"),
		assignmentValue(escapeTarget, "invoke-set-escape-write", differentTarget("invoke-set-escape-value")),
	}),
	escapeCall,
	escapeTarget
)

local recursiveTarget = declaration("invokeSetRecursiveTarget", "invoke-set-recursive-target")
local recursiveCall = callExpression(recursiveTarget, "invoke-set-recursive-read")
local recursiveHolder = declaration("invokeSetRecursiveHolder", "invoke-set-recursive-holder")
local recursiveFunction, _ = invocationFromBody({
	callStatement(recursiveCall, "invoke-set-recursive-read-statement"),
	callStatement(localInvocation(recursiveHolder, "invoke-set-recursive-self-call", false), "invoke-set-recursive-self-statement"),
}, "invoke-set-recursive-function", nil, nil)
expectOriginFailure(
	document({
		localStatement(recursiveTarget, "invoke-set-recursive-target-declaration"),
		assignment(recursiveTarget, "invoke-set-recursive-current"),
		localFunctionStatement(recursiveHolder, recursiveFunction, "invoke-set-recursive-holder-declaration"),
		callStatement(localInvocation(recursiveHolder, "invoke-set-recursive-entry", false), "invoke-set-recursive-entry-statement"),
		assignmentValue(recursiveTarget, "invoke-set-recursive-write", differentTarget("invoke-set-recursive-value")),
	}),
	recursiveCall,
	recursiveTarget
)

local repeatedTarget = declaration("invokeSetRepeatedTarget", "invoke-set-repeated-target")
local repeatedCall = callExpression(repeatedTarget, "invoke-set-repeated-read")
local repeatedFunction, _ = readInvocation(repeatedCall, "invoke-set-repeated-function")
local repeatedHolder = declaration("invokeSetRepeatedHolder", "invoke-set-repeated-holder")
expectOriginFailure(
	document({
		localStatement(repeatedTarget, "invoke-set-repeated-target-declaration"),
		assignment(repeatedTarget, "invoke-set-repeated-current"),
		localStatement(repeatedHolder, "invoke-set-repeated-holder-declaration", repeatedFunction),
		whileStatement("invoke-set-repeated-loop", {
			callStatement(localInvocation(repeatedHolder, "invoke-set-repeated-call", false), "invoke-set-repeated-statement"),
		}),
		assignmentValue(repeatedTarget, "invoke-set-repeated-write", differentTarget("invoke-set-repeated-value")),
	}),
	repeatedCall,
	repeatedTarget
)
