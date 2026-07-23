--!strict

local Support = require("./temporal_test_support")
local InvocationSupport = require("./temporal_invocation_test_support")

type Record = Support.Record
type BindingKind = InvocationSupport.BindingKind

local assignment = Support.assignment
local assignmentValue = Support.assignmentValue
local block = Support.block
local branchStatement = Support.branchStatement
local callExpression = Support.callExpression
local callStatement = Support.callStatement
local declaration = Support.declaration
local document = Support.document
local expectFailure = Support.expectFailure
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
	assert(proof.definition_count == 1, `{location} callee kill produced a definition set`)
	assert(proof.definition_location == location, `{location} callee kill lost the original invocation`)
end

local function expectOriginFailure(documentValue: Record, call: Record, target: Record)
	local location = target.location
	assert(type(location) == "string" and location ~= "")
	expectFailure(function()
		verifyOrigin(documentValue, call, target, authenticatedOrigin)
	end, "temporal target place " .. location)
end

local function directKillDocument(prefix: string, bindingKind: BindingKind): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
	}
	appendFunctionBinding(body, holder, functionValue, prefix .. "-holder", false, bindingKind)
	table.insert(body, callStatement(localInvocation(holder, prefix .. "-call", false), prefix .. "-call-statement"))
	table.insert(body, assignmentValue(holder, prefix .. "-kill", differentTarget(prefix .. "-replacement")))
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local function expectDirectKill(prefix: string, bindingKind: BindingKind)
	local fixture, call, target = directKillDocument(prefix, bindingKind)
	expectProof(fixture, call, target, prefix .. "-current")
end

expectDirectKill("kill-direct-local", "local")
expectDirectKill("kill-direct-local-function", "local_function")
expectDirectKill("kill-direct-assignment", "assignment")

local aliasTarget = declaration("killAliasTarget", "kill-alias-target")
local aliasCall = callExpression(aliasTarget, "kill-alias-read")
local aliasFunction, _ = readInvocation(aliasCall, "kill-alias-function")
local aliasHolder = declaration("killAliasHolder", "kill-alias-holder")
local aliasOther = declaration("killAliasOther", "kill-alias-other")
local aliasBody: { Record } = {
	localStatement(aliasTarget, "kill-alias-target-declaration"),
	assignment(aliasTarget, "kill-alias-current"),
	localStatement(aliasHolder, "kill-alias-holder-declaration", aliasFunction),
	localStatement(aliasOther, "kill-alias-other-declaration"),
}
local firstAlias = appendAliasBinding(aliasBody, aliasHolder, "kill-alias-first", true, "local")
local secondAlias = appendAliasBinding(aliasBody, aliasHolder, "kill-alias-second", true, "assignment")
table.insert(aliasBody, callStatement(localInvocation(aliasHolder, "kill-alias-direct-call", false), "kill-alias-direct-statement"))
table.insert(aliasBody, {
	type = "AstStatAssign",
	location = "kill-alias-kill",
	vars = {
		localExpression(aliasHolder, "kill-alias-holder-kill-target"),
		localExpression(aliasOther, "kill-alias-other-kill-target"),
	},
	values = { differentTarget("kill-alias-replacement"), differentTarget("kill-alias-other-replacement") },
})
table.insert(aliasBody, assignmentValue(aliasHolder, "kill-alias-second-kill", differentTarget("kill-alias-second-replacement")))
table.insert(aliasBody, callStatement(localInvocation(firstAlias, "kill-alias-call-1", true), "kill-alias-statement-1"))
table.insert(aliasBody, callStatement(localInvocation(secondAlias, "kill-alias-call-2", true), "kill-alias-statement-2"))
table.insert(aliasBody, assignmentValue(aliasTarget, "kill-alias-future-write", differentTarget("kill-alias-future-value")))
expectProof(document(aliasBody), aliasCall, aliasTarget, "kill-alias-current")

local callerTarget = declaration("killCallerTarget", "kill-caller-target")
local callerCall = callExpression(callerTarget, "kill-caller-read")
local callerHolderFunction, _ = readInvocation(callerCall, "kill-caller-holder-function")
local callerHolder = declaration("killCallerHolder", "kill-caller-holder")
local caller = declaration("killCaller", "kill-caller")
local callerFunction, _ = invocationFromBody({
	callStatement(localInvocation(callerHolder, "kill-caller-holder-call", false), "kill-caller-holder-statement"),
}, "kill-caller-function", nil, nil)
expectProof(
	document({
		localStatement(callerTarget, "kill-caller-target-declaration"),
		assignment(callerTarget, "kill-caller-current"),
		localStatement(callerHolder, "kill-caller-holder-declaration", callerHolderFunction),
		localStatement(caller, "kill-caller-declaration", callerFunction),
		callStatement(localInvocation(caller, "kill-caller-call", false), "kill-caller-statement"),
		assignmentValue(caller, "kill-caller-kill", differentTarget("kill-caller-replacement")),
		assignmentValue(caller, "kill-caller-second-kill", differentTarget("kill-caller-second-replacement")),
		assignmentValue(callerTarget, "kill-caller-future-write", differentTarget("kill-caller-future-value")),
	}),
	callerCall,
	callerTarget,
	"kill-caller-current"
)

local function unreachableOriginal(prefix: string, aliasAfterKill: boolean): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration", functionValue),
		assignmentValue(holder, prefix .. "-kill", differentTarget(prefix .. "-replacement")),
	}
	local callee = holder
	if aliasAfterKill then
		callee = appendAliasBinding(body, holder, prefix .. "-alias", false, "local")
	end
	table.insert(body, callStatement(localInvocation(callee, prefix .. "-call", false), prefix .. "-call-statement"))
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local postKill, postKillCall, postKillTarget = unreachableOriginal("kill-post-call", false)
expectOriginFailure(postKill, postKillCall, postKillTarget)
local postAlias, postAliasCall, postAliasTarget = unreachableOriginal("kill-post-alias", true)
expectOriginFailure(postAlias, postAliasCall, postAliasTarget)

local predefinitionTarget = declaration("killPredefinitionTarget", "kill-predefinition-target")
local predefinitionCall = callExpression(predefinitionTarget, "kill-predefinition-read")
local predefinitionFunction, _ = readInvocation(predefinitionCall, "kill-predefinition-function")
local predefinitionHolder = declaration("killPredefinitionHolder", "kill-predefinition-holder")
expectProof(
	document({
		localStatement(predefinitionTarget, "kill-predefinition-target-declaration"),
		assignment(predefinitionTarget, "kill-predefinition-current"),
		localStatement(predefinitionHolder, "kill-predefinition-holder-declaration"),
		assignmentValue(predefinitionHolder, "kill-predefinition-early-write", differentTarget("kill-predefinition-early-value")),
		assignmentValue(predefinitionHolder, "kill-predefinition-definition", predefinitionFunction),
		callStatement(localInvocation(predefinitionHolder, "kill-predefinition-call", false), "kill-predefinition-statement"),
		assignmentValue(predefinitionTarget, "kill-predefinition-future-write", differentTarget("kill-predefinition-future-value")),
	}),
	predefinitionCall,
	predefinitionTarget,
	"kill-predefinition-current"
)

local function controlKill(prefix: string, mode: string): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local kill = assignmentValue(holder, prefix .. "-kill", differentTarget(prefix .. "-replacement"))
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration", functionValue),
		callStatement(localInvocation(holder, prefix .. "-call", false), prefix .. "-call-statement"),
	}
	if mode == "branch" then
		table.insert(body, branchStatement(prefix, { kill }, nil))
	elseif mode == "block" then
		table.insert(body, block({ kill }, prefix .. "-block"))
	else
		assert(mode == "repeated")
		table.insert(body, whileStatement(prefix .. "-loop", { kill }))
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

for _, mode in { "branch", "block", "repeated" } do
	local prefix = "kill-control-" .. mode
	local fixture, call, target = controlKill(prefix, mode)
	expectOriginFailure(fixture, call, target)
end

local multipleTarget = declaration("killMultipleTarget", "kill-multiple-target")
local multipleCall = callExpression(multipleTarget, "kill-multiple-read")
local multipleFunction, _ = readInvocation(multipleCall, "kill-multiple-function")
local multipleHolder = declaration("killMultipleHolder", "kill-multiple-holder")
expectProof(
	document({
		localStatement(multipleTarget, "kill-multiple-target-declaration"),
		assignment(multipleTarget, "kill-multiple-current"),
		localStatement(multipleHolder, "kill-multiple-holder-declaration", multipleFunction),
		callStatement(localInvocation(multipleHolder, "kill-multiple-call", false), "kill-multiple-statement"),
		assignmentValue(multipleHolder, "kill-multiple-first", differentTarget("kill-multiple-first-value")),
		assignmentValue(multipleHolder, "kill-multiple-second", differentTarget("kill-multiple-second-value")),
		assignmentValue(multipleTarget, "kill-multiple-future-write", differentTarget("kill-multiple-future-value")),
	}),
	multipleCall,
	multipleTarget,
	"kill-multiple-current"
)

local sameTarget = declaration("killSameTarget", "kill-same-target")
local sameCall = callExpression(sameTarget, "kill-same-read")
local sameFunction, _ = readInvocation(sameCall, "kill-same-function")
local sameHolder = declaration("killSameHolder", "kill-same-holder")
expectOriginFailure(
	document({
		localStatement(sameTarget, "kill-same-target-declaration"),
		assignment(sameTarget, "kill-same-current"),
		localStatement(sameHolder, "kill-same-holder-declaration", sameFunction),
		callStatement(localInvocation(sameHolder, "kill-same-call", false), "kill-same-statement"),
		assignmentValue(sameHolder, "kill-same-kill", localExpression(sameHolder, "kill-same-old-value")),
		assignmentValue(sameTarget, "kill-same-future-write", differentTarget("kill-same-future-value")),
	}),
	sameCall,
	sameTarget
)

local multiTarget = declaration("killMultiTarget", "kill-multi-target")
local multiCall = callExpression(multiTarget, "kill-multi-read")
local multiFunction, _ = readInvocation(multiCall, "kill-multi-function")
local multiHolder = declaration("killMultiHolder", "kill-multi-holder")
local multiOther = declaration("killMultiOther", "kill-multi-other")
expectProof(
	document({
		localStatement(multiTarget, "kill-multi-target-declaration"),
		assignment(multiTarget, "kill-multi-current"),
		localStatement(multiHolder, "kill-multi-holder-declaration", multiFunction),
		localStatement(multiOther, "kill-multi-other-declaration"),
		callStatement(localInvocation(multiHolder, "kill-multi-call", false), "kill-multi-statement"),
		{
			type = "AstStatAssign",
			location = "kill-multi-kill",
			vars = {
				localExpression(multiHolder, "kill-multi-holder-target"),
				localExpression(multiOther, "kill-multi-other-target"),
			},
			values = { differentTarget("kill-multi-holder-value"), differentTarget("kill-multi-other-value") },
		},
		{
			type = "AstStatAssign",
			location = "kill-multi-second-kill",
			vars = {
				localExpression(multiHolder, "kill-multi-second-holder-target"),
				localExpression(multiOther, "kill-multi-second-other-target"),
			},
			values = { differentTarget("kill-multi-second-holder-value"), differentTarget("kill-multi-second-other-value") },
		},
		assignmentValue(multiHolder, "kill-multi-scalar-kill", differentTarget("kill-multi-scalar-value")),
		assignmentValue(multiTarget, "kill-multi-future-write", differentTarget("kill-multi-future-value")),
	}),
	multiCall,
	multiTarget,
	"kill-multi-current"
)

local compoundTarget = declaration("killCompoundTarget", "kill-compound-target")
local compoundCall = callExpression(compoundTarget, "kill-compound-read")
local compoundFunction, _ = readInvocation(compoundCall, "kill-compound-function")
local compoundHolder = declaration("killCompoundHolder", "kill-compound-holder")
expectOriginFailure(
	document({
		localStatement(compoundTarget, "kill-compound-target-declaration"),
		assignment(compoundTarget, "kill-compound-current"),
		localStatement(compoundHolder, "kill-compound-holder-declaration", compoundFunction),
		callStatement(localInvocation(compoundHolder, "kill-compound-call", false), "kill-compound-statement"),
		{
			type = "AstStatCompoundAssign",
			location = "kill-compound-kill",
			var = localExpression(compoundHolder, "kill-compound-target"),
			op = "Add",
			value = differentTarget("kill-compound-value"),
		},
		assignmentValue(compoundTarget, "kill-compound-future-write", differentTarget("kill-compound-future-value")),
	}),
	compoundCall,
	compoundTarget
)

local capturedTarget = declaration("killCapturedTarget", "kill-captured-target")
local capturedCall = callExpression(capturedTarget, "kill-captured-read")
local capturedFunction, _ = readInvocation(capturedCall, "kill-captured-function")
local capturedHolder = declaration("killCapturedHolder", "kill-captured-holder")
local capturedOther = declaration("killCapturedOther", "kill-captured-other")
local _, capturedCaller = invocationFromBody({
	callStatement(localInvocation(capturedHolder, "kill-captured-call", false), "kill-captured-statement"),
}, "kill-captured-caller", nil, nil)
expectProof(
	document({
		localStatement(capturedTarget, "kill-captured-target-declaration"),
		assignment(capturedTarget, "kill-captured-current"),
		localStatement(capturedHolder, "kill-captured-holder-declaration", capturedFunction),
		localStatement(capturedOther, "kill-captured-other-declaration"),
		callStatement(capturedCaller, "kill-captured-caller-statement"),
		{
			type = "AstStatAssign",
			location = "kill-captured-kill",
			vars = {
				localExpression(capturedHolder, "kill-captured-holder-kill-target"),
				localExpression(capturedOther, "kill-captured-other-kill-target"),
			},
			values = {
				differentTarget("kill-captured-replacement"),
				differentTarget("kill-captured-other-replacement"),
			},
		},
		assignmentValue(capturedTarget, "kill-captured-future-write", differentTarget("kill-captured-future-value")),
	}),
	capturedCall,
	capturedTarget,
	"kill-captured-current"
)

local function capturedVersionDocument(prefix: string, callsBefore: number, callsAfter: number): (Record, Record, Record)
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
		localStatement(holder, prefix .. "-holder-declaration"),
		assignmentValue(holder, prefix .. "-holder-old", differentTarget(prefix .. "-holder-old-value")),
		assignmentValue(holder, prefix .. "-holder-definition", holderFunction),
		localStatement(caller, prefix .. "-caller-declaration", callerFunction),
	}
	for index = 1, callsBefore do
		table.insert(
			body,
			callStatement(localInvocation(caller, `{prefix}-before-call-{index}`, false), `{prefix}-before-statement-{index}`)
		)
	end
	table.insert(body, assignmentValue(holder, prefix .. "-holder-kill", differentTarget(prefix .. "-holder-new-value")))
	table.insert(body, assignmentValue(holder, prefix .. "-holder-next", differentTarget(prefix .. "-holder-next-value")))
	for index = 1, callsAfter do
		table.insert(
			body,
			callStatement(localInvocation(caller, `{prefix}-after-call-{index}`, false), `{prefix}-after-statement-{index}`)
		)
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local capturedBefore, capturedBeforeCall, capturedBeforeTarget = capturedVersionDocument("version-captured-before", 2, 0)
expectProof(capturedBefore, capturedBeforeCall, capturedBeforeTarget, "version-captured-before-current")
local capturedAfter, capturedAfterCall, capturedAfterTarget = capturedVersionDocument("version-captured-after", 0, 1)
expectOriginFailure(capturedAfter, capturedAfterCall, capturedAfterTarget)
local capturedMixed, capturedMixedCall, capturedMixedTarget = capturedVersionDocument("version-captured-mixed", 1, 1)
expectOriginFailure(capturedMixed, capturedMixedCall, capturedMixedTarget)

local nestedCapturedTarget = declaration("versionNestedCapturedTarget", "version-nested-captured-target")
local nestedCapturedCall = callExpression(nestedCapturedTarget, "version-nested-captured-read")
local nestedCapturedFunction, _ = readInvocation(nestedCapturedCall, "version-nested-captured-function")
local nestedCapturedHolder = declaration("versionNestedCapturedHolder", "version-nested-captured-holder")
local _, nestedCapturedInner = invocationFromBody({
	callStatement(
		localInvocation(nestedCapturedHolder, "version-nested-captured-holder-call", false),
		"version-nested-captured-holder-statement"
	),
}, "version-nested-captured-inner", nil, nil)
local _, nestedCapturedOuter = invocationFromBody({
	callStatement(nestedCapturedInner, "version-nested-captured-inner-statement"),
}, "version-nested-captured-outer", nil, nil)
expectProof(
	document({
		localStatement(nestedCapturedTarget, "version-nested-captured-target-declaration"),
		assignment(nestedCapturedTarget, "version-nested-captured-current"),
		localStatement(nestedCapturedHolder, "version-nested-captured-holder-declaration", nestedCapturedFunction),
		callStatement(nestedCapturedOuter, "version-nested-captured-outer-statement"),
		assignmentValue(
			nestedCapturedHolder,
			"version-nested-captured-kill",
			differentTarget("version-nested-captured-replacement")
		),
		assignmentValue(
			nestedCapturedTarget,
			"version-nested-captured-future-write",
			differentTarget("version-nested-captured-future-value")
		),
	}),
	nestedCapturedCall,
	nestedCapturedTarget,
	"version-nested-captured-current"
)

local sameEntryTarget = declaration("versionSameEntryTarget", "version-same-entry-target")
local sameEntryCall = callExpression(sameEntryTarget, "version-same-entry-read")
local sameEntryFunction, _ = readInvocation(sameEntryCall, "version-same-entry-function")
local sameEntryHolder = declaration("versionSameEntryHolder", "version-same-entry-holder")
local _, sameEntryCaller = invocationFromBody({
	callStatement(localInvocation(sameEntryHolder, "version-same-entry-holder-call", false), "version-same-entry-holder-statement"),
}, "version-same-entry-caller", nil, nil)
expectOriginFailure(
	document({
		localStatement(sameEntryTarget, "version-same-entry-target-declaration"),
		assignment(sameEntryTarget, "version-same-entry-current"),
		localStatement(sameEntryHolder, "version-same-entry-holder-declaration", sameEntryFunction),
		assignmentValue(sameEntryHolder, "version-same-entry-kill", sameEntryCaller),
		assignmentValue(sameEntryTarget, "version-same-entry-future-write", differentTarget("version-same-entry-future-value")),
	}),
	sameEntryCall,
	sameEntryTarget
)

local multiReadTarget = declaration("killMultiReadTarget", "kill-multi-read-target")
local multiReadCall = callExpression(multiReadTarget, "kill-multi-read-read")
local multiReadFunction, _ = readInvocation(multiReadCall, "kill-multi-read-function")
local multiReadHolder = declaration("killMultiReadHolder", "kill-multi-read-holder")
local multiReadOther = declaration("killMultiReadOther", "kill-multi-read-other")
expectOriginFailure(
	document({
		localStatement(multiReadTarget, "kill-multi-read-target-declaration"),
		assignment(multiReadTarget, "kill-multi-read-current"),
		localStatement(multiReadHolder, "kill-multi-read-holder-declaration", multiReadFunction),
		localStatement(multiReadOther, "kill-multi-read-other-declaration"),
		callStatement(localInvocation(multiReadHolder, "kill-multi-read-call", false), "kill-multi-read-statement"),
		{
			type = "AstStatAssign",
			location = "kill-multi-read-kill",
			vars = {
				localExpression(multiReadHolder, "kill-multi-read-holder-target"),
				localExpression(multiReadOther, "kill-multi-read-other-target"),
			},
			values = {
				localExpression(multiReadHolder, "kill-multi-read-old-value"),
				differentTarget("kill-multi-read-other-value"),
			},
		},
		assignmentValue(multiReadTarget, "kill-multi-read-future-write", differentTarget("kill-multi-read-future-value")),
	}),
	multiReadCall,
	multiReadTarget
)

local duplicateTarget = declaration("killDuplicateTarget", "kill-duplicate-target")
local duplicateCall = callExpression(duplicateTarget, "kill-duplicate-read")
local duplicateFunction, _ = readInvocation(duplicateCall, "kill-duplicate-function")
local duplicateHolder = declaration("killDuplicateHolder", "kill-duplicate-holder")
expectOriginFailure(
	document({
		localStatement(duplicateTarget, "kill-duplicate-target-declaration"),
		assignment(duplicateTarget, "kill-duplicate-current"),
		localStatement(duplicateHolder, "kill-duplicate-holder-declaration", duplicateFunction),
		callStatement(localInvocation(duplicateHolder, "kill-duplicate-call", false), "kill-duplicate-statement"),
		{
			type = "AstStatAssign",
			location = "kill-duplicate-kill",
			vars = {
				localExpression(duplicateHolder, "kill-duplicate-target-1"),
				localExpression(duplicateHolder, "kill-duplicate-target-2"),
			},
			values = { differentTarget("kill-duplicate-value-1"), differentTarget("kill-duplicate-value-2") },
		},
		assignmentValue(duplicateTarget, "kill-duplicate-future-write", differentTarget("kill-duplicate-future-value")),
	}),
	duplicateCall,
	duplicateTarget
)

local malformedTarget = declaration("killMalformedTarget", "kill-malformed-target")
local malformedCall = callExpression(malformedTarget, "kill-malformed-read")
local malformedFunction, _ = readInvocation(malformedCall, "kill-malformed-function")
local malformedHolder = declaration("killMalformedHolder", "kill-malformed-holder")
expectOriginFailure(
	document({
		localStatement(malformedTarget, "kill-malformed-target-declaration"),
		assignment(malformedTarget, "kill-malformed-current"),
		localStatement(malformedHolder, "kill-malformed-holder-declaration", malformedFunction),
		callStatement(localInvocation(malformedHolder, "kill-malformed-call", false), "kill-malformed-statement"),
		{
			type = "AstStatAssign",
			location = "kill-malformed-kill",
			vars = { localExpression(malformedHolder, "kill-malformed-target-use") },
			values = "malformed",
		},
		assignmentValue(malformedTarget, "kill-malformed-future-write", differentTarget("kill-malformed-future-value")),
	}),
	malformedCall,
	malformedTarget
)

local indexedTarget = declaration("killIndexedTarget", "kill-indexed-target")
local indexedCall = callExpression(indexedTarget, "kill-indexed-read")
local indexedFunction, _ = readInvocation(indexedCall, "kill-indexed-function")
local indexedHolder = declaration("killIndexedHolder", "kill-indexed-holder")
local indexedTable = declaration("killIndexedTable", "kill-indexed-table")
expectOriginFailure(
	document({
		localStatement(indexedTarget, "kill-indexed-target-declaration"),
		assignment(indexedTarget, "kill-indexed-current"),
		localStatement(indexedHolder, "kill-indexed-holder-declaration", indexedFunction),
		localStatement(indexedTable, "kill-indexed-table-declaration"),
		callStatement(localInvocation(indexedHolder, "kill-indexed-call", false), "kill-indexed-statement"),
		{
			type = "AstStatAssign",
			location = "kill-indexed-kill",
			vars = {
				localExpression(indexedHolder, "kill-indexed-holder-target"),
				{
					type = "AstExprIndexName",
					location = "kill-indexed-other-target",
					expr = localExpression(indexedTable, "kill-indexed-table-use"),
					index = "slot",
				},
			},
			values = { differentTarget("kill-indexed-holder-value"), differentTarget("kill-indexed-other-value") },
		},
		assignmentValue(indexedTarget, "kill-indexed-future-write", differentTarget("kill-indexed-future-value")),
	}),
	indexedCall,
	indexedTarget
)

local versionAliasTarget = declaration("versionAliasTarget", "version-alias-target")
local versionAliasCall = callExpression(versionAliasTarget, "version-alias-read")
local versionAliasFunction, _ = readInvocation(versionAliasCall, "version-alias-function")
local versionAliasHolder = declaration("versionAliasHolder", "version-alias-holder")
local versionAliasBody: { Record } = {
	localStatement(versionAliasTarget, "version-alias-target-declaration"),
	assignment(versionAliasTarget, "version-alias-current"),
	localStatement(versionAliasHolder, "version-alias-holder-declaration"),
	assignmentValue(versionAliasHolder, "version-alias-old-1", differentTarget("version-alias-old-value-1")),
	assignmentValue(versionAliasHolder, "version-alias-old-2", differentTarget("version-alias-old-value-2")),
	assignmentValue(versionAliasHolder, "version-alias-definition", versionAliasFunction),
}
local versionAlias = appendAliasBinding(versionAliasBody, versionAliasHolder, "version-alias-snapshot", true, "local")
table.insert(
	versionAliasBody,
	assignmentValue(versionAliasHolder, "version-alias-replacement-1", differentTarget("version-alias-new-value-1"))
)
table.insert(
	versionAliasBody,
	assignmentValue(versionAliasHolder, "version-alias-replacement-2", differentTarget("version-alias-new-value-2"))
)
table.insert(
	versionAliasBody,
	callStatement(localInvocation(versionAlias, "version-alias-call", true), "version-alias-statement")
)
table.insert(
	versionAliasBody,
	assignmentValue(versionAliasTarget, "version-alias-future-write", differentTarget("version-alias-future-value"))
)
expectProof(document(versionAliasBody), versionAliasCall, versionAliasTarget, "version-alias-current")

local oldAliasTarget = declaration("versionOldAliasTarget", "version-old-alias-target")
local oldAliasCall = callExpression(oldAliasTarget, "version-old-alias-read")
local oldAliasFunction, _ = readInvocation(oldAliasCall, "version-old-alias-function")
local oldAliasHolder = declaration("versionOldAliasHolder", "version-old-alias-holder")
local oldAliasBody: { Record } = {
	localStatement(oldAliasTarget, "version-old-alias-target-declaration"),
	assignment(oldAliasTarget, "version-old-alias-current"),
	localStatement(oldAliasHolder, "version-old-alias-holder-declaration"),
	assignmentValue(oldAliasHolder, "version-old-alias-old", differentTarget("version-old-alias-old-value")),
}
local oldAlias = appendAliasBinding(oldAliasBody, oldAliasHolder, "version-old-alias-snapshot", true, "local")
table.insert(oldAliasBody, assignmentValue(oldAliasHolder, "version-old-alias-definition", oldAliasFunction))
table.insert(
	oldAliasBody,
	callStatement(localInvocation(oldAlias, "version-old-alias-call", true), "version-old-alias-statement")
)
table.insert(
	oldAliasBody,
	assignmentValue(oldAliasTarget, "version-old-alias-future-write", differentTarget("version-old-alias-future-value"))
)
expectOriginFailure(document(oldAliasBody), oldAliasCall, oldAliasTarget)

local function versionBoundaryDocument(prefix: string, boundaryCount: number): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration", functionValue),
		callStatement(localInvocation(holder, prefix .. "-call", false), prefix .. "-call-statement"),
	}
	for index = 1, boundaryCount do
		table.insert(body, assignmentValue(holder, `{prefix}-boundary-{index}`, differentTarget(`{prefix}-value-{index}`)))
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local boundedVersions, boundedVersionsCall, boundedVersionsTarget = versionBoundaryDocument("version-bounded", 64)
expectProof(boundedVersions, boundedVersionsCall, boundedVersionsTarget, "version-bounded-current")
local excessiveVersions, excessiveVersionsCall, excessiveVersionsTarget = versionBoundaryDocument("version-excessive", 65)
expectOriginFailure(excessiveVersions, excessiveVersionsCall, excessiveVersionsTarget)
