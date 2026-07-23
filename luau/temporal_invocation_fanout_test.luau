--!strict

local Support = require("./temporal_test_support")
local InvocationSupport = require("./temporal_invocation_test_support")
local TemporalTargetIdentity = require("./temporal_target_identity")

type Record = Support.Record
type BindingKind = InvocationSupport.BindingKind

local assignment = Support.assignment
local assignmentValue = Support.assignmentValue
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
local wrappedExpression = InvocationSupport.wrappedExpression

local authenticatedOrigin: Record = { kind = "environment", name = "authenticated_target" }

local function expectProof(documentValue: Record, call: Record, target: Record, location: string)
	local proof = verifyOrigin(documentValue, call, target, authenticatedOrigin)
	assert(proof.definition_count == 1, `{location} fanout produced a definition set`)
	assert(proof.definition_location == location, `{location} fanout did not retain one source definition`)
end

local function expectOriginFailure(documentValue: Record, call: Record, target: Record)
	local location = target.location
	assert(type(location) == "string" and location ~= "")
	expectFailure(function()
		verifyOrigin(documentValue, call, target, authenticatedOrigin)
	end, "temporal target place " .. location)
end

local function consumerStatement(value: Record, prefix: string): Record
	return callStatement({
		type = "AstExprCall",
		location = prefix .. "-consumer",
		func = globalExpression("consume", prefix .. "-consumer-callee"),
		args = { value },
		self = false,
	}, prefix .. "-consumer-statement")
end

local function starDocument(
	prefix: string,
	leafCount: number,
	sourceBinding: BindingKind,
	wrapped: boolean
): (Record, Record, Record)
	assert(leafCount >= 2)
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
	for leafIndex = 1, leafCount do
		local alias = appendAliasBinding(
			body,
			holder,
			`{prefix}-leaf-{leafIndex}`,
			wrapped,
			if leafIndex % 2 == 0 then "assignment" else "local"
		)
		table.insert(
			body,
			callStatement(
				localInvocation(alias, `{prefix}-call-{leafIndex}`, wrapped),
				`{prefix}-call-{leafIndex}-statement`
			)
		)
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local star, starCall, starTarget = starDocument("fanout-star", 2, "assignment", true)
expectProof(star, starCall, starTarget, "fanout-star-current")

local bounded, boundedCall, boundedTarget = starDocument(
	"fanout-bounded",
	TemporalTargetIdentity.maxInvocationSites,
	"local",
	false
)
expectProof(bounded, boundedCall, boundedTarget, "fanout-bounded-current")

local excessive, excessiveCall, excessiveTarget = starDocument(
	"fanout-excessive",
	TemporalTargetIdentity.maxInvocationSites + 1,
	"local",
	false
)
expectOriginFailure(excessive, excessiveCall, excessiveTarget)

local mixedTarget = declaration("fanoutMixedTarget", "fanout-mixed-target")
local mixedCall = callExpression(mixedTarget, "fanout-mixed-read")
local mixedFunction, _ = readInvocation(mixedCall, "fanout-mixed-function")
local mixedHolder = declaration("fanoutMixedHolder", "fanout-mixed-holder")
local mixedBody: { Record } = {
	localStatement(mixedTarget, "fanout-mixed-target-declaration"),
	assignment(mixedTarget, "fanout-mixed-current"),
	localStatement(mixedHolder, "fanout-mixed-holder-declaration", mixedFunction),
	callStatement(localInvocation(mixedHolder, "fanout-mixed-direct-call", false), "fanout-mixed-direct-statement"),
}
local mixedAlias = appendAliasBinding(mixedBody, mixedHolder, "fanout-mixed-alias", false, "local")
table.insert(mixedBody, callStatement(localInvocation(mixedAlias, "fanout-mixed-alias-call", false), "fanout-mixed-alias-statement"))
table.insert(mixedBody, assignmentValue(mixedTarget, "fanout-mixed-write", differentTarget("fanout-mixed-value")))
expectProof(document(mixedBody), mixedCall, mixedTarget, "fanout-mixed-current")

local nestedTarget = declaration("fanoutNestedTarget", "fanout-nested-target")
local nestedCall = callExpression(nestedTarget, "fanout-nested-read")
local nestedFunction, _ = readInvocation(nestedCall, "fanout-nested-function")
local nestedHolder = declaration("fanoutNestedHolder", "fanout-nested-holder")
local nestedBody: { Record } = {
	localStatement(nestedTarget, "fanout-nested-target-declaration"),
	assignment(nestedTarget, "fanout-nested-current"),
	localFunctionStatement(nestedHolder, nestedFunction, "fanout-nested-holder-declaration"),
}
local nestedLeft = appendAliasBinding(nestedBody, nestedHolder, "fanout-nested-left", false, "local")
local nestedRight = appendAliasBinding(nestedBody, nestedHolder, "fanout-nested-right", false, "assignment")
for leafIndex = 1, 2 do
	local leaf = appendAliasBinding(
		nestedBody,
		nestedLeft,
		`fanout-nested-left-{leafIndex}`,
		false,
		if leafIndex == 1 then "local" else "assignment"
	)
	table.insert(
		nestedBody,
		callStatement(localInvocation(leaf, `fanout-nested-call-{leafIndex}`, false), `fanout-nested-statement-{leafIndex}`)
	)
end
table.insert(nestedBody, callStatement(localInvocation(nestedRight, "fanout-nested-right-call", false), "fanout-nested-right-statement"))
table.insert(nestedBody, assignmentValue(nestedTarget, "fanout-nested-write", differentTarget("fanout-nested-value")))
expectProof(document(nestedBody), nestedCall, nestedTarget, "fanout-nested-current")

local callerTarget = declaration("fanoutCallerTarget", "fanout-caller-target")
local callerCall = callExpression(callerTarget, "fanout-caller-read")
local callerHolderFunction, _ = readInvocation(callerCall, "fanout-caller-holder-function")
local callerHolder = declaration("fanoutCallerHolder", "fanout-caller-holder")
local caller = declaration("fanoutCaller", "fanout-caller")
local callerFunction, _ = invocationFromBody({
	callStatement(localInvocation(callerHolder, "fanout-caller-holder-call", false), "fanout-caller-holder-statement"),
}, "fanout-caller-function", nil, nil)
local callerBody: { Record } = {
	localStatement(callerTarget, "fanout-caller-target-declaration"),
	assignment(callerTarget, "fanout-caller-current"),
	localStatement(callerHolder, "fanout-caller-holder-declaration", callerHolderFunction),
	localStatement(caller, "fanout-caller-declaration", callerFunction),
}
for leafIndex = 1, 2 do
	local leaf = appendAliasBinding(callerBody, caller, `fanout-caller-leaf-{leafIndex}`, true, "assignment")
	table.insert(
		callerBody,
		callStatement(localInvocation(leaf, `fanout-caller-call-{leafIndex}`, true), `fanout-caller-statement-{leafIndex}`)
	)
end
table.insert(callerBody, assignmentValue(callerTarget, "fanout-caller-write", differentTarget("fanout-caller-value")))
expectProof(document(callerBody), callerCall, callerTarget, "fanout-caller-current")

local function failureFixture(prefix: string, mode: string): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration", functionValue),
	}
	local first = appendAliasBinding(body, holder, prefix .. "-first", false, "local")
	table.insert(body, callStatement(localInvocation(first, prefix .. "-first-call", false), prefix .. "-first-statement"))
	if mode == "escape" then
		table.insert(body, consumerStatement(localExpression(holder, prefix .. "-escape"), prefix .. "-escape"))
	elseif mode == "incomplete" then
		appendAliasBinding(body, holder, prefix .. "-unused", false, "local")
	elseif mode == "reassignment" then
		local second = appendAliasBinding(body, holder, prefix .. "-second", false, "local")
		table.insert(body, assignmentValue(second, prefix .. "-second-write", differentTarget(prefix .. "-second-value")))
		table.insert(body, callStatement(localInvocation(second, prefix .. "-second-call", false), prefix .. "-second-statement"))
	elseif mode == "repeated" then
		local second = appendAliasBinding(body, holder, prefix .. "-second", false, "local")
		table.insert(body, whileStatement(prefix .. "-loop", {
			callStatement(localInvocation(second, prefix .. "-loop-call", false), prefix .. "-loop-statement"),
		}))
	else
		assert(mode == "cycle")
		local second = appendAliasBinding(body, holder, prefix .. "-second", false, "local")
		table.insert(body, assignmentValue(holder, prefix .. "-cycle-write", localExpression(second, prefix .. "-cycle-value")))
		table.insert(body, callStatement(localInvocation(second, prefix .. "-second-call", false), prefix .. "-second-statement"))
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

for _, mode in { "escape", "incomplete", "reassignment", "repeated", "cycle" } do
	local fixture, call, target = failureFixture("fanout-" .. mode, mode)
	expectOriginFailure(fixture, call, target)
end

local orderTarget = declaration("fanoutOrderTarget", "fanout-order-target")
local orderCall = callExpression(orderTarget, "fanout-order-read")
local orderFunction, _ = readInvocation(orderCall, "fanout-order-function")
local orderHolder = declaration("fanoutOrderHolder", "fanout-order-holder")
local orderAlias = declaration("fanoutOrderAlias", "fanout-order-alias")
expectOriginFailure(
	document({
		localStatement(orderTarget, "fanout-order-target-declaration"),
		assignment(orderTarget, "fanout-order-current"),
		localStatement(orderHolder, "fanout-order-holder-declaration", orderFunction),
		localStatement(orderAlias, "fanout-order-alias-declaration"),
		callStatement(localInvocation(orderAlias, "fanout-order-early-call", false), "fanout-order-early-statement"),
		assignmentValue(orderAlias, "fanout-order-alias-assignment", localExpression(orderHolder, "fanout-order-source")),
		assignmentValue(orderTarget, "fanout-order-write", differentTarget("fanout-order-value")),
	}),
	orderCall,
	orderTarget
)

type TransferKind = "local" | "assignment"
type TransferCase = {
	prefix: string,
	kind: TransferKind,
	ordinal: number,
	targetCount: number,
	valueCount: number,
	wrapped: boolean,
	overwriteSource: boolean,
}

local function multiTransferDocument(
	prefix: string,
	kind: TransferKind,
	ordinal: number,
	targetCount: number,
	valueCount: number,
	wrapped: boolean,
	overwriteSource: boolean
): (Record, Record, Record)
	assert(ordinal >= 1 and ordinal <= targetCount and ordinal <= valueCount)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local alias = declaration(prefix .. "Alias", prefix .. "-alias")
	local targets: { Record } = {}
	for index = 1, targetCount do
		targets[index] = if index == ordinal
			then alias
			else declaration(`{prefix}Other{index}`, `{prefix}-other-{index}`)
	end
	local values: { Record } = {}
	for index = 1, valueCount do
		if index == ordinal then
			local source = localExpression(holder, prefix .. "-source")
			values[index] = if wrapped then wrappedExpression(source, prefix .. "-source") else source
		else
			values[index] = differentTarget(`{prefix}-value-{index}`)
		end
	end
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration", functionValue),
	}
	if kind == "local" then
		table.insert(body, {
			type = "AstStatLocal",
			location = prefix .. "-transfer",
			vars = targets,
			values = values,
		})
	else
		for index, localNode in targets do
			table.insert(body, localStatement(localNode, `{prefix}-declaration-{index}`))
		end
		local variables: { Record } = {}
		for index, localNode in targets do
			variables[index] = localExpression(localNode, `{prefix}-target-{index}`)
		end
		table.insert(body, {
			type = "AstStatAssign",
			location = prefix .. "-transfer",
			vars = variables,
			values = values,
		})
	end
	table.insert(body, callStatement(localInvocation(holder, prefix .. "-direct-call", false), prefix .. "-direct-statement"))
	if overwriteSource then
		table.insert(body, assignmentValue(holder, prefix .. "-source-kill", differentTarget(prefix .. "-source-kill-value")))
	end
	table.insert(body, callStatement(localInvocation(alias, prefix .. "-alias-call", true), prefix .. "-alias-statement"))
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local transferCases: { TransferCase } = {
	{ prefix = "fanout-transfer-local-first", kind = "local", ordinal = 1, targetCount = 2, valueCount = 2, wrapped = false, overwriteSource = false },
	{ prefix = "fanout-transfer-local-middle", kind = "local", ordinal = 2, targetCount = 3, valueCount = 3, wrapped = true, overwriteSource = true },
	{ prefix = "fanout-transfer-local-final-short", kind = "local", ordinal = 2, targetCount = 3, valueCount = 2, wrapped = false, overwriteSource = true },
	{ prefix = "fanout-transfer-assignment-first-extra", kind = "assignment", ordinal = 1, targetCount = 2, valueCount = 3, wrapped = true, overwriteSource = false },
	{ prefix = "fanout-transfer-assignment-middle", kind = "assignment", ordinal = 2, targetCount = 3, valueCount = 3, wrapped = false, overwriteSource = true },
	{ prefix = "fanout-transfer-assignment-final-short", kind = "assignment", ordinal = 2, targetCount = 3, valueCount = 2, wrapped = true, overwriteSource = true },
}
for _, row in transferCases do
	local fixture, call, target = multiTransferDocument(
		row.prefix,
		row.kind,
		row.ordinal,
		row.targetCount,
		row.valueCount,
		row.wrapped,
		row.overwriteSource
	)
	expectProof(fixture, call, target, row.prefix .. "-current")
end

local chainTarget = declaration("fanoutTransferChainTarget", "fanout-transfer-chain-target")
local chainCall = callExpression(chainTarget, "fanout-transfer-chain-read")
local chainFunction, _ = readInvocation(chainCall, "fanout-transfer-chain-function")
local chainHolder = declaration("fanoutTransferChainHolder", "fanout-transfer-chain-holder")
local chainFirst = declaration("fanoutTransferChainFirst", "fanout-transfer-chain-first")
local chainSecond = declaration("fanoutTransferChainSecond", "fanout-transfer-chain-second")
local chainOther = declaration("fanoutTransferChainOther", "fanout-transfer-chain-other")
expectProof(
	document({
		localStatement(chainTarget, "fanout-transfer-chain-target-declaration"),
		assignment(chainTarget, "fanout-transfer-chain-current"),
		localStatement(chainHolder, "fanout-transfer-chain-holder-declaration", chainFunction),
		{
			type = "AstStatLocal",
			location = "fanout-transfer-chain-first-transfer",
			vars = { chainOther, chainFirst },
			values = {
				differentTarget("fanout-transfer-chain-first-other-value"),
				localExpression(chainHolder, "fanout-transfer-chain-first-source"),
			},
		},
		localStatement(chainSecond, "fanout-transfer-chain-second-declaration"),
		{
			type = "AstStatAssign",
			location = "fanout-transfer-chain-second-transfer",
			vars = {
				localExpression(chainOther, "fanout-transfer-chain-second-other-target"),
				localExpression(chainSecond, "fanout-transfer-chain-second-target"),
			},
			values = {
				differentTarget("fanout-transfer-chain-second-other-value"),
				localExpression(chainFirst, "fanout-transfer-chain-second-source"),
			},
		},
		assignmentValue(chainHolder, "fanout-transfer-chain-source-kill", differentTarget("fanout-transfer-chain-source-kill-value")),
		callStatement(localInvocation(chainSecond, "fanout-transfer-chain-call", true), "fanout-transfer-chain-statement"),
		assignmentValue(chainTarget, "fanout-transfer-chain-future-write", differentTarget("fanout-transfer-chain-future-value")),
	}),
	chainCall,
	chainTarget,
	"fanout-transfer-chain-current"
)

local boundTarget = declaration("fanoutTransferBoundTarget", "fanout-transfer-bound-target")
local boundCall = callExpression(boundTarget, "fanout-transfer-bound-read")
local boundHolderFunction, _ = readInvocation(boundCall, "fanout-transfer-bound-holder-function")
local boundHolder = declaration("fanoutTransferBoundHolder", "fanout-transfer-bound-holder")
local boundCaller = declaration("fanoutTransferBoundCaller", "fanout-transfer-bound-caller")
local boundCallerFunction, _ = invocationFromBody({
	callStatement(localInvocation(boundHolder, "fanout-transfer-bound-holder-call", false), "fanout-transfer-bound-holder-statement"),
}, "fanout-transfer-bound-caller-function", nil, nil)
local boundAlias = declaration("fanoutTransferBoundAlias", "fanout-transfer-bound-alias")
local boundOther = declaration("fanoutTransferBoundOther", "fanout-transfer-bound-other")
expectProof(
	document({
		localStatement(boundTarget, "fanout-transfer-bound-target-declaration"),
		assignment(boundTarget, "fanout-transfer-bound-current"),
		localStatement(boundHolder, "fanout-transfer-bound-holder-declaration", boundHolderFunction),
		localStatement(boundCaller, "fanout-transfer-bound-caller-declaration", boundCallerFunction),
		{
			type = "AstStatLocal",
			location = "fanout-transfer-bound-transfer",
			vars = { boundOther, boundAlias },
			values = {
				differentTarget("fanout-transfer-bound-other-value"),
				localExpression(boundCaller, "fanout-transfer-bound-source"),
			},
		},
		callStatement(localInvocation(boundAlias, "fanout-transfer-bound-call", true), "fanout-transfer-bound-statement"),
		assignmentValue(boundTarget, "fanout-transfer-bound-future-write", differentTarget("fanout-transfer-bound-future-value")),
	}),
	boundCall,
	boundTarget,
	"fanout-transfer-bound-current"
)

local discardedTransferTarget = declaration("fanoutDiscardedTransferTarget", "fanout-discarded-transfer-target")
local discardedTransferCall = callExpression(discardedTransferTarget, "fanout-discarded-transfer-read")
local discardedTransferFunction, _ = readInvocation(discardedTransferCall, "fanout-discarded-transfer-function")
local discardedTransferHolder = declaration("fanoutDiscardedTransferHolder", "fanout-discarded-transfer-holder")
local discardedTransferOther = declaration("fanoutDiscardedTransferOther", "fanout-discarded-transfer-other")
expectOriginFailure(
	document({
		localStatement(discardedTransferTarget, "fanout-discarded-transfer-target-declaration"),
		assignment(discardedTransferTarget, "fanout-discarded-transfer-current"),
		localStatement(discardedTransferHolder, "fanout-discarded-transfer-holder-declaration", discardedTransferFunction),
		{
			type = "AstStatLocal",
			location = "fanout-discarded-transfer",
			vars = { discardedTransferOther },
			values = {
				differentTarget("fanout-discarded-transfer-other-value"),
				localExpression(discardedTransferHolder, "fanout-discarded-transfer-source"),
			},
		},
		callStatement(localInvocation(discardedTransferHolder, "fanout-discarded-transfer-call", false), "fanout-discarded-transfer-statement"),
		assignmentValue(discardedTransferTarget, "fanout-discarded-transfer-future-write", differentTarget("fanout-discarded-transfer-future-value")),
	}),
	discardedTransferCall,
	discardedTransferTarget
)

local duplicateLocalTarget = declaration("fanoutDuplicateLocalTarget", "fanout-duplicate-local-target")
local duplicateLocalCall = callExpression(duplicateLocalTarget, "fanout-duplicate-local-read")
local duplicateLocalFunction, _ = readInvocation(duplicateLocalCall, "fanout-duplicate-local-function")
local duplicateLocalHolder = declaration("fanoutDuplicateLocalHolder", "fanout-duplicate-local-holder")
local duplicateLocalAlias = declaration("fanoutDuplicateLocalAlias", "fanout-duplicate-local-alias")
expectOriginFailure(
	document({
		localStatement(duplicateLocalTarget, "fanout-duplicate-local-target-declaration"),
		assignment(duplicateLocalTarget, "fanout-duplicate-local-current"),
		localStatement(duplicateLocalHolder, "fanout-duplicate-local-holder-declaration", duplicateLocalFunction),
		{
			type = "AstStatLocal",
			location = "fanout-duplicate-local-transfer",
			vars = { duplicateLocalAlias, duplicateLocalAlias },
			values = {
				differentTarget("fanout-duplicate-local-other-value"),
				localExpression(duplicateLocalHolder, "fanout-duplicate-local-source"),
			},
		},
		callStatement(
			localInvocation(duplicateLocalAlias, "fanout-duplicate-local-call", false),
			"fanout-duplicate-local-statement"
		),
		assignmentValue(
			duplicateLocalTarget,
			"fanout-duplicate-local-future-write",
			differentTarget("fanout-duplicate-local-future-value")
		),
	}),
	duplicateLocalCall,
	duplicateLocalTarget
)

type InvalidTransferMode = "duplicate" | "duplicate_other" | "effectful" | "malformed" | "same" | "branch"

local function invalidTransferDocument(prefix: string, mode: InvalidTransferMode): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local alias = declaration(prefix .. "Alias", prefix .. "-alias")
	local other = declaration(prefix .. "Other", prefix .. "-other")
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration", functionValue),
		localStatement(alias, prefix .. "-alias-declaration"),
		localStatement(other, prefix .. "-other-declaration"),
	}
	local transfer: Record
	if mode == "duplicate" then
		transfer = {
			type = "AstStatAssign",
			location = prefix .. "-transfer",
			vars = { localExpression(alias, prefix .. "-target-1"), localExpression(alias, prefix .. "-target-2") },
			values = { differentTarget(prefix .. "-value-1"), localExpression(holder, prefix .. "-source") },
		}
	elseif mode == "duplicate_other" then
		transfer = {
			type = "AstStatAssign",
			location = prefix .. "-transfer",
			vars = {
				localExpression(other, prefix .. "-other-target-1"),
				localExpression(other, prefix .. "-other-target-2"),
				localExpression(alias, prefix .. "-alias-target"),
			},
			values = {
				differentTarget(prefix .. "-other-value-1"),
				differentTarget(prefix .. "-other-value-2"),
				localExpression(holder, prefix .. "-source"),
			},
		}
	elseif mode == "effectful" then
		transfer = {
			type = "AstStatAssign",
			location = prefix .. "-transfer",
			vars = {
				localExpression(alias, prefix .. "-alias-target"),
				{
					type = "AstExprIndexName",
					location = prefix .. "-effectful-target",
					expr = localExpression(other, prefix .. "-effectful-table"),
					index = "slot",
				},
			},
			values = { localExpression(holder, prefix .. "-source"), differentTarget(prefix .. "-other-value") },
		}
	elseif mode == "malformed" then
		transfer = {
			type = "AstStatAssign",
			location = prefix .. "-transfer",
			vars = { localExpression(alias, prefix .. "-target") },
			values = { localExpression(holder, prefix .. "-source"), ("malformed" :: any) },
		}
	elseif mode == "same" then
		table.insert(body, assignmentValue(alias, prefix .. "-alias-old", differentTarget(prefix .. "-alias-old-value")))
		transfer = {
			type = "AstStatAssign",
			location = prefix .. "-transfer",
			vars = { localExpression(alias, prefix .. "-alias-target"), localExpression(other, prefix .. "-other-target") },
			values = { localExpression(holder, prefix .. "-source"), localExpression(alias, prefix .. "-alias-old-use") },
		}
	else
		transfer = {
			type = "AstStatAssign",
			location = prefix .. "-transfer",
			vars = { localExpression(alias, prefix .. "-target"), localExpression(other, prefix .. "-other-target") },
			values = { localExpression(holder, prefix .. "-source"), differentTarget(prefix .. "-other-value") },
		}
	end
	if mode == "branch" then
		table.insert(body, Support.branchStatement(prefix, { transfer }, nil))
	else
		table.insert(body, transfer)
	end
	table.insert(body, callStatement(localInvocation(alias, prefix .. "-call", false), prefix .. "-call-statement"))
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

for _, mode in { "duplicate", "duplicate_other", "effectful", "malformed", "same", "branch" } do
	local prefix = "fanout-transfer-invalid-" .. mode
	local fixture, call, target = invalidTransferDocument(prefix, mode :: InvalidTransferMode)
	expectOriginFailure(fixture, call, target)
end
