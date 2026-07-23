--!strict

local Support = require("./temporal_test_support")
local InvocationSupport = require("./temporal_invocation_test_support")

type Record = Support.Record
type DefinitionKind = "local" | "assignment"
type MappingCase = {
	prefix: string,
	kind: DefinitionKind,
	ordinal: number,
	targetCount: number,
	valueCount: number,
	wrapped: boolean,
	priorGeneration: boolean,
	laterGeneration: boolean,
}

local assignment = Support.assignment
local assignmentValue = Support.assignmentValue
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

local appendAliasBinding = InvocationSupport.appendAliasBinding
local differentTarget = InvocationSupport.differentTarget
local localInvocation = InvocationSupport.localInvocation
local readInvocation = InvocationSupport.readInvocation
local wrappedExpression = InvocationSupport.wrappedExpression

local authenticatedOrigin: Record = { kind = "environment", name = "authenticated_target" }

local function expectProof(documentValue: Record, call: Record, target: Record, location: string)
	local proof = verifyOrigin(documentValue, call, target, authenticatedOrigin)
	assert(proof.definition_count == 1, `{location} multi-target definition produced a definition set`)
	assert(proof.definition_location == location, `{location} multi-target definition lost the original invocation`)
end

local function expectOriginFailure(documentValue: Record, call: Record, target: Record)
	local location = target.location
	assert(type(location) == "string" and location ~= "")
	expectFailure(function()
		verifyOrigin(documentValue, call, target, authenticatedOrigin)
	end, "temporal target place " .. location)
end

local function mappedDefinitionDocument(
	prefix: string,
	kind: DefinitionKind,
	ordinal: number,
	targetCount: number,
	valueCount: number,
	wrapped: boolean,
	priorGeneration: boolean,
	laterGeneration: boolean
): (Record, Record, Record)
	assert(ordinal >= 1 and ordinal <= targetCount and ordinal <= valueCount)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local targets: { Record } = {}
	for index = 1, targetCount do
		targets[index] = if index == ordinal
			then holder
			else declaration(`{prefix}Other{index}`, `{prefix}-other-{index}`)
	end
	local values: { Record } = {}
	for index = 1, valueCount do
		values[index] = if index == ordinal
			then if wrapped then wrappedExpression(functionValue, prefix .. "-definition") else functionValue
			else differentTarget(`{prefix}-value-{index}`)
	end
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
	}
	local definition: Record
	if kind == "local" then
		definition = {
			type = "AstStatLocal",
			location = prefix .. "-definition",
			vars = targets,
			values = values,
		}
	else
		for index, localNode in targets do
			table.insert(body, localStatement(localNode, `{prefix}-declaration-{index}`))
		end
		if priorGeneration then
			table.insert(body, assignmentValue(holder, prefix .. "-old", differentTarget(prefix .. "-old-value")))
		end
		local variables: { Record } = {}
		for index, localNode in targets do
			variables[index] = localExpression(localNode, `{prefix}-definition-target-{index}`)
		end
		definition = {
			type = "AstStatAssign",
			location = prefix .. "-definition",
			vars = variables,
			values = values,
		}
	end
	table.insert(body, definition)
	table.insert(body, callStatement(localInvocation(holder, prefix .. "-call", false), prefix .. "-call-statement"))
	if laterGeneration then
		table.insert(body, assignmentValue(holder, prefix .. "-kill", differentTarget(prefix .. "-kill-value")))
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local mappingCases: { MappingCase } = {
	{ prefix = "definition-local-first", kind = "local", ordinal = 1, targetCount = 2, valueCount = 2, wrapped = false, priorGeneration = false, laterGeneration = true },
	{ prefix = "definition-local-middle-wrapped", kind = "local", ordinal = 2, targetCount = 3, valueCount = 3, wrapped = true, priorGeneration = false, laterGeneration = true },
	{ prefix = "definition-local-final-short", kind = "local", ordinal = 2, targetCount = 3, valueCount = 2, wrapped = false, priorGeneration = false, laterGeneration = true },
	{ prefix = "definition-assignment-first-extra", kind = "assignment", ordinal = 1, targetCount = 2, valueCount = 3, wrapped = false, priorGeneration = true, laterGeneration = true },
	{ prefix = "definition-assignment-middle", kind = "assignment", ordinal = 2, targetCount = 3, valueCount = 3, wrapped = false, priorGeneration = true, laterGeneration = true },
	{ prefix = "definition-assignment-final-short", kind = "assignment", ordinal = 2, targetCount = 3, valueCount = 2, wrapped = true, priorGeneration = true, laterGeneration = true },
}
for _, row in mappingCases do
	local prefix = row.prefix
	local fixture, call, target = mappedDefinitionDocument(
		prefix,
		row.kind,
		row.ordinal,
		row.targetCount,
		row.valueCount,
		row.wrapped,
		row.priorGeneration,
		row.laterGeneration
	)
	expectProof(fixture, call, target, prefix .. "-current")
end

local aliasTarget = declaration("definitionAliasTarget", "definition-alias-target")
local aliasCall = callExpression(aliasTarget, "definition-alias-read")
local aliasFunction, _ = readInvocation(aliasCall, "definition-alias-function")
local aliasHolder = declaration("definitionAliasHolder", "definition-alias-holder")
local aliasOther = declaration("definitionAliasOther", "definition-alias-other")
local aliasBody: { Record } = {
	localStatement(aliasTarget, "definition-alias-target-declaration"),
	assignment(aliasTarget, "definition-alias-current"),
	localStatement(aliasHolder, "definition-alias-holder-declaration"),
	localStatement(aliasOther, "definition-alias-other-declaration"),
	assignmentValue(aliasHolder, "definition-alias-old", differentTarget("definition-alias-old-value")),
	{
		type = "AstStatAssign",
		location = "definition-alias-definition",
		vars = {
			localExpression(aliasOther, "definition-alias-other-target"),
			localExpression(aliasHolder, "definition-alias-holder-target"),
		},
		values = { differentTarget("definition-alias-other-value"), aliasFunction },
	},
}
local alias = appendAliasBinding(aliasBody, aliasHolder, "definition-alias-snapshot", true, "local")
table.insert(aliasBody, callStatement(localInvocation(aliasHolder, "definition-alias-direct-call", false), "definition-alias-direct-statement"))
table.insert(aliasBody, callStatement(localInvocation(alias, "definition-alias-call", true), "definition-alias-statement"))
table.insert(aliasBody, assignmentValue(aliasHolder, "definition-alias-kill", differentTarget("definition-alias-kill-value")))
table.insert(aliasBody, assignmentValue(aliasTarget, "definition-alias-future-write", differentTarget("definition-alias-future-value")))
expectProof(document(aliasBody), aliasCall, aliasTarget, "definition-alias-current")

local function capturedDefinitionDocument(prefix: string, callBeforeKill: boolean): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local other = declaration(prefix .. "Other", prefix .. "-other")
	local caller = declaration(prefix .. "Caller", prefix .. "-caller")
	local callerFunction, _ = invocationFromBody({
		callStatement(localInvocation(holder, prefix .. "-holder-call", false), prefix .. "-holder-statement"),
	}, prefix .. "-caller-function", nil, nil)
	local callerStatement = callStatement(localInvocation(caller, prefix .. "-caller-call", false), prefix .. "-caller-statement")
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration"),
		localStatement(other, prefix .. "-other-declaration"),
		{
			type = "AstStatAssign",
			location = prefix .. "-definition",
			vars = {
				localExpression(other, prefix .. "-other-target"),
				localExpression(holder, prefix .. "-holder-target"),
			},
			values = { differentTarget(prefix .. "-other-value"), functionValue },
		},
		localStatement(caller, prefix .. "-caller-declaration", callerFunction),
	}
	if callBeforeKill then
		table.insert(body, callerStatement)
	end
	table.insert(body, assignmentValue(holder, prefix .. "-kill", differentTarget(prefix .. "-kill-value")))
	if not callBeforeKill then
		table.insert(body, callerStatement)
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local capturedBefore, capturedBeforeCall, capturedBeforeTarget = capturedDefinitionDocument("definition-captured-before", true)
expectProof(capturedBefore, capturedBeforeCall, capturedBeforeTarget, "definition-captured-before-current")
local capturedAfter, capturedAfterCall, capturedAfterTarget = capturedDefinitionDocument("definition-captured-after", false)
expectOriginFailure(capturedAfter, capturedAfterCall, capturedAfterTarget)

local discardedTarget = declaration("definitionDiscardedTarget", "definition-discarded-target")
local discardedCall = callExpression(discardedTarget, "definition-discarded-read")
local discardedFunction, _ = readInvocation(discardedCall, "definition-discarded-function")
local discardedHolder = declaration("definitionDiscardedHolder", "definition-discarded-holder")
expectOriginFailure(
	document({
		localStatement(discardedTarget, "definition-discarded-target-declaration"),
		assignment(discardedTarget, "definition-discarded-current"),
		{
			type = "AstStatLocal",
			location = "definition-discarded-definition",
			vars = { discardedHolder },
			values = { differentTarget("definition-discarded-value"), discardedFunction },
		},
		assignmentValue(discardedTarget, "definition-discarded-future-write", differentTarget("definition-discarded-future-value")),
	}),
	discardedCall,
	discardedTarget
)

local duplicateTarget = declaration("definitionDuplicateTarget", "definition-duplicate-target")
local duplicateCall = callExpression(duplicateTarget, "definition-duplicate-read")
local duplicateFunction, _ = readInvocation(duplicateCall, "definition-duplicate-function")
local duplicateHolder = declaration("definitionDuplicateHolder", "definition-duplicate-holder")
expectOriginFailure(
	document({
		localStatement(duplicateTarget, "definition-duplicate-target-declaration"),
		assignment(duplicateTarget, "definition-duplicate-current"),
		localStatement(duplicateHolder, "definition-duplicate-holder-declaration"),
		{
			type = "AstStatAssign",
			location = "definition-duplicate-definition",
			vars = {
				localExpression(duplicateHolder, "definition-duplicate-target-1"),
				localExpression(duplicateHolder, "definition-duplicate-target-2"),
			},
			values = { differentTarget("definition-duplicate-value-1"), duplicateFunction },
		},
		callStatement(localInvocation(duplicateHolder, "definition-duplicate-call", false), "definition-duplicate-statement"),
		assignmentValue(duplicateTarget, "definition-duplicate-future-write", differentTarget("definition-duplicate-future-value")),
	}),
	duplicateCall,
	duplicateTarget
)

local function effectfulDefinitionDocument(prefix: string, targetKind: "index" | "global"): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local placeTable = declaration(prefix .. "Table", prefix .. "-table")
	local otherTarget: Record = if targetKind == "index"
		then {
			type = "AstExprIndexName",
			location = prefix .. "-other-target",
			expr = localExpression(placeTable, prefix .. "-table-use"),
			index = "slot",
		}
		else { type = "AstExprGlobal", location = prefix .. "-other-target", global = "effectful_target" }
	return document({
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration"),
		localStatement(placeTable, prefix .. "-table-declaration"),
		{
			type = "AstStatAssign",
			location = prefix .. "-definition",
			vars = { localExpression(holder, prefix .. "-holder-target"), otherTarget },
			values = { functionValue, differentTarget(prefix .. "-other-value") },
		},
		callStatement(localInvocation(holder, prefix .. "-call", false), prefix .. "-call-statement"),
		assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")),
	}), call, target
end

for _, kind in { "index", "global" } do
	local prefix = "definition-effectful-" .. kind
	local fixture, call, target = effectfulDefinitionDocument(prefix, kind :: "index" | "global")
	expectOriginFailure(fixture, call, target)
end

local sameStatementTarget = declaration("definitionSameStatementTarget", "definition-same-statement-target")
local sameStatementCall = callExpression(sameStatementTarget, "definition-same-statement-read")
local sameStatementFunction, _ = readInvocation(sameStatementCall, "definition-same-statement-function")
local sameStatementHolder = declaration("definitionSameStatementHolder", "definition-same-statement-holder")
local sameStatementOther = declaration("definitionSameStatementOther", "definition-same-statement-other")
expectOriginFailure(
	document({
		localStatement(sameStatementTarget, "definition-same-statement-target-declaration"),
		assignment(sameStatementTarget, "definition-same-statement-current"),
		localStatement(sameStatementHolder, "definition-same-statement-holder-declaration"),
		localStatement(sameStatementOther, "definition-same-statement-other-declaration"),
		assignmentValue(sameStatementHolder, "definition-same-statement-old", differentTarget("definition-same-statement-old-value")),
		{
			type = "AstStatAssign",
			location = "definition-same-statement-definition",
			vars = {
				localExpression(sameStatementHolder, "definition-same-statement-holder-target"),
				localExpression(sameStatementOther, "definition-same-statement-other-target"),
			},
			values = {
				sameStatementFunction,
				localExpression(sameStatementHolder, "definition-same-statement-old-use"),
			},
		},
		callStatement(localInvocation(sameStatementHolder, "definition-same-statement-call", false), "definition-same-statement-call-statement"),
		assignmentValue(sameStatementTarget, "definition-same-statement-future-write", differentTarget("definition-same-statement-future-value")),
	}),
	sameStatementCall,
	sameStatementTarget
)

local malformedTarget = declaration("definitionMalformedTarget", "definition-malformed-target")
local malformedCall = callExpression(malformedTarget, "definition-malformed-read")
local malformedFunction, _ = readInvocation(malformedCall, "definition-malformed-function")
local malformedHolder = declaration("definitionMalformedHolder", "definition-malformed-holder")
expectOriginFailure(
	document({
		localStatement(malformedTarget, "definition-malformed-target-declaration"),
		assignment(malformedTarget, "definition-malformed-current"),
		localStatement(malformedHolder, "definition-malformed-holder-declaration"),
		{
			type = "AstStatAssign",
			location = "definition-malformed-definition",
			vars = { localExpression(malformedHolder, "definition-malformed-holder-target") },
			values = { malformedFunction, ("malformed" :: any) },
		},
		callStatement(localInvocation(malformedHolder, "definition-malformed-call", false), "definition-malformed-statement"),
		assignmentValue(malformedTarget, "definition-malformed-future-write", differentTarget("definition-malformed-future-value")),
	}),
	malformedCall,
	malformedTarget
)

local unorderedTarget = declaration("definitionUnorderedTarget", "definition-unordered-target")
local unorderedCall = callExpression(unorderedTarget, "definition-unordered-read")
local unorderedFunction, _ = readInvocation(unorderedCall, "definition-unordered-function")
local unorderedHolder = declaration("definitionUnorderedHolder", "definition-unordered-holder")
local unorderedOther = declaration("definitionUnorderedOther", "definition-unordered-other")
expectOriginFailure(
	document({
		localStatement(unorderedTarget, "definition-unordered-target-declaration"),
		assignment(unorderedTarget, "definition-unordered-current"),
		localStatement(unorderedHolder, "definition-unordered-holder-declaration"),
		localStatement(unorderedOther, "definition-unordered-other-declaration"),
		branchStatement("definition-unordered", {
			{
				type = "AstStatAssign",
				location = "definition-unordered-definition",
				vars = {
					localExpression(unorderedOther, "definition-unordered-other-target"),
					localExpression(unorderedHolder, "definition-unordered-holder-target"),
				},
				values = { differentTarget("definition-unordered-other-value"), unorderedFunction },
			},
		}, nil),
		callStatement(localInvocation(unorderedHolder, "definition-unordered-call", false), "definition-unordered-call-statement"),
		assignmentValue(unorderedTarget, "definition-unordered-future-write", differentTarget("definition-unordered-future-value")),
	}),
	unorderedCall,
	unorderedTarget
)

local function functionStatement(localNode: Record, functionValue: Record, location: string): Record
	return {
		type = "AstStatFunction",
		location = location,
		name = localExpression(localNode, location .. "-target"),
		func = functionValue,
	}
end

local function statementDefinitionDocument(
	prefix: string,
	prior: "none" | "scalar" | "function",
	later: "none" | "scalar" | "function"
): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local priorFunction, _ = invocationFromBody({}, prefix .. "-prior", nil, nil)
	local laterFunction, _ = invocationFromBody({}, prefix .. "-later", nil, nil)
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration"),
	}
	if prior == "scalar" then
		table.insert(body, assignmentValue(holder, prefix .. "-prior", differentTarget(prefix .. "-prior-value")))
	elseif prior == "function" then
		table.insert(body, functionStatement(holder, priorFunction, prefix .. "-prior"))
	end
	table.insert(body, functionStatement(holder, functionValue, prefix .. "-definition"))
	table.insert(body, callStatement(localInvocation(holder, prefix .. "-call", false), prefix .. "-call-statement"))
	if later == "scalar" then
		table.insert(body, assignmentValue(holder, prefix .. "-later", differentTarget(prefix .. "-later-value")))
	elseif later == "function" then
		table.insert(body, functionStatement(holder, laterFunction, prefix .. "-later"))
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

for _, row in {
	{ prefix = "definition-statement-direct", prior = "none", later = "none" },
	{ prefix = "definition-statement-prior-scalar", prior = "scalar", later = "none" },
	{ prefix = "definition-statement-later-scalar", prior = "none", later = "scalar" },
	{ prefix = "definition-statement-prior-function", prior = "function", later = "none" },
	{ prefix = "definition-statement-later-function", prior = "none", later = "function" },
	{ prefix = "definition-statement-mixed", prior = "scalar", later = "function" },
} do
	local fixture, call, target = statementDefinitionDocument(
		row.prefix,
		row.prior :: "none" | "scalar" | "function",
		row.later :: "none" | "scalar" | "function"
	)
	expectProof(fixture, call, target, row.prefix .. "-current")
end

local statementAliasTarget = declaration("definitionStatementAliasTarget", "definition-statement-alias-target")
local statementAliasCall = callExpression(statementAliasTarget, "definition-statement-alias-read")
local statementAliasFunction, _ = readInvocation(statementAliasCall, "definition-statement-alias-function")
local statementAliasReplacement, _ = invocationFromBody({}, "definition-statement-alias-replacement", nil, nil)
local statementAliasHolder = declaration("definitionStatementAliasHolder", "definition-statement-alias-holder")
local statementAliasBody: { Record } = {
	localStatement(statementAliasTarget, "definition-statement-alias-target-declaration"),
	assignment(statementAliasTarget, "definition-statement-alias-current"),
	localStatement(statementAliasHolder, "definition-statement-alias-holder-declaration"),
	functionStatement(statementAliasHolder, statementAliasFunction, "definition-statement-alias-definition"),
}
local statementAlias = appendAliasBinding(statementAliasBody, statementAliasHolder, "definition-statement-alias-snapshot", true, "local")
table.insert(
	statementAliasBody,
	functionStatement(statementAliasHolder, statementAliasReplacement, "definition-statement-alias-replacement")
)
table.insert(
	statementAliasBody,
	callStatement(localInvocation(statementAlias, "definition-statement-alias-call", true), "definition-statement-alias-statement")
)
table.insert(
	statementAliasBody,
	assignmentValue(statementAliasTarget, "definition-statement-alias-future-write", differentTarget("definition-statement-alias-future-value"))
)
expectProof(document(statementAliasBody), statementAliasCall, statementAliasTarget, "definition-statement-alias-current")

local function capturedStatementDocument(prefix: string, callBeforeReplacement: boolean): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local replacement, _ = invocationFromBody({}, prefix .. "-replacement", nil, nil)
	local holder = declaration(prefix .. "Holder", prefix .. "-holder")
	local caller = declaration(prefix .. "Caller", prefix .. "-caller")
	local callerFunction, _ = invocationFromBody({
		callStatement(localInvocation(holder, prefix .. "-holder-call", false), prefix .. "-holder-statement"),
	}, prefix .. "-caller-function", nil, nil)
	local callerStatement = callStatement(localInvocation(caller, prefix .. "-caller-call", false), prefix .. "-caller-statement")
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(holder, prefix .. "-holder-declaration"),
		functionStatement(holder, functionValue, prefix .. "-definition"),
		localStatement(caller, prefix .. "-caller-declaration", callerFunction),
	}
	if callBeforeReplacement then
		table.insert(body, callerStatement)
	end
	table.insert(body, functionStatement(holder, replacement, prefix .. "-replacement"))
	if not callBeforeReplacement then
		table.insert(body, callerStatement)
	end
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local statementCapturedBefore, statementCapturedBeforeCall, statementCapturedBeforeTarget = capturedStatementDocument(
	"definition-statement-captured-before",
	true
)
expectProof(
	statementCapturedBefore,
	statementCapturedBeforeCall,
	statementCapturedBeforeTarget,
	"definition-statement-captured-before-current"
)
local statementCapturedAfter, statementCapturedAfterCall, statementCapturedAfterTarget = capturedStatementDocument(
	"definition-statement-captured-after",
	false
)
expectOriginFailure(statementCapturedAfter, statementCapturedAfterCall, statementCapturedAfterTarget)

local function unsupportedStatementDocument(prefix: string, targetKind: "index" | "global" | "malformed"): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local functionValue, _ = readInvocation(call, prefix .. "-function")
	local namespace = declaration(prefix .. "Namespace", prefix .. "-namespace")
	local statementTarget: any = if targetKind == "index"
		then {
			type = "AstExprIndexName",
			location = prefix .. "-function-target",
			expr = localExpression(namespace, prefix .. "-namespace-use"),
			index = "member",
		}
		else if targetKind == "global"
			then { type = "AstExprGlobal", location = prefix .. "-function-target", global = "global_target" }
			else "malformed"
	return document({
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(namespace, prefix .. "-namespace-declaration"),
		{
			type = "AstStatFunction",
			location = prefix .. "-definition",
			name = statementTarget,
			func = functionValue,
		},
		assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")),
	}), call, target
end

for _, kind in { "index", "global", "malformed" } do
	local prefix = "definition-statement-unsupported-" .. kind
	local fixture, call, target = unsupportedStatementDocument(prefix, kind :: "index" | "global" | "malformed")
	expectOriginFailure(fixture, call, target)
end

local unorderedStatementTarget = declaration("definitionStatementUnorderedTarget", "definition-statement-unordered-target")
local unorderedStatementCall = callExpression(unorderedStatementTarget, "definition-statement-unordered-read")
local unorderedStatementFunction, _ = readInvocation(unorderedStatementCall, "definition-statement-unordered-function")
local unorderedStatementHolder = declaration("definitionStatementUnorderedHolder", "definition-statement-unordered-holder")
expectOriginFailure(
	document({
		localStatement(unorderedStatementTarget, "definition-statement-unordered-target-declaration"),
		assignment(unorderedStatementTarget, "definition-statement-unordered-current"),
		localStatement(unorderedStatementHolder, "definition-statement-unordered-holder-declaration"),
		branchStatement("definition-statement-unordered", {
			functionStatement(unorderedStatementHolder, unorderedStatementFunction, "definition-statement-unordered-definition"),
		}, nil),
		callStatement(
			localInvocation(unorderedStatementHolder, "definition-statement-unordered-call", false),
			"definition-statement-unordered-call-statement"
		),
		assignmentValue(
			unorderedStatementTarget,
			"definition-statement-unordered-future-write",
			differentTarget("definition-statement-unordered-future-value")
		),
	}),
	unorderedStatementCall,
	unorderedStatementTarget
)

local recursiveStatementTarget = declaration("definitionStatementRecursiveTarget", "definition-statement-recursive-target")
local recursiveStatementCall = callExpression(recursiveStatementTarget, "definition-statement-recursive-read")
local recursiveStatementHolder = declaration("definitionStatementRecursiveHolder", "definition-statement-recursive-holder")
local recursiveStatementFunction, _ = invocationFromBody({
	callStatement(recursiveStatementCall, "definition-statement-recursive-read-statement"),
	callStatement(
		localInvocation(recursiveStatementHolder, "definition-statement-recursive-self-call", false),
		"definition-statement-recursive-self-statement"
	),
}, "definition-statement-recursive-function", nil, nil)
expectOriginFailure(
	document({
		localStatement(recursiveStatementTarget, "definition-statement-recursive-target-declaration"),
		assignment(recursiveStatementTarget, "definition-statement-recursive-current"),
		localStatement(recursiveStatementHolder, "definition-statement-recursive-holder-declaration"),
		functionStatement(recursiveStatementHolder, recursiveStatementFunction, "definition-statement-recursive-definition"),
		callStatement(
			localInvocation(recursiveStatementHolder, "definition-statement-recursive-entry", false),
			"definition-statement-recursive-entry-statement"
		),
		assignmentValue(
			recursiveStatementTarget,
			"definition-statement-recursive-future-write",
			differentTarget("definition-statement-recursive-future-value")
		),
	}),
	recursiveStatementCall,
	recursiveStatementTarget
)

local escapeStatementTarget = declaration("definitionStatementEscapeTarget", "definition-statement-escape-target")
local escapeStatementCall = callExpression(escapeStatementTarget, "definition-statement-escape-read")
local escapeStatementFunction, _ = readInvocation(escapeStatementCall, "definition-statement-escape-function")
local escapeStatementHolder = declaration("definitionStatementEscapeHolder", "definition-statement-escape-holder")
expectOriginFailure(
	document({
		localStatement(escapeStatementTarget, "definition-statement-escape-target-declaration"),
		assignment(escapeStatementTarget, "definition-statement-escape-current"),
		localStatement(escapeStatementHolder, "definition-statement-escape-holder-declaration"),
		functionStatement(escapeStatementHolder, escapeStatementFunction, "definition-statement-escape-definition"),
		callStatement(localInvocation(escapeStatementHolder, "definition-statement-escape-call", false), "definition-statement-escape-call-statement"),
		callStatement({
			type = "AstExprCall",
			location = "definition-statement-escape-consumer-call",
			func = Support.globalExpression("consume", "definition-statement-escape-consumer"),
			args = { localExpression(escapeStatementHolder, "definition-statement-escape-argument") },
			self = false,
		}, "definition-statement-escape-consumer-statement"),
		assignmentValue(escapeStatementTarget, "definition-statement-escape-future-write", differentTarget("definition-statement-escape-future-value")),
	}),
	escapeStatementCall,
	escapeStatementTarget
)
