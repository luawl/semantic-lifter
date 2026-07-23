--!strict

local TemporalTargetIdentity = require("./temporal_target_identity")
local Support = require("./temporal_test_support")
local InvocationSupport = require("./temporal_invocation_test_support")

type Record = Support.Record

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

local differentTarget = InvocationSupport.differentTarget
local localFunctionStatement = InvocationSupport.localFunctionStatement
local localInvocation = InvocationSupport.localInvocation
local wrappedExpression = InvocationSupport.wrappedExpression

local authenticatedOrigin: Record = { kind = "environment", name = "authenticated_target" }
local wrappers: { string } = { "AstExprGroup", "AstExprTypeAssertion", "AstExprInstantiate" }

local function returnStatement(value: Record, prefix: string): Record
	return { type = "AstStatReturn", location = prefix .. "-return", list = { value } }
end

local function returningFunction(value: Record, prefix: string, wrapped: boolean): Record
	local returned = if wrapped then wrappedExpression(value, prefix .. "-returned") else value
	local functionValue, _ = invocationFromBody({ returnStatement(returned, prefix) }, prefix, nil, nil)
	return functionValue
end

local function returningValuesFunction(values: { Record }, prefix: string): Record
	assert(#values >= 1)
	local functionValue = returningFunction(values[1], prefix, false)
	functionValue.body.body[1].list = values
	return functionValue
end

local function parameterInvoker(
	arguments: { Record },
	parameterCount: number,
	selectedIndex: number,
	prefix: string,
	wrapped: boolean
): (Record, Record, Record, { Record }, Record)
	assert(parameterCount >= 1 and selectedIndex >= 1 and selectedIndex <= parameterCount)
	local parameters: { Record } = {}
	for index = 1, parameterCount do
		table.insert(parameters, declaration(`{prefix}Parameter{index}`, `{prefix}-parameter-{index}`))
	end
	local callee: Record = localExpression(parameters[selectedIndex], prefix .. "-parameter-read")
	if wrapped then
		callee = wrappedExpression(callee, prefix .. "-parameter-callee")
	end
	local innerCall: Record = {
		type = "AstExprCall",
		location = prefix .. "-parameter-call",
		func = callee,
		args = {},
		self = false,
	}
	local returned = if wrapped then wrappedExpression(innerCall, prefix .. "-parameter-result") else innerCall
	local functionValue, rawCall = invocationFromBody(
		{ returnStatement(returned, prefix) },
		prefix,
		if wrapped then wrappers else nil,
		arguments
	)
	functionValue.args = parameters
	return if wrapped then wrappedExpression(rawCall, prefix .. "-outer-call") else rawCall,
		rawCall,
		functionValue,
		parameters,
		innerCall
end

local function parameterAliasInvoker(
	arguments: { Record },
	parameterCount: number,
	selectedIndex: number,
	aliasCount: number,
	prefix: string,
	wrapped: boolean
): (Record, Record, Record, { Record }, Record, { Record })
	assert(aliasCount >= 1)
	local value, rawCall, functionValue, parameters, innerCall = parameterInvoker(
		arguments,
		parameterCount,
		selectedIndex,
		prefix,
		wrapped
	)
	local aliases: { Record } = {}
	local source: Record = localExpression(parameters[selectedIndex], prefix .. "-alias-parameter-read")
	for index = 1, aliasCount do
		local alias = declaration(`{prefix}Alias{index}`, `{prefix}-alias-{index}`)
		table.insert(aliases, alias)
		table.insert(functionValue.body.body, index, {
			type = "AstStatLocal",
			location = `{prefix}-alias-statement-{index}`,
			vars = { alias },
			values = {
				if wrapped then wrappedExpression(source, `{prefix}-alias-value-{index}`) else source,
			},
		})
		source = localExpression(alias, `{prefix}-alias-read-{index}`)
	end
	innerCall.func = if wrapped then wrappedExpression(source, prefix .. "-alias-callee") else source
	return value, rawCall, functionValue, parameters, innerCall, aliases
end

local function parameterResultInvoker(
	arguments: { Record },
	parameterCount: number,
	selectedIndex: number,
	calleeAliasCount: number,
	resultAliasCount: number,
	prefix: string,
	wrapped: boolean
): (Record, Record, Record, { Record }, Record, { Record }, { Record })
	assert(resultAliasCount >= 0)
	local value, rawCall, functionValue, parameters, innerCall, calleeAliases = parameterAliasInvoker(
		arguments,
		parameterCount,
		selectedIndex,
		calleeAliasCount,
		prefix,
		wrapped
	)
	local body = functionValue.body.body
	local resultLocals: { Record } = {}
	local result = declaration(prefix .. "Result", prefix .. "-result")
	table.insert(resultLocals, result)
	table.insert(body, (#body), {
		type = "AstStatLocal",
		location = prefix .. "-result-statement",
		vars = { result },
		values = { if wrapped then wrappedExpression(innerCall, prefix .. "-result-value") else innerCall },
	})
	local source: Record = localExpression(result, prefix .. "-result-read")
	for index = 1, resultAliasCount do
		local alias = declaration(`{prefix}ResultAlias{index}`, `{prefix}-result-alias-{index}`)
		table.insert(resultLocals, alias)
		table.insert(body, (#body), {
			type = "AstStatLocal",
			location = `{prefix}-result-alias-statement-{index}`,
			vars = { alias },
			values = {
				if wrapped then wrappedExpression(source, `{prefix}-result-alias-value-{index}`) else source,
			},
		})
		source = localExpression(alias, `{prefix}-result-alias-read-{index}`)
	end
	body[#body].list = {
		if wrapped then wrappedExpression(source, prefix .. "-result-returned") else source,
	}
	return value, rawCall, functionValue, parameters, innerCall, calleeAliases, resultLocals
end

local function setLocalTargetCount(statement: Record, targetCount: number, prefix: string): { Record }
	assert(targetCount >= 1 and type(statement.vars) == "table" and type(statement.vars[1]) == "table")
	local targets: { Record } = { statement.vars[1] :: Record }
	for index = 2, targetCount do
		table.insert(targets, declaration(`{prefix}Target{index}`, `{prefix}-target-{index}`))
	end
	statement.vars = targets
	return targets
end

local function setSelectedLocalOrdinal(
	statement: Record,
	ordinal: number,
	width: number,
	prefix: string
): ({ Record }, { Record })
	assert(ordinal >= 1 and ordinal <= width)
	assert(type(statement.vars) == "table" and type(statement.vars[1]) == "table")
	assert(type(statement.values) == "table" and type(statement.values[1]) == "table")
	local selectedTarget = statement.vars[1] :: Record
	local selectedValue = statement.values[1] :: Record
	local targets: { Record } = {}
	local values: { Record } = {}
	for index = 1, width do
		table.insert(targets, if index == ordinal
			then selectedTarget
			else declaration(`{prefix}Target{index}`, `{prefix}-target-{index}`))
		table.insert(values, if index == ordinal then selectedValue else differentTarget(`{prefix}-value-{index}`))
	end
	statement.vars = targets
	statement.values = values
	return targets, values
end

local function setLocalValueCount(statement: Record, valueCount: number, prefix: string): { Record }
	assert(valueCount >= 1 and type(statement.values) == "table" and type(statement.values[1]) == "table")
	local values: { Record } = { statement.values[1] :: Record }
	for index = 2, valueCount do
		table.insert(values, differentTarget(`{prefix}-value-{index}`))
	end
	statement.values = values
	return values
end

local function expectProof(
	prefix: string,
	value: Record,
	before: { Record }?,
	after: { Record }?
)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local targetCall = callExpression(target, prefix .. "-target-read")
	local body: { Record } = {}
	if before ~= nil then
		for _, statement in before :: { Record } do
			table.insert(body, statement)
		end
	end
	table.insert(body, localStatement(target, prefix .. "-target-declaration"))
	table.insert(body, assignmentValue(target, prefix .. "-current", value))
	table.insert(body, callStatement(targetCall, prefix .. "-target-call-statement"))
	if after ~= nil then
		for _, statement in after :: { Record } do
			table.insert(body, statement)
		end
	end
	local proof = verifyOrigin(document(body), targetCall, target, authenticatedOrigin)
	assert(proof.definition_location == prefix .. "-current", `{prefix} lost its parameter factory result`)
end

local function expectExpressionFailure(fixture: Record, expression: Record)
	local analysis = TemporalTargetIdentity.analyze(fixture)
	assert(
		not TemporalTargetIdentity.matchesExpression(analysis, expression, authenticatedOrigin),
		`{expression.location} unexpectedly matched the authenticated origin`
	)
end

local function expectCallFailure(prefix: string, call: Record)
	expectExpressionFailure(document({ callStatement(call, prefix .. "-statement") }), call)
end

local rawCandidate = returningFunction(
	globalExpression("authenticated_target", "parameter-factory-raw-value"),
	"parameter-factory-raw-candidate",
	false
)

local function rawResultStatement(prefix: string): (Record, Record, Record)
	local call, _, functionValue, _, _, calleeAliases = parameterResultInvoker({
		rawCandidate,
	}, 1, 1, 1, 0, prefix, false)
	return call, functionValue.body.body[#calleeAliases + 1], functionValue
end

local function useAssignmentSnapshots(functionValue: Record, prefix: string)
	functionValue.body.body = Support.assignmentBackedSnapshots(functionValue.body.body, prefix)
end

local rawCall = parameterInvoker({ rawCandidate }, 1, 1, "parameter-factory-raw", false)
expectProof("parameter-factory-raw", rawCall, nil, nil)

local aliasCalleeCall = parameterAliasInvoker({ rawCandidate }, 1, 1, 1, "parameter-factory-alias-callee", false)
expectProof("parameter-factory-alias-callee", aliasCalleeCall, nil, nil)

local resultSnapshotCall = parameterResultInvoker({
	rawCandidate,
}, 1, 1, 1, 0, "parameter-factory-result-snapshot", false)
expectProof("parameter-factory-result-snapshot", resultSnapshotCall, nil, nil)

local projectionCandidate = returningValuesFunction({
	differentTarget("parameter-factory-projection-ignored"),
	globalExpression("authenticated_target", "parameter-factory-projection-selected"),
}, "parameter-factory-projection-candidate")
local projectionCall, _, projectionFunction, _, _, projectionCalleeAliases = parameterResultInvoker({
	projectionCandidate,
}, 1, 1, 2, 1, "parameter-factory-projection", false)
Support.setSingleValueTargetOrdinal(
	projectionFunction.body.body[#projectionCalleeAliases + 1],
	2,
	2,
	"parameter-factory-projection"
)
expectProof("parameter-factory-projection", projectionCall, nil, nil)
useAssignmentSnapshots(projectionFunction, "parameter-factory-assignment-projection")
expectProof("parameter-factory-assignment-projection", projectionCall, nil, nil)

local projectedCallableCandidate = returningValuesFunction({
	differentTarget("parameter-factory-projected-callee-ignored"),
	returningFunction(
		globalExpression("authenticated_target", "parameter-factory-projected-callee-selected"),
		"parameter-factory-projected-callee-returned",
		false
	),
}, "parameter-factory-projected-callee-candidate")
local projectedCallableCall, _, projectedCallableFunction, _, _, projectedCallableAliases, projectedCallableResults = parameterResultInvoker({
	projectedCallableCandidate,
}, 1, 1, 2, 1, "parameter-factory-projected-callee", false)
Support.setSingleValueTargetOrdinal(
	projectedCallableFunction.body.body[#projectedCallableAliases + 1],
	2,
	2,
	"parameter-factory-projected-callee"
)
projectedCallableFunction.body.body[#projectedCallableFunction.body.body].list = {
	callExpression(projectedCallableResults[#projectedCallableResults], "parameter-factory-projected-callee-read"),
}
expectProof("parameter-factory-projected-callee", projectedCallableCall, nil, nil)
useAssignmentSnapshots(projectedCallableFunction, "parameter-factory-projected-callee-assignment")
expectProof("parameter-factory-projected-callee-assignment", projectedCallableCall, nil, nil)

local parameterTailNestedFunction = returningValuesFunction({
	differentTarget("parameter-factory-tail-nested-ignored"),
	globalExpression("authenticated_target", "parameter-factory-tail-nested-selected"),
}, "parameter-factory-tail-nested")
local parameterTailCandidate = returningValuesFunction({
	differentTarget("parameter-factory-tail-leading"),
	{
		type = "AstExprCall",
		location = "parameter-factory-tail-nested-call",
		func = parameterTailNestedFunction,
		args = {},
		self = false,
	},
}, "parameter-factory-tail-candidate")
local parameterTailCall, _, parameterTailFunction, _, _, parameterTailAliases = parameterResultInvoker({
	parameterTailCandidate,
}, 1, 1, 2, 1, "parameter-factory-tail", false)
Support.setSingleValueTargetOrdinal(
	parameterTailFunction.body.body[#parameterTailAliases + 1],
	3,
	3,
	"parameter-factory-tail"
)
expectProof("parameter-factory-tail", parameterTailCall, nil, nil)
useAssignmentSnapshots(parameterTailFunction, "parameter-factory-tail-assignment")
expectProof("parameter-factory-tail-assignment", parameterTailCall, nil, nil)

local assignmentSnapshotCall, _, assignmentSnapshotFunction = parameterResultInvoker({
	rawCandidate,
}, 1, 1, 2, 1, "parameter-factory-assignment-snapshot", true)
useAssignmentSnapshots(assignmentSnapshotFunction, "parameter-factory-assignment-snapshot")
expectProof("parameter-factory-assignment-snapshot", assignmentSnapshotCall, nil, nil)

local multiTargetCall, _, multiTargetFunction, _, _, multiTargetCalleeAliases = parameterResultInvoker({
	rawCandidate,
}, 1, 1, 2, 1, "parameter-factory-multi-target", true)
setSelectedLocalOrdinal(multiTargetFunction.body.body[1], 2, 3, "parameter-factory-multi-target-callee-1")
setSelectedLocalOrdinal(multiTargetFunction.body.body[2], 3, 3, "parameter-factory-multi-target-callee-2")
setSelectedLocalOrdinal(
	multiTargetFunction.body.body[#multiTargetCalleeAliases + 1],
	2,
	3,
	"parameter-factory-multi-target-result"
)
setSelectedLocalOrdinal(
	multiTargetFunction.body.body[#multiTargetCalleeAliases + 2],
	3,
	3,
	"parameter-factory-multi-target-result-alias"
)
expectProof("parameter-factory-multi-target", multiTargetCall, nil, nil)
useAssignmentSnapshots(multiTargetFunction, "parameter-factory-assignment-mixed-ordinals")
expectProof("parameter-factory-assignment-mixed-ordinals", multiTargetCall, nil, nil)

local multiValueCall, multiValueStatement = rawResultStatement("parameter-factory-multi-value")
local multiValueTrailing: Record = {
	type = "AstExprCall",
	location = "parameter-factory-multi-value-trailing-call",
	func = globalExpression("observe", "parameter-factory-multi-value-trailing-callee"),
	args = {},
	self = false,
}
table.insert(multiValueStatement.values, multiValueTrailing)
expectProof("parameter-factory-multi-value", multiValueCall, nil, nil)
assert(multiValueStatement.values[2] == multiValueTrailing)

local values64Call, values64Statement, values64Function = rawResultStatement("parameter-factory-values-64")
setLocalValueCount(values64Statement, 64, "parameter-factory-values-64")
expectProof("parameter-factory-values-64", values64Call, nil, nil)
useAssignmentSnapshots(values64Function, "parameter-factory-assignment-values-64")
expectProof("parameter-factory-assignment-values-64", values64Call, nil, nil)

local values65Call, values65Statement, values65Function = rawResultStatement("parameter-factory-values-65")
setLocalValueCount(values65Statement, 65, "parameter-factory-values-65")
expectCallFailure("parameter-factory-values-65", values65Call)
useAssignmentSnapshots(values65Function, "parameter-factory-assignment-values-65")
expectCallFailure("parameter-factory-assignment-values-65", values65Call)

local targets64Call, targets64Statement, targets64Function = rawResultStatement("parameter-factory-targets-64")
setSelectedLocalOrdinal(targets64Statement, 64, 64, "parameter-factory-targets-64")
expectProof("parameter-factory-targets-64", targets64Call, nil, nil)
useAssignmentSnapshots(targets64Function, "parameter-factory-assignment-targets-64")
expectProof("parameter-factory-assignment-targets-64", targets64Call, nil, nil)

local targets65Call, targets65Statement, targets65Function = rawResultStatement("parameter-factory-targets-65")
setSelectedLocalOrdinal(targets65Statement, 65, 65, "parameter-factory-targets-65")
expectCallFailure("parameter-factory-targets-65", targets65Call)
useAssignmentSnapshots(targets65Function, "parameter-factory-assignment-targets-65")
expectCallFailure("parameter-factory-assignment-targets-65", targets65Call)

local laterTargetCall, laterTargetStatement, laterTargetFunction = rawResultStatement(
	"parameter-factory-later-target"
)
local laterTargets = setLocalTargetCount(
	laterTargetStatement,
	2,
	"parameter-factory-later-target"
)
laterTargetFunction.body.body[#laterTargetFunction.body.body].list = {
	localExpression(laterTargets[2], "parameter-factory-later-target-read"),
}
expectCallFailure("parameter-factory-later-target", laterTargetCall)

local returnedParameter = declaration("parameterFactoryReturnedParameter", "parameter-factory-returned-parameter")
local returnedParameterCandidate = returningFunction(
	localExpression(returnedParameter, "parameter-factory-returned-parameter-read"),
	"parameter-factory-returned-parameter-candidate",
	false
)
returnedParameterCandidate.args = { returnedParameter }
local returnedParameterCall, _, _, _, returnedParameterInnerCall = parameterResultInvoker({
	returnedParameterCandidate,
}, 1, 1, 2, 1, "parameter-factory-returned-parameter", false)
returnedParameterInnerCall.args = {
	globalExpression("authenticated_target", "parameter-factory-returned-parameter-argument"),
}
expectProof("parameter-factory-returned-parameter", returnedParameterCall, nil, nil)

local returnedLocal = declaration("parameterFactoryReturnedLocal", "parameter-factory-returned-local")
local returnedLocalCandidate, _ = invocationFromBody({
	localStatement(
		returnedLocal,
		"parameter-factory-returned-local-declaration",
		globalExpression("authenticated_target", "parameter-factory-returned-local-value")
	),
	returnStatement(localExpression(returnedLocal, "parameter-factory-returned-local-read"), "parameter-factory-returned-local"),
}, "parameter-factory-returned-local-candidate", nil, nil)
local returnedLocalCall = parameterResultInvoker({
	returnedLocalCandidate,
}, 1, 1, 3, 2, "parameter-factory-returned-local", true)
expectProof("parameter-factory-returned-local", returnedLocalCall, nil, nil)

local ordinalCandidate = returningFunction(
	globalExpression("authenticated_target", "parameter-factory-ordinal-value"),
	"parameter-factory-ordinal-candidate",
	true
)
local ordinalCall = parameterResultInvoker({
	differentTarget("parameter-factory-ordinal-other-1"),
	ordinalCandidate,
	differentTarget("parameter-factory-ordinal-other-2"),
	differentTarget("parameter-factory-ordinal-extra"),
}, 3, 2, 3, 3, "parameter-factory-ordinal", true)
expectProof("parameter-factory-ordinal", ordinalCall, nil, nil)

local immutableFactory = declaration("parameterFactoryImmutable", "parameter-factory-immutable")
local immutableCall = parameterResultInvoker({
	wrappedExpression(localExpression(immutableFactory, "parameter-factory-immutable-argument"), "parameter-factory-immutable-argument"),
}, 1, 1, 2, 1, "parameter-factory-immutable", true)
expectProof("parameter-factory-immutable", immutableCall, {
	localStatement(immutableFactory, "parameter-factory-immutable-declaration", returningFunction(
		globalExpression("authenticated_target", "parameter-factory-immutable-value"),
		"parameter-factory-immutable-function",
		false
	)),
}, nil)

local aliasSource = declaration("parameterFactoryAliasSource", "parameter-factory-alias-source")
local alias = declaration("parameterFactoryAlias", "parameter-factory-alias")
local aliasCall = parameterResultInvoker({
	localExpression(alias, "parameter-factory-alias-argument"),
}, 1, 1, 2, 1, "parameter-factory-alias", false)
expectProof("parameter-factory-alias", aliasCall, {
	localStatement(aliasSource, "parameter-factory-alias-source-declaration", returningFunction(
		globalExpression("authenticated_target", "parameter-factory-alias-value"),
		"parameter-factory-alias-function",
		false
	)),
	localStatement(
		alias,
		"parameter-factory-alias-declaration",
		localExpression(aliasSource, "parameter-factory-alias-source-read")
	),
}, nil)

local statementFactory = declaration("parameterFactoryStatement", "parameter-factory-statement")
local statementCall = parameterResultInvoker({
	localExpression(statementFactory, "parameter-factory-statement-argument"),
}, 1, 1, 2, 2, "parameter-factory-statement", false)
expectProof("parameter-factory-statement", statementCall, {
	localFunctionStatement(statementFactory, returningFunction(
		globalExpression("authenticated_target", "parameter-factory-statement-value"),
		"parameter-factory-statement-function",
		false
	), "parameter-factory-statement-declaration"),
}, nil)

local anchoredInvoker = declaration("parameterFactoryAnchoredInvoker", "parameter-factory-anchored-invoker")
local anchoredFactory = declaration("parameterFactoryAnchored", "parameter-factory-anchored")
local _, _, anchoredInvokerFunction = parameterResultInvoker({}, 1, 1, 3, 1, "parameter-factory-anchored-body", false)
local anchoredCall = localInvocation(anchoredInvoker, "parameter-factory-anchored", false)
anchoredCall.args = { localExpression(anchoredFactory, "parameter-factory-anchored-argument") }
expectProof("parameter-factory-anchored", anchoredCall, {
	localStatement(anchoredInvoker, "parameter-factory-anchored-invoker-declaration", anchoredInvokerFunction),
	localStatement(anchoredFactory, "parameter-factory-anchored-declaration"),
	assignmentValue(anchoredFactory, "parameter-factory-anchored-write", returningFunction(
		globalExpression("authenticated_target", "parameter-factory-anchored-value"),
		"parameter-factory-anchored-function",
		false
	)),
}, {
	assignmentValue(
		anchoredFactory,
		"parameter-factory-anchored-future-write",
		differentTarget("parameter-factory-anchored-future-value")
	),
})

local sameInvoker = declaration("parameterFactorySameInvoker", "parameter-factory-same-invoker")
local sameFactory = declaration("parameterFactorySame", "parameter-factory-same")
local sameTarget = declaration("parameterFactorySameTarget", "parameter-factory-same-target")
local sameTargetCall = callExpression(sameTarget, "parameter-factory-same-target-read")
local _, _, sameInvokerFunction = parameterResultInvoker({}, 1, 1, 2, 1, "parameter-factory-same-body", false)
local sameInvocation = localInvocation(sameInvoker, "parameter-factory-same", false)
sameInvocation.args = { localExpression(sameFactory, "parameter-factory-same-argument") }
local sameProof = verifyOrigin(document({
	localStatement(sameInvoker, "parameter-factory-same-invoker-declaration", sameInvokerFunction),
	localStatement(sameFactory, "parameter-factory-same-factory-declaration"),
	assignmentValue(sameFactory, "parameter-factory-same-old-write", returningFunction(
		globalExpression("authenticated_target", "parameter-factory-same-value"),
		"parameter-factory-same-old-function",
		false
	)),
	localStatement(sameTarget, "parameter-factory-same-target-declaration"),
	{
		type = "AstStatAssign",
		location = "parameter-factory-same-write",
		vars = {
			localExpression(sameFactory, "parameter-factory-same-factory-target"),
			localExpression(sameTarget, "parameter-factory-same-target-target"),
		},
		values = {
			returningFunction(
				differentTarget("parameter-factory-same-new-value"),
				"parameter-factory-same-new-function",
				false
			),
			sameInvocation,
		},
	},
	callStatement(sameTargetCall, "parameter-factory-same-target-call-statement"),
}), sameTargetCall, sameTarget, authenticatedOrigin)
assert(sameProof.definition_location == "parameter-factory-same-write")

local _, _, nestedForwarder = parameterResultInvoker({}, 1, 1, 2, 1, "parameter-factory-nested-inner", true)
local nestedCall, _, _, _, nestedInnerCall = parameterResultInvoker({
	nestedForwarder,
}, 1, 1, 3, 2, "parameter-factory-nested-outer", true)
nestedInnerCall.args = { rawCandidate }
expectProof("parameter-factory-nested", nestedCall, nil, nil)

local repeatedInvoker = declaration("parameterFactoryRepeatedInvoker", "parameter-factory-repeated-invoker")
local _, _, repeatedInvokerFunction = parameterResultInvoker({}, 1, 1, 2, 1, "parameter-factory-repeated-body", false)
local repeatedFirstCall = localInvocation(repeatedInvoker, "parameter-factory-repeated-first", false)
repeatedFirstCall.args = { rawCandidate }
local repeatedSecondCall = localInvocation(repeatedInvoker, "parameter-factory-repeated-second", false)
repeatedSecondCall.args = { rawCandidate }
local repeatedFirstTarget = declaration("parameterFactoryRepeatedFirstTarget", "parameter-factory-repeated-first-target")
local repeatedSecondTarget = declaration("parameterFactoryRepeatedSecondTarget", "parameter-factory-repeated-second-target")
local repeatedFirstTargetCall = callExpression(repeatedFirstTarget, "parameter-factory-repeated-first-target-read")
local repeatedSecondTargetCall = callExpression(repeatedSecondTarget, "parameter-factory-repeated-second-target-read")
local repeatedFixture = document({
	localStatement(repeatedInvoker, "parameter-factory-repeated-invoker-declaration", repeatedInvokerFunction),
	localStatement(repeatedFirstTarget, "parameter-factory-repeated-first-target-declaration"),
	assignmentValue(repeatedFirstTarget, "parameter-factory-repeated-first-current", repeatedFirstCall),
	callStatement(repeatedFirstTargetCall, "parameter-factory-repeated-first-target-statement"),
	localStatement(repeatedSecondTarget, "parameter-factory-repeated-second-target-declaration"),
	assignmentValue(repeatedSecondTarget, "parameter-factory-repeated-second-current", repeatedSecondCall),
	callStatement(repeatedSecondTargetCall, "parameter-factory-repeated-second-target-statement"),
})
assert(verifyOrigin(
	repeatedFixture,
	repeatedFirstTargetCall,
	repeatedFirstTarget,
	authenticatedOrigin
).definition_location == "parameter-factory-repeated-first-current")
assert(verifyOrigin(
	repeatedFixture,
	repeatedSecondTargetCall,
	repeatedSecondTarget,
	authenticatedOrigin
).definition_location == "parameter-factory-repeated-second-current")

local aliasDepth64Call = parameterAliasInvoker({
	rawCandidate,
}, 1, 1, 64, "parameter-factory-alias-depth-64", false)
expectProof("parameter-factory-alias-depth-64", aliasDepth64Call, nil, nil)

local aliasDepth65Call = parameterAliasInvoker({
	rawCandidate,
}, 1, 1, 65, "parameter-factory-alias-depth-65", false)
expectCallFailure("parameter-factory-alias-depth-65", aliasDepth65Call)

local resultCalleeDepth64Call = parameterResultInvoker({
	rawCandidate,
}, 1, 1, 64, 0, "parameter-factory-result-callee-depth-64", false)
expectProof("parameter-factory-result-callee-depth-64", resultCalleeDepth64Call, nil, nil)

local resultCalleeDepth65Call = parameterResultInvoker({
	rawCandidate,
}, 1, 1, 65, 0, "parameter-factory-result-callee-depth-65", false)
expectCallFailure("parameter-factory-result-callee-depth-65", resultCalleeDepth65Call)

local resultAliasDepth64Call = parameterResultInvoker({
	rawCandidate,
}, 1, 1, 1, 64, "parameter-factory-result-alias-depth-64", true)
expectProof("parameter-factory-result-alias-depth-64", resultAliasDepth64Call, nil, nil)

local resultAliasDepth65Call = parameterResultInvoker({
	rawCandidate,
}, 1, 1, 1, 65, "parameter-factory-result-alias-depth-65", false)
expectCallFailure("parameter-factory-result-alias-depth-65", resultAliasDepth65Call)

type ResultMutation = (Record, Record, { Record }, number) -> ()

local malformedResultCases: { { name: string, resultAliasCount: number, mutate: ResultMutation } } = {
	{
		name = "skipped",
		resultAliasCount = 2,
		mutate = function(functionValue: Record, _innerCall: Record, results: { Record }, resultIndex: number)
			functionValue.body.body[resultIndex + 2].values = {
				localExpression(results[1], "parameter-factory-result-skipped-read"),
			}
		end,
	},
	{
		name = "unrelated",
		resultAliasCount = 1,
		mutate = function(functionValue: Record, _innerCall: Record, _results: { Record }, resultIndex: number)
			functionValue.body.body[resultIndex + 1].values = {
				differentTarget("parameter-factory-result-unrelated-value"),
			}
		end,
	},
	{
		name = "second-call",
		resultAliasCount = 1,
		mutate = function(functionValue: Record, _innerCall: Record, results: { Record }, resultIndex: number)
			functionValue.body.body[resultIndex + 1].values = { {
				type = "AstExprCall",
				location = "parameter-factory-result-second-call",
				func = localExpression(results[1], "parameter-factory-result-second-callee"),
				args = {},
				self = false,
			} }
		end,
	},
	{
		name = "keyed-declaration",
		resultAliasCount = 0,
		mutate = function(functionValue: Record, _innerCall: Record, results: { Record }, resultIndex: number)
			functionValue.body.body[resultIndex].vars = {
				results[1],
				extra = declaration("parameterFactoryResultKeyed", "parameter-factory-result-keyed-extra"),
			} :: any
		end,
	},
	{
		name = "duplicate-targets",
		resultAliasCount = 0,
		mutate = function(functionValue: Record, _innerCall: Record, results: { Record }, resultIndex: number)
			functionValue.body.body[resultIndex].vars = { results[1], results[1] }
		end,
	},
	{
		name = "wrong-value-ordinal",
		resultAliasCount = 0,
		mutate = function(functionValue: Record, innerCall: Record, _results: { Record }, resultIndex: number)
			functionValue.body.body[resultIndex].values = {
				differentTarget("parameter-factory-result-wrong-value-first"),
				innerCall,
			}
		end,
	},
	{
		name = "empty-values",
		resultAliasCount = 0,
		mutate = function(functionValue: Record, _innerCall: Record, _results: { Record }, resultIndex: number)
			functionValue.body.body[resultIndex].values = {}
		end,
	},
	{
		name = "keyed-values",
		resultAliasCount = 0,
		mutate = function(functionValue: Record, innerCall: Record, _results: { Record }, resultIndex: number)
			functionValue.body.body[resultIndex].values = {
				innerCall,
				extra = differentTarget("parameter-factory-result-keyed-value"),
			} :: any
		end,
	},
	{
		name = "assignment",
		resultAliasCount = 0,
		mutate = function(functionValue: Record, innerCall: Record, results: { Record }, resultIndex: number)
			functionValue.body.body[resultIndex] = assignmentValue(
				results[1],
				"parameter-factory-result-assignment-write",
				innerCall
			)
		end,
	},
	{
		name = "effect",
		resultAliasCount = 0,
		mutate = function(functionValue: Record, _innerCall: Record, _results: { Record }, resultIndex: number)
			table.insert(functionValue.body.body, resultIndex + 1, {
				type = "AstStatExpr",
				location = "parameter-factory-result-effect-statement",
				expr = {
					type = "AstExprCall",
					location = "parameter-factory-result-effect-call",
					func = globalExpression("observe", "parameter-factory-result-effect-callee"),
					args = {},
					self = false,
				},
			})
		end,
	},
	{
		name = "control",
		resultAliasCount = 0,
		mutate = function(functionValue: Record, _innerCall: Record, _results: { Record }, resultIndex: number)
			table.insert(functionValue.body.body, resultIndex + 1, Support.branchStatement(
				"parameter-factory-result-control",
				{},
				nil
			))
		end,
	},
}

for _, case in malformedResultCases do
	local prefix = "parameter-factory-result-" .. case.name
	local call, _, functionValue, _, innerCall, calleeAliases, results = parameterResultInvoker({
		rawCandidate,
	}, 1, 1, 2, case.resultAliasCount, prefix, false)
	case.mutate(functionValue, innerCall, results, #calleeAliases + 1)
	expectCallFailure(prefix, call)
end

local trailingReturnCall, _, trailingReturnFunction = parameterResultInvoker({
	rawCandidate,
}, 1, 1, 2, 1, "parameter-factory-result-trailing-return", false)
table.insert(trailingReturnFunction.body.body[#trailingReturnFunction.body.body].list, differentTarget(
	"parameter-factory-result-trailing-return-value"
))
expectProof("parameter-factory-result-trailing-return", trailingReturnCall, nil, nil)

local function forwardingFunction(depth: number, prefix: string): Record
	assert(depth >= 1)
	local parameter = declaration(`{prefix}Parameter{depth}`, `{prefix}-parameter-{depth}`)
	local returned: Record
	if depth == 1 then
		returned = {
			type = "AstExprCall",
			location = prefix .. "-final-call",
			func = localExpression(parameter, prefix .. "-final-callee"),
			args = {},
			self = false,
		}
	else
		returned = {
			type = "AstExprCall",
			location = `{prefix}-forward-call-{depth}`,
			func = forwardingFunction(depth - 1, prefix),
			args = { localExpression(parameter, `{prefix}-forward-argument-{depth}`) },
			self = false,
		}
	end
	local functionValue, _ = invocationFromBody({ returnStatement(returned, `{prefix}-{depth}`) }, `{prefix}-{depth}`, nil, nil)
	functionValue.args = { parameter }
	return functionValue
end

local depthCandidate = returningFunction(
	globalExpression("authenticated_target", "parameter-factory-depth-value"),
	"parameter-factory-depth-candidate",
	false
)
local depth64Call: Record = {
	type = "AstExprCall",
	location = "parameter-factory-depth-64-call",
	func = forwardingFunction(63, "parameter-factory-depth-64"),
	args = { depthCandidate },
	self = false,
}
expectProof("parameter-factory-depth-64", depth64Call, nil, nil)

local depth65Call: Record = {
	type = "AstExprCall",
	location = "parameter-factory-depth-65-call",
	func = forwardingFunction(64, "parameter-factory-depth-65"),
	args = { depthCandidate },
	self = false,
}
local depth65Target = declaration("parameterFactoryDepth65Target", "parameter-factory-depth-65-target")
local depth65TargetCall = callExpression(depth65Target, "parameter-factory-depth-65-target-read")
expectFailure(function()
	verifyOrigin(document({
		localStatement(depth65Target, "parameter-factory-depth-65-target-declaration"),
		assignmentValue(depth65Target, "parameter-factory-depth-65-current", depth65Call),
		callStatement(depth65TargetCall, "parameter-factory-depth-65-target-call-statement"),
	}), depth65TargetCall, depth65Target, authenticatedOrigin)
end, "temporal target definition " .. depth65Target.location)

type AliasMutation = (Record, { Record }, Record, { Record }) -> ()
local malformedAliasCases: { { name: string, aliasCount: number, mutate: AliasMutation } } = {
	{
		name = "skipped",
		aliasCount = 3,
		mutate = function(functionValue: Record, aliases: { Record }, _innerCall: Record, _parameters: { Record })
			functionValue.body.body[3].values = {
				localExpression(aliases[1], "parameter-factory-alias-skipped-read"),
			}
		end,
	},
	{
		name = "unrelated",
		aliasCount = 2,
		mutate = function(functionValue: Record, _aliases: { Record }, _innerCall: Record, _parameters: { Record })
			functionValue.body.body[2].values = {
				differentTarget("parameter-factory-alias-unrelated-value"),
			}
		end,
	},
	{
		name = "self",
		aliasCount = 1,
		mutate = function(functionValue: Record, aliases: { Record }, _innerCall: Record, _parameters: { Record })
			functionValue.body.body[1].values = {
				localExpression(aliases[1], "parameter-factory-alias-self-read"),
			}
		end,
	},
	{
		name = "forward",
		aliasCount = 2,
		mutate = function(functionValue: Record, aliases: { Record }, _innerCall: Record, _parameters: { Record })
			functionValue.body.body[1].values = {
				localExpression(aliases[2], "parameter-factory-alias-forward-read"),
			}
		end,
	},
	{
		name = "duplicate",
		aliasCount = 2,
		mutate = function(functionValue: Record, aliases: { Record }, _innerCall: Record, _parameters: { Record })
			functionValue.body.body[2].vars = { aliases[1] }
		end,
	},
	{
		name = "keyed",
		aliasCount = 1,
		mutate = function(functionValue: Record, aliases: { Record }, _innerCall: Record, _parameters: { Record })
			functionValue.body.body[1].vars = {
				aliases[1],
				extra = declaration("parameterFactoryAliasKeyed", "parameter-factory-alias-keyed-extra"),
			} :: any
		end,
	},
	{
		name = "assignment",
		aliasCount = 1,
		mutate = function(functionValue: Record, aliases: { Record }, _innerCall: Record, parameters: { Record })
			functionValue.body.body[1] = assignmentValue(
				aliases[1],
				"parameter-factory-alias-assignment-write",
				localExpression(parameters[1], "parameter-factory-alias-assignment-value")
			)
		end,
	},
	{
		name = "effect",
		aliasCount = 1,
		mutate = function(functionValue: Record, _aliases: { Record }, _innerCall: Record, _parameters: { Record })
			table.insert(functionValue.body.body, 2, {
				type = "AstStatExpr",
				location = "parameter-factory-alias-effect-statement",
				expr = {
					type = "AstExprCall",
					location = "parameter-factory-alias-effect-call",
					func = globalExpression("observe", "parameter-factory-alias-effect-callee"),
					args = {},
					self = false,
				},
			})
		end,
	},
	{
		name = "control",
		aliasCount = 1,
		mutate = function(functionValue: Record, _aliases: { Record }, _innerCall: Record, _parameters: { Record })
			table.insert(functionValue.body.body, 2, Support.branchStatement(
				"parameter-factory-alias-control",
				{},
				nil
			))
		end,
	},
	{
		name = "skipped-callee",
		aliasCount = 2,
		mutate = function(_functionValue: Record, aliases: { Record }, innerCall: Record, _parameters: { Record })
			innerCall.func = localExpression(aliases[1], "parameter-factory-alias-skipped-callee-read")
		end,
	},
}

for _, case in malformedAliasCases do
	local prefix = "parameter-factory-alias-" .. case.name
	local call, _, functionValue, parameters, innerCall, aliases = parameterAliasInvoker({
		rawCandidate,
	}, 1, 1, case.aliasCount, prefix, false)
	case.mutate(functionValue, aliases, innerCall, parameters)
	expectCallFailure(prefix, call)
end

local capturedBodyFactory = declaration("parameterFactoryCapturedBody", "parameter-factory-captured-body")
local capturedBodyCall, _, capturedBodyFunction = parameterResultInvoker({
	differentTarget("parameter-factory-captured-body-argument"),
}, 1, 1, 1, 1, "parameter-factory-captured-body", false)
capturedBodyFunction.body.body[1].values = {
	localExpression(capturedBodyFactory, "parameter-factory-captured-body-read"),
}
expectExpressionFailure(document({
	localStatement(capturedBodyFactory, "parameter-factory-captured-body-declaration"),
	assignmentValue(capturedBodyFactory, "parameter-factory-captured-body-write", returningFunction(
		globalExpression("authenticated_target", "parameter-factory-captured-body-value"),
		"parameter-factory-captured-body-function",
		false
	)),
	callStatement(capturedBodyCall, "parameter-factory-captured-body-statement"),
}), capturedBodyCall)

local parameterCycleCall, parameterCycleRawCall, _, parameterCycleParameters = parameterAliasInvoker({
	rawCandidate,
}, 1, 1, 1, "parameter-factory-parameter-cycle", false)
parameterCycleRawCall.args = {
	localExpression(parameterCycleParameters[1], "parameter-factory-parameter-cycle-argument"),
}
expectCallFailure("parameter-factory-parameter-cycle", parameterCycleCall)

local missingCall = parameterResultInvoker({}, 1, 1, 1, 1, "parameter-factory-missing", false)
expectCallFailure("parameter-factory-missing", missingCall)

local methodCall, _, _, _, methodInnerCall = parameterResultInvoker({
	rawCandidate,
}, 1, 1, 1, 1, "parameter-factory-method", false)
methodInnerCall.self = true
expectCallFailure("parameter-factory-method", methodCall)

local nonfunctionCall = parameterResultInvoker({
	globalExpression("not_a_factory", "parameter-factory-nonfunction-argument"),
}, 1, 1, 2, 1, "parameter-factory-nonfunction", false)
expectCallFailure("parameter-factory-nonfunction", nonfunctionCall)

local indexedCall = parameterResultInvoker({
	{
		type = "AstExprIndexName",
		location = "parameter-factory-indexed-argument",
		expr = globalExpression("registry", "parameter-factory-indexed-root"),
		index = "factory",
	},
}, 1, 1, 2, 1, "parameter-factory-indexed", false)
expectCallFailure("parameter-factory-indexed", indexedCall)

local duplicateCall, _, duplicateFunction, duplicateParameters = parameterResultInvoker({
	rawCandidate,
	differentTarget("parameter-factory-duplicate-extra"),
}, 2, 1, 1, 1, "parameter-factory-duplicate", false)
duplicateFunction.args = { duplicateParameters[1], duplicateParameters[1] }
expectCallFailure("parameter-factory-duplicate", duplicateCall)

local keyedCall, keyedRawCall = parameterResultInvoker({
	rawCandidate,
}, 1, 1, 1, 1, "parameter-factory-keyed", false)
keyedRawCall.args = { rawCandidate, extra = differentTarget("parameter-factory-keyed-extra") } :: any
expectCallFailure("parameter-factory-keyed", keyedCall)

local reassignedCall, _, reassignedFunction, reassignedParameters = parameterInvoker({
	rawCandidate,
}, 1, 1, "parameter-factory-reassigned", false)
table.insert(reassignedFunction.body.body, 1, assignmentValue(
	reassignedParameters[1],
	"parameter-factory-reassigned-write",
	differentTarget("parameter-factory-reassigned-value")
))
expectCallFailure("parameter-factory-reassigned", reassignedCall)

local beforeInvoker = declaration("parameterFactoryBeforeInvoker", "parameter-factory-before-invoker")
local beforeFactory = declaration("parameterFactoryBefore", "parameter-factory-before")
local _, _, beforeInvokerFunction = parameterResultInvoker({}, 1, 1, 2, 1, "parameter-factory-before-body", false)
local beforeCall = localInvocation(beforeInvoker, "parameter-factory-before", false)
beforeCall.args = { localExpression(beforeFactory, "parameter-factory-before-argument") }
expectExpressionFailure(document({
	localStatement(beforeInvoker, "parameter-factory-before-invoker-declaration", beforeInvokerFunction),
	localStatement(beforeFactory, "parameter-factory-before-declaration"),
	callStatement(beforeCall, "parameter-factory-before-call-statement"),
	assignmentValue(beforeFactory, "parameter-factory-before-write", returningFunction(
		globalExpression("authenticated_target", "parameter-factory-before-value"),
		"parameter-factory-before-function",
		false
	)),
}), beforeCall)
