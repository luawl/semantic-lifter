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

local function returningFunction(value: Record, prefix: string, wrapped: boolean): Record
	local returned = if wrapped then wrappedExpression(value, prefix .. "-returned") else value
	local functionValue, _ = invocationFromBody({
		{ type = "AstStatReturn", location = prefix .. "-return", list = { returned } },
	}, prefix, if wrapped then wrappers else nil, nil)
	return functionValue
end

local function returningValuesFunction(values: { Record }, prefix: string): Record
	assert(#values >= 1)
	local functionValue = returningFunction(values[1], prefix, false)
	functionValue.body.body[1].list = values
	return functionValue
end

local function functionStatement(localNode: Record, functionValue: Record, location: string): Record
	return {
		type = "AstStatFunction",
		location = location,
		name = localExpression(localNode, location .. "-target"),
		func = functionValue,
	}
end

local function expectProof(
	prefix: string,
	before: { Record },
	after: { Record }?,
	factory: Record,
	wrapped: boolean,
	arguments: { Record }?
)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local targetCall = callExpression(target, prefix .. "-target-read")
	local factoryCall = localInvocation(factory, prefix .. "-factory", wrapped)
	if arguments ~= nil then
		factoryCall.args = arguments :: { Record }
	end
	local body: { Record } = {}
	for _, statement in before do
		table.insert(body, statement)
	end
	table.insert(body, localStatement(target, prefix .. "-target-declaration"))
	table.insert(body, assignmentValue(target, prefix .. "-current", factoryCall))
	table.insert(body, callStatement(targetCall, prefix .. "-target-call-statement"))
	if after ~= nil then
		for _, statement in after :: { Record } do
			table.insert(body, statement)
		end
	end
	local proof = verifyOrigin(document(body), targetCall, target, authenticatedOrigin)
	assert(proof.definition_location == prefix .. "-current", `{prefix} lost its statement-defined factory result`)
end

local function expectExpressionFailure(fixture: Record, expression: Record)
	local analysis = TemporalTargetIdentity.analyze(fixture)
	assert(not TemporalTargetIdentity.matchesExpression(analysis, expression, authenticatedOrigin))
end

local function capturedOwner(
	factory: Record,
	prefix: string,
	wrapped: boolean,
	discardFirst: boolean
): (Record, Record, Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local targetCall = callExpression(target, prefix .. "-target-read")
	local factoryCall = localInvocation(factory, prefix .. "-factory", wrapped)
	local body: { Record } = {}
	if discardFirst then
		table.insert(body, callStatement(
			localInvocation(factory, prefix .. "-discarded-factory", false),
			prefix .. "-discarded-factory-statement"
		))
	end
	table.insert(body, localStatement(target, prefix .. "-target-declaration"))
	table.insert(body, assignmentValue(target, prefix .. "-current", factoryCall))
	table.insert(body, callStatement(targetCall, prefix .. "-target-call-statement"))
	local functionValue, _ = invocationFromBody(body, prefix .. "-owner-function", nil, nil)
	local owner = declaration(prefix .. "Owner", prefix .. "-owner")
	return localStatement(owner, prefix .. "-owner-declaration", functionValue),
		callStatement(localInvocation(owner, prefix .. "-owner-call", false), prefix .. "-owner-call-statement"),
		targetCall,
		target,
		factoryCall
end

local function capturedSnapshotInvocation(
	factory: Record,
	prefix: string,
	calleeAliasCount: number,
	resultAliasCount: number?,
	wrapped: boolean
): (Record, Record, Record)
	assert(calleeAliasCount >= 1 and (resultAliasCount == nil or resultAliasCount >= 0))
	local body: { Record } = {}
	local source: Record = localExpression(factory, prefix .. "-factory-read")
	local finalAlias: Record? = nil
	for index = 1, calleeAliasCount do
		local alias = declaration(`{prefix}Alias{index}`, `{prefix}-alias-{index}`)
		table.insert(body, localStatement(
			alias,
			`{prefix}-alias-statement-{index}`,
			if wrapped then wrappedExpression(source, `{prefix}-alias-value-{index}`) else source
		))
		source = localExpression(alias, `{prefix}-alias-read-{index}`)
		finalAlias = alias
	end
	local innerCall = localInvocation(finalAlias :: Record, prefix .. "-alias-call", wrapped)
	local returned: Record = innerCall
	if resultAliasCount ~= nil then
		local result = declaration(prefix .. "Result", prefix .. "-result")
		table.insert(body, localStatement(
			result,
			prefix .. "-result-statement",
			if wrapped then wrappedExpression(innerCall, prefix .. "-result-value") else innerCall
		))
		source = localExpression(result, prefix .. "-result-read")
		for index = 1, resultAliasCount :: number do
			local alias = declaration(`{prefix}ResultAlias{index}`, `{prefix}-result-alias-{index}`)
			table.insert(body, localStatement(
				alias,
				`{prefix}-result-alias-statement-{index}`,
				if wrapped then wrappedExpression(source, `{prefix}-result-alias-value-{index}`) else source
			))
			source = localExpression(alias, `{prefix}-result-alias-read-{index}`)
		end
		returned = source
	end
	table.insert(body, {
		type = "AstStatReturn",
		location = prefix .. "-return",
		list = { if wrapped then wrappedExpression(returned, prefix .. "-returned") else returned },
	})
	local functionValue, call = invocationFromBody(
		body,
		prefix .. "-owner",
		if wrapped then wrappers else nil,
		nil
	)
	return functionValue, call, innerCall
end

local function expectSnapshotProof(prefix: string, before: { Record }, value: Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local targetCall = callExpression(target, prefix .. "-target-read")
	local body = table.clone(before)
	table.insert(body, localStatement(target, prefix .. "-target-declaration"))
	table.insert(body, assignmentValue(target, prefix .. "-current", value))
	table.insert(body, callStatement(targetCall, prefix .. "-target-call-statement"))
	local proof = verifyOrigin(document(body), targetCall, target, authenticatedOrigin)
	assert(proof.definition_location == prefix .. "-current", `{prefix} lost its captured snapshot result`)
end

local directFactory = declaration("statementFactoryDirect", "statement-factory-direct")
expectProof("statement-factory-direct", {
	localFunctionStatement(directFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-direct-value"),
		"statement-factory-direct-function",
		false
	), "statement-factory-direct-declaration"),
}, nil, directFactory, true, nil)

local assignedFactory = declaration("statementFactoryAssigned", "statement-factory-assigned")
expectProof("statement-factory-assigned", {
	localStatement(assignedFactory, "statement-factory-assigned-local"),
	functionStatement(assignedFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-assigned-value"),
		"statement-factory-assigned-function",
		true
	), "statement-factory-assigned-definition"),
}, nil, assignedFactory, false, nil)

local repeatedCallFactory = declaration("statementFactoryRepeatedCall", "statement-factory-repeated-call")
expectProof("statement-factory-repeated-call", {
	localFunctionStatement(repeatedCallFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-repeated-call-value"),
		"statement-factory-repeated-call-function",
		false
	), "statement-factory-repeated-call-declaration"),
	callStatement(
		localInvocation(repeatedCallFactory, "statement-factory-repeated-call-discarded", false),
		"statement-factory-repeated-call-discarded-statement"
	),
}, nil, repeatedCallFactory, false, nil)

local replacementFactory = declaration("statementFactoryReplacement", "statement-factory-replacement")
expectProof("statement-factory-replacement", {
	localFunctionStatement(replacementFactory, returningFunction(
		differentTarget("statement-factory-replacement-old-value"),
		"statement-factory-replacement-old-function",
		false
	), "statement-factory-replacement-declaration"),
	functionStatement(replacementFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-replacement-value"),
		"statement-factory-replacement-function",
		false
	), "statement-factory-replacement-definition"),
}, nil, replacementFactory, true, nil)

local futureFactory = declaration("statementFactoryFuture", "statement-factory-future")
expectProof("statement-factory-future", {
	localStatement(futureFactory, "statement-factory-future-local"),
	functionStatement(futureFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-future-value"),
		"statement-factory-future-function",
		false
	), "statement-factory-future-definition"),
}, {
	functionStatement(futureFactory, returningFunction(
		differentTarget("statement-factory-future-replacement-value"),
		"statement-factory-future-replacement-function",
		false
	), "statement-factory-future-replacement"),
}, futureFactory, false, nil)

local aliasFactory = declaration("statementFactoryAliasSource", "statement-factory-alias-source")
local alias = declaration("statementFactoryAlias", "statement-factory-alias")
expectProof("statement-factory-alias", {
	localFunctionStatement(aliasFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-alias-value"),
		"statement-factory-alias-function",
		false
	), "statement-factory-alias-source-declaration"),
	localStatement(
		alias,
		"statement-factory-alias-declaration",
		localExpression(aliasFactory, "statement-factory-alias-source-read")
	),
}, {
	functionStatement(aliasFactory, returningFunction(
		differentTarget("statement-factory-alias-replacement-value"),
		"statement-factory-alias-replacement-function",
		false
	), "statement-factory-alias-replacement"),
}, alias, false, nil)

local parameter = declaration("statementFactoryParameter", "statement-factory-parameter")
local parameterFunction = returningFunction(
	localExpression(parameter, "statement-factory-parameter-read"),
	"statement-factory-parameter-function",
	false
)
parameterFunction.args = { parameter }
local parameterFactory = declaration("statementFactoryParameterCallee", "statement-factory-parameter-callee")
expectProof("statement-factory-parameter", {
	localFunctionStatement(parameterFactory, parameterFunction, "statement-factory-parameter-declaration"),
}, nil, parameterFactory, false, {
	globalExpression("authenticated_target", "statement-factory-parameter-argument"),
})

local function versionDocument(definitionCount: number, prefix: string): (Record, Record, Record)
	assert(definitionCount >= 2)
	local factory = declaration(prefix .. "Factory", prefix .. "-factory")
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local targetCall = callExpression(target, prefix .. "-target-read")
	local body: { Record } = { localStatement(factory, prefix .. "-local") }
	for index = 2, definitionCount do
		local value = if index == definitionCount
			then globalExpression("authenticated_target", `{prefix}-value`)
			else differentTarget(`{prefix}-value-{index}`)
		table.insert(body, functionStatement(factory, returningFunction(
			value,
			`{prefix}-function-{index}`,
			false
		), `{prefix}-definition-{index}`))
	end
	table.insert(body, localStatement(target, prefix .. "-target-declaration"))
	table.insert(body, assignmentValue(
		target,
		prefix .. "-current",
		localInvocation(factory, prefix .. "-factory-call", false)
	))
	table.insert(body, callStatement(targetCall, prefix .. "-target-call-statement"))
	return document(body), targetCall, target
end

local versions64Fixture, versions64Call, versions64Target = versionDocument(64, "statement-factory-versions-64")
local versions64Proof = verifyOrigin(versions64Fixture, versions64Call, versions64Target, authenticatedOrigin)
assert(versions64Proof.definition_location == "statement-factory-versions-64-current")

local versions65Fixture, versions65Call, versions65Target = versionDocument(65, "statement-factory-versions-65")
expectFailure(function()
	verifyOrigin(versions65Fixture, versions65Call, versions65Target, authenticatedOrigin)
end, "temporal target definition " .. versions65Target.location)

local beforeFactory = declaration("statementFactoryBefore", "statement-factory-before")
local beforeCall = localInvocation(beforeFactory, "statement-factory-before-call", false)
expectExpressionFailure(document({
	callStatement(beforeCall, "statement-factory-before-call-statement"),
	localFunctionStatement(beforeFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-before-value"),
		"statement-factory-before-function",
		false
	), "statement-factory-before-declaration"),
}), beforeCall)

local branchFactory = declaration("statementFactoryBranch", "statement-factory-branch")
local branchCall = localInvocation(branchFactory, "statement-factory-branch-call", false)
expectExpressionFailure(document({
	localStatement(branchFactory, "statement-factory-branch-local"),
	Support.branchStatement("statement-factory-branch", {
		functionStatement(branchFactory, returningFunction(
			globalExpression("authenticated_target", "statement-factory-branch-value"),
			"statement-factory-branch-function",
			false
		), "statement-factory-branch-definition"),
	}, nil),
	callStatement(branchCall, "statement-factory-branch-call-statement"),
}), branchCall)

local repeatedFactory = declaration("statementFactoryRepeated", "statement-factory-repeated")
local repeatedCall = localInvocation(repeatedFactory, "statement-factory-repeated-call", false)
expectExpressionFailure(document({
	localStatement(repeatedFactory, "statement-factory-repeated-local"),
	Support.whileStatement("statement-factory-repeated-loop", {
		functionStatement(repeatedFactory, returningFunction(
			globalExpression("authenticated_target", "statement-factory-repeated-value"),
			"statement-factory-repeated-function",
			false
		), "statement-factory-repeated-definition"),
		callStatement(repeatedCall, "statement-factory-repeated-call-statement"),
	}),
}), repeatedCall)

local capturedFactory = declaration("statementFactoryCaptured", "statement-factory-captured")
local capturedOwnerDeclaration, capturedOwnerCall, capturedTargetCall, capturedTarget, _ = capturedOwner(
	capturedFactory,
	"statement-factory-captured",
	true,
	true
)
local capturedProof = verifyOrigin(document({
	localFunctionStatement(capturedFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-value"),
		"statement-factory-captured-function",
		false
	), "statement-factory-captured-declaration"),
	capturedOwnerDeclaration,
	capturedOwnerCall,
}), capturedTargetCall, capturedTarget, authenticatedOrigin)
assert(capturedProof.definition_location == "statement-factory-captured-current")

local capturedSnapshotFactory = declaration(
	"statementFactoryCapturedSnapshot",
	"statement-factory-captured-snapshot"
)
local _, capturedSnapshotCall = capturedSnapshotInvocation(
	capturedSnapshotFactory,
	"statement-factory-captured-snapshot",
	1,
	nil,
	false
)
expectSnapshotProof("statement-factory-captured-snapshot", {
	localFunctionStatement(capturedSnapshotFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-snapshot-value"),
		"statement-factory-captured-snapshot-function",
		false
	), "statement-factory-captured-snapshot-declaration"),
}, capturedSnapshotCall)

local capturedAssignmentFactory = declaration(
	"statementFactoryCapturedAssignment",
	"statement-factory-captured-assignment"
)
local capturedAssignmentFunction, capturedAssignmentCall = capturedSnapshotInvocation(
	capturedAssignmentFactory,
	"statement-factory-captured-assignment",
	2,
	1,
	true
)
capturedAssignmentFunction.body.body = Support.assignmentBackedSnapshots(
	capturedAssignmentFunction.body.body,
	"statement-factory-captured-assignment"
)
expectSnapshotProof("statement-factory-captured-assignment", {
	localFunctionStatement(capturedAssignmentFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-assignment-value"),
		"statement-factory-captured-assignment-function",
		false
	), "statement-factory-captured-assignment-declaration"),
}, capturedAssignmentCall)

local capturedProjectionFactory = declaration(
	"statementFactoryCapturedProjection",
	"statement-factory-captured-projection"
)
local capturedProjectionFunction, capturedProjectionCall = capturedSnapshotInvocation(
	capturedProjectionFactory,
	"statement-factory-captured-projection",
	1,
	1,
	false
)
Support.setSingleValueTargetOrdinal(
	capturedProjectionFunction.body.body[2],
	2,
	2,
	"statement-factory-captured-projection"
)
expectSnapshotProof("statement-factory-captured-projection", {
	localFunctionStatement(capturedProjectionFactory, returningValuesFunction({
		differentTarget("statement-factory-captured-projection-ignored"),
		globalExpression("authenticated_target", "statement-factory-captured-projection-selected"),
	}, "statement-factory-captured-projection-function"), "statement-factory-captured-projection-declaration"),
}, capturedProjectionCall)

local capturedProjectedCallableFactory = declaration(
	"statementFactoryCapturedProjectedCallable",
	"statement-factory-captured-projected-callee"
)
local capturedProjectedCallableFunction, capturedProjectedCallableCall = capturedSnapshotInvocation(
	capturedProjectedCallableFactory,
	"statement-factory-captured-projected-callee",
	2,
	1,
	false
)
Support.setSingleValueTargetOrdinal(
	capturedProjectedCallableFunction.body.body[3],
	2,
	2,
	"statement-factory-captured-projected-callee"
)
local capturedProjectedCallableReturn = capturedProjectedCallableFunction.body.body[#capturedProjectedCallableFunction.body.body]
local capturedProjectedCallableRead = capturedProjectedCallableReturn.list[1]
assert(type(capturedProjectedCallableRead) == "table" and capturedProjectedCallableRead.type == "AstExprLocal")
capturedProjectedCallableReturn.list[1] = callExpression(
	capturedProjectedCallableRead["local"],
	"statement-factory-captured-projected-callee-read"
)
local capturedProjectedCallablePrelude = {
	localFunctionStatement(capturedProjectedCallableFactory, returningValuesFunction({
		differentTarget("statement-factory-captured-projected-callee-ignored"),
		returningFunction(
			globalExpression("authenticated_target", "statement-factory-captured-projected-callee-selected"),
			"statement-factory-captured-projected-callee-returned",
			false
		),
	}, "statement-factory-captured-projected-callee-function"), "statement-factory-captured-projected-callee-declaration"),
}
expectSnapshotProof(
	"statement-factory-captured-projected-callee",
	capturedProjectedCallablePrelude,
	capturedProjectedCallableCall
)
capturedProjectedCallableFunction.body.body = Support.assignmentBackedSnapshots(
	capturedProjectedCallableFunction.body.body,
	"statement-factory-captured-projected-callee-assignment"
)
expectSnapshotProof(
	"statement-factory-captured-projected-callee-assignment",
	capturedProjectedCallablePrelude,
	capturedProjectedCallableCall
)

local capturedTailFactory = declaration("statementFactoryCapturedTail", "statement-factory-captured-tail")
local capturedTailFunction, capturedTailCall = capturedSnapshotInvocation(
	capturedTailFactory,
	"statement-factory-captured-tail",
	2,
	1,
	false
)
Support.setSingleValueTargetOrdinal(
	capturedTailFunction.body.body[3],
	3,
	3,
	"statement-factory-captured-tail"
)
local capturedTailNested = returningValuesFunction({
	differentTarget("statement-factory-captured-tail-nested-ignored"),
	globalExpression("authenticated_target", "statement-factory-captured-tail-nested-selected"),
}, "statement-factory-captured-tail-nested")
local capturedTailPrelude = {
	localFunctionStatement(capturedTailFactory, returningValuesFunction({
		differentTarget("statement-factory-captured-tail-leading"),
		{
			type = "AstExprCall",
			location = "statement-factory-captured-tail-nested-call",
			func = capturedTailNested,
			args = {},
			self = false,
		},
	}, "statement-factory-captured-tail-function"), "statement-factory-captured-tail-declaration"),
}
expectSnapshotProof("statement-factory-captured-tail", capturedTailPrelude, capturedTailCall)
capturedTailFunction.body.body = Support.assignmentBackedSnapshots(
	capturedTailFunction.body.body,
	"statement-factory-captured-tail-assignment"
)
expectSnapshotProof("statement-factory-captured-tail-assignment", capturedTailPrelude, capturedTailCall)

local capturedMultiTargetFactory = declaration(
	"statementFactoryCapturedMultiTarget",
	"statement-factory-captured-multi-target"
)
local capturedMultiTargetFunction, capturedMultiTargetCall = capturedSnapshotInvocation(
	capturedMultiTargetFactory,
	"statement-factory-captured-multi-target",
	2,
	1,
	true
)
local capturedMultiTargetCallee = capturedMultiTargetFunction.body.body[1]
local capturedMultiTargetSelectedCallee = capturedMultiTargetCallee.vars[1]
local capturedMultiTargetSelectedCalleeValue = capturedMultiTargetCallee.values[1]
capturedMultiTargetCallee.vars = {
	declaration("statementFactoryCapturedMultiTargetCalleeExtra", "statement-factory-captured-multi-target-callee-extra"),
	capturedMultiTargetSelectedCallee,
}
capturedMultiTargetCallee.values = {
	differentTarget("statement-factory-captured-multi-target-callee-ignored"),
	capturedMultiTargetSelectedCalleeValue,
}
local capturedMultiTargetTrailing: Record = {
	type = "AstExprCall",
	location = "statement-factory-captured-multi-target-trailing-call",
	func = globalExpression("observe", "statement-factory-captured-multi-target-trailing-callee"),
	args = {},
	self = false,
}
local capturedMultiTargetResult = capturedMultiTargetFunction.body.body[3]
local capturedMultiTargetSelectedResult = capturedMultiTargetResult.vars[1]
local capturedMultiTargetSelectedResultValue = capturedMultiTargetResult.values[1]
capturedMultiTargetResult.vars = {
	declaration("statementFactoryCapturedMultiTargetResultExtra", "statement-factory-captured-multi-target-result-extra"),
	capturedMultiTargetSelectedResult,
}
capturedMultiTargetResult.values = { capturedMultiTargetTrailing, capturedMultiTargetSelectedResultValue }
expectSnapshotProof("statement-factory-captured-multi-target", {
	localFunctionStatement(capturedMultiTargetFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-multi-target-value"),
		"statement-factory-captured-multi-target-function",
		false
	), "statement-factory-captured-multi-target-declaration"),
}, capturedMultiTargetCall)
assert(capturedMultiTargetFunction.body.body[3].values[1] == capturedMultiTargetTrailing)
capturedMultiTargetFunction.body.body = Support.assignmentBackedSnapshots(
	capturedMultiTargetFunction.body.body,
	"statement-factory-captured-assignment-ordinals"
)
expectSnapshotProof("statement-factory-captured-assignment-ordinals", {
	localFunctionStatement(capturedMultiTargetFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-assignment-ordinals-value"),
		"statement-factory-captured-assignment-ordinals-function",
		false
	), "statement-factory-captured-assignment-ordinals-declaration"),
}, capturedMultiTargetCall)

local capturedStatementFactory = declaration(
	"statementFactoryCapturedStatement",
	"statement-factory-captured-statement"
)
local capturedStatementOwnerDeclaration, capturedStatementOwnerCall, capturedStatementTargetCall,
	capturedStatementTarget, _ = capturedOwner(
		capturedStatementFactory,
		"statement-factory-captured-statement",
		false,
		false
	)
local capturedStatementProof = verifyOrigin(document({
	localStatement(capturedStatementFactory, "statement-factory-captured-statement-local"),
	functionStatement(capturedStatementFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-statement-value"),
		"statement-factory-captured-statement-function",
		false
	), "statement-factory-captured-statement-definition"),
	capturedStatementOwnerDeclaration,
	capturedStatementOwnerCall,
}), capturedStatementTargetCall, capturedStatementTarget, authenticatedOrigin)
assert(capturedStatementProof.definition_location == "statement-factory-captured-statement-current")

local _, capturedStatementSnapshotCall = capturedSnapshotInvocation(
	capturedStatementFactory,
	"statement-factory-captured-statement-snapshot",
	2,
	2,
	true
)
expectSnapshotProof("statement-factory-captured-statement-snapshot", {
	localStatement(capturedStatementFactory, "statement-factory-captured-statement-snapshot-local"),
	functionStatement(capturedStatementFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-statement-snapshot-value"),
		"statement-factory-captured-statement-snapshot-function",
		true
	), "statement-factory-captured-statement-snapshot-definition"),
}, capturedStatementSnapshotCall)

local capturedAliasFactory = declaration(
	"statementFactoryCapturedAliasFactory",
	"statement-factory-captured-alias-factory"
)
local capturedAlias = declaration("statementFactoryCapturedAlias", "statement-factory-captured-alias")
local _, capturedAliasSnapshotCall = capturedSnapshotInvocation(
	capturedAlias,
	"statement-factory-captured-alias-snapshot",
	3,
	3,
	true
)
expectSnapshotProof("statement-factory-captured-alias-snapshot", {
	localStatement(capturedAliasFactory, "statement-factory-captured-alias-factory-declaration", returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-alias-value"),
		"statement-factory-captured-alias-function",
		false
	)),
	localStatement(
		capturedAlias,
		"statement-factory-captured-alias-declaration",
		localExpression(capturedAliasFactory, "statement-factory-captured-alias-source")
	),
}, capturedAliasSnapshotCall)

local capturedDepthFactory = declaration("statementFactoryCapturedDepth", "statement-factory-captured-depth")
local _, capturedDepth64Call = capturedSnapshotInvocation(
	capturedDepthFactory,
	"statement-factory-captured-depth-64",
	64,
	64,
	false
)
expectSnapshotProof("statement-factory-captured-depth-64", {
	localFunctionStatement(capturedDepthFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-depth-value"),
		"statement-factory-captured-depth-function",
		false
	), "statement-factory-captured-depth-declaration"),
}, capturedDepth64Call)

local _, capturedCalleeDepth65Call = capturedSnapshotInvocation(
	capturedDepthFactory,
	"statement-factory-captured-callee-depth-65",
	65,
	0,
	false
)
expectExpressionFailure(document({
	localFunctionStatement(capturedDepthFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-callee-depth-65-value"),
		"statement-factory-captured-callee-depth-65-function",
		false
	), "statement-factory-captured-callee-depth-65-declaration"),
	callStatement(capturedCalleeDepth65Call, "statement-factory-captured-callee-depth-65-statement"),
}), capturedCalleeDepth65Call)

local _, capturedResultDepth65Call = capturedSnapshotInvocation(
	capturedDepthFactory,
	"statement-factory-captured-result-depth-65",
	1,
	65,
	false
)
expectExpressionFailure(document({
	localFunctionStatement(capturedDepthFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-result-depth-65-value"),
		"statement-factory-captured-result-depth-65-function",
		false
	), "statement-factory-captured-result-depth-65-declaration"),
	callStatement(capturedResultDepth65Call, "statement-factory-captured-result-depth-65-statement"),
}), capturedResultDepth65Call)

local capturedRepeatedFactory = declaration(
	"statementFactoryCapturedRepeated",
	"statement-factory-captured-repeated"
)
local capturedRepeatedInvoker = declaration(
	"statementFactoryCapturedRepeatedInvoker",
	"statement-factory-captured-repeated-invoker"
)
local capturedRepeatedFunction, _, _ = capturedSnapshotInvocation(
	capturedRepeatedFactory,
	"statement-factory-captured-repeated-body",
	2,
	1,
	false
)
local capturedRepeatedFirstCall = localInvocation(
	capturedRepeatedInvoker,
	"statement-factory-captured-repeated-first",
	false
)
local capturedRepeatedSecondCall = localInvocation(
	capturedRepeatedInvoker,
	"statement-factory-captured-repeated-second",
	false
)
local capturedRepeatedFirstTarget = declaration(
	"statementFactoryCapturedRepeatedFirstTarget",
	"statement-factory-captured-repeated-first-target"
)
local capturedRepeatedSecondTarget = declaration(
	"statementFactoryCapturedRepeatedSecondTarget",
	"statement-factory-captured-repeated-second-target"
)
local capturedRepeatedFirstTargetCall = callExpression(
	capturedRepeatedFirstTarget,
	"statement-factory-captured-repeated-first-target-read"
)
local capturedRepeatedSecondTargetCall = callExpression(
	capturedRepeatedSecondTarget,
	"statement-factory-captured-repeated-second-target-read"
)
local capturedRepeatedFixture = document({
	localFunctionStatement(capturedRepeatedFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-repeated-value"),
		"statement-factory-captured-repeated-function",
		false
	), "statement-factory-captured-repeated-declaration"),
	localStatement(
		capturedRepeatedInvoker,
		"statement-factory-captured-repeated-invoker-declaration",
		capturedRepeatedFunction
	),
	localStatement(capturedRepeatedFirstTarget, "statement-factory-captured-repeated-first-target-declaration"),
	assignmentValue(
		capturedRepeatedFirstTarget,
		"statement-factory-captured-repeated-first-current",
		capturedRepeatedFirstCall
	),
	callStatement(capturedRepeatedFirstTargetCall, "statement-factory-captured-repeated-first-target-statement"),
	localStatement(capturedRepeatedSecondTarget, "statement-factory-captured-repeated-second-target-declaration"),
	assignmentValue(
		capturedRepeatedSecondTarget,
		"statement-factory-captured-repeated-second-current",
		capturedRepeatedSecondCall
	),
	callStatement(capturedRepeatedSecondTargetCall, "statement-factory-captured-repeated-second-target-statement"),
})
assert(verifyOrigin(
	capturedRepeatedFixture,
	capturedRepeatedFirstTargetCall,
	capturedRepeatedFirstTarget,
	authenticatedOrigin
).definition_location == "statement-factory-captured-repeated-first-current")
assert(verifyOrigin(
	capturedRepeatedFixture,
	capturedRepeatedSecondTargetCall,
	capturedRepeatedSecondTarget,
	authenticatedOrigin
).definition_location == "statement-factory-captured-repeated-second-current")

local capturedSnapshotFutureFactory = declaration(
	"statementFactoryCapturedSnapshotFuture",
	"statement-factory-captured-snapshot-future"
)
local _, capturedSnapshotFutureCall = capturedSnapshotInvocation(
	capturedSnapshotFutureFactory,
	"statement-factory-captured-snapshot-future",
	1,
	1,
	false
)
expectExpressionFailure(document({
	localFunctionStatement(capturedSnapshotFutureFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-snapshot-future-value"),
		"statement-factory-captured-snapshot-future-function",
		false
	), "statement-factory-captured-snapshot-future-declaration"),
	assignmentValue(
		capturedSnapshotFutureFactory,
		"statement-factory-captured-snapshot-future-write",
		differentTarget("statement-factory-captured-snapshot-future-write-value")
	),
	callStatement(capturedSnapshotFutureCall, "statement-factory-captured-snapshot-future-statement"),
}), capturedSnapshotFutureCall)

local capturedSnapshotBeforeFactory = declaration(
	"statementFactoryCapturedSnapshotBefore",
	"statement-factory-captured-snapshot-before"
)
local capturedSnapshotBeforeInvoker = declaration(
	"statementFactoryCapturedSnapshotBeforeInvoker",
	"statement-factory-captured-snapshot-before-invoker"
)
local capturedSnapshotBeforeFunction, _, _ = capturedSnapshotInvocation(
	capturedSnapshotBeforeFactory,
	"statement-factory-captured-snapshot-before-body",
	1,
	1,
	false
)
local capturedSnapshotBeforeCall = localInvocation(
	capturedSnapshotBeforeInvoker,
	"statement-factory-captured-snapshot-before",
	false
)
expectExpressionFailure(document({
	localStatement(capturedSnapshotBeforeFactory, "statement-factory-captured-snapshot-before-local"),
	localStatement(
		capturedSnapshotBeforeInvoker,
		"statement-factory-captured-snapshot-before-invoker-declaration",
		capturedSnapshotBeforeFunction
	),
	functionStatement(capturedSnapshotBeforeFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-snapshot-before-value"),
		"statement-factory-captured-snapshot-before-function",
		false
	), "statement-factory-captured-snapshot-before-definition"),
	callStatement(capturedSnapshotBeforeCall, "statement-factory-captured-snapshot-before-statement"),
}), capturedSnapshotBeforeCall)

local capturedSnapshotBranchFactory = declaration(
	"statementFactoryCapturedSnapshotBranch",
	"statement-factory-captured-snapshot-branch"
)
local _, capturedSnapshotBranchCall = capturedSnapshotInvocation(
	capturedSnapshotBranchFactory,
	"statement-factory-captured-snapshot-branch",
	1,
	0,
	false
)
expectExpressionFailure(document({
	localStatement(capturedSnapshotBranchFactory, "statement-factory-captured-snapshot-branch-local"),
	Support.branchStatement("statement-factory-captured-snapshot-branch", {
		functionStatement(capturedSnapshotBranchFactory, returningFunction(
			globalExpression("authenticated_target", "statement-factory-captured-snapshot-branch-value"),
			"statement-factory-captured-snapshot-branch-function",
			false
		), "statement-factory-captured-snapshot-branch-definition"),
		callStatement(capturedSnapshotBranchCall, "statement-factory-captured-snapshot-branch-statement"),
	}, nil),
}), capturedSnapshotBranchCall)

local capturedFutureFactory = declaration("statementFactoryCapturedFuture", "statement-factory-captured-future")
local capturedFutureOwnerDeclaration, capturedFutureOwnerCall, _, _, capturedFutureCall = capturedOwner(
	capturedFutureFactory,
	"statement-factory-captured-future",
	false,
	false
)
expectExpressionFailure(document({
	localFunctionStatement(capturedFutureFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-future-value"),
		"statement-factory-captured-future-function",
		false
	), "statement-factory-captured-future-declaration"),
	capturedFutureOwnerDeclaration,
	assignmentValue(
		capturedFutureFactory,
		"statement-factory-captured-future-write",
		differentTarget("statement-factory-captured-future-write-value")
	),
	capturedFutureOwnerCall,
}), capturedFutureCall)

local capturedLaterFactory = declaration("statementFactoryCapturedLater", "statement-factory-captured-later")
local capturedLaterOwnerDeclaration, capturedLaterOwnerCall, _, _, capturedLaterCall = capturedOwner(
	capturedLaterFactory,
	"statement-factory-captured-later",
	false,
	false
)
expectExpressionFailure(document({
	localFunctionStatement(capturedLaterFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-later-value"),
		"statement-factory-captured-later-function",
		false
	), "statement-factory-captured-later-declaration"),
	capturedLaterOwnerDeclaration,
	capturedLaterOwnerCall,
	functionStatement(capturedLaterFactory, returningFunction(
		differentTarget("statement-factory-captured-later-write-value"),
		"statement-factory-captured-later-write-function",
		false
	), "statement-factory-captured-later-write"),
}), capturedLaterCall)

local capturedMultipleFactory = declaration(
	"statementFactoryCapturedMultiple",
	"statement-factory-captured-multiple"
)
local capturedMultipleOwnerDeclaration, capturedMultipleOwnerCall, _, _, capturedMultipleCall = capturedOwner(
	capturedMultipleFactory,
	"statement-factory-captured-multiple",
	false,
	false
)
expectExpressionFailure(document({
	localFunctionStatement(capturedMultipleFactory, returningFunction(
		differentTarget("statement-factory-captured-multiple-old-value"),
		"statement-factory-captured-multiple-old-function",
		false
	), "statement-factory-captured-multiple-declaration"),
	functionStatement(capturedMultipleFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-multiple-value"),
		"statement-factory-captured-multiple-function",
		false
	), "statement-factory-captured-multiple-definition"),
	capturedMultipleOwnerDeclaration,
	capturedMultipleOwnerCall,
}), capturedMultipleCall)

local capturedBeforeFactory = declaration("statementFactoryCapturedBefore", "statement-factory-captured-before")
local capturedBeforeOwnerDeclaration, capturedBeforeOwnerCall, _, _, capturedBeforeCall = capturedOwner(
	capturedBeforeFactory,
	"statement-factory-captured-before",
	false,
	false
)
expectExpressionFailure(document({
	localStatement(capturedBeforeFactory, "statement-factory-captured-before-local"),
	capturedBeforeOwnerDeclaration,
	functionStatement(capturedBeforeFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-before-value"),
		"statement-factory-captured-before-function",
		false
	), "statement-factory-captured-before-definition"),
	capturedBeforeOwnerCall,
}), capturedBeforeCall)

local capturedBranchFactory = declaration("statementFactoryCapturedBranch", "statement-factory-captured-branch")
local capturedBranchOwnerDeclaration, capturedBranchOwnerCall, _, _, capturedBranchCall = capturedOwner(
	capturedBranchFactory,
	"statement-factory-captured-branch",
	false,
	false
)
expectExpressionFailure(document({
	localStatement(capturedBranchFactory, "statement-factory-captured-branch-local"),
	Support.branchStatement("statement-factory-captured-branch", {
		functionStatement(capturedBranchFactory, returningFunction(
			globalExpression("authenticated_target", "statement-factory-captured-branch-value"),
			"statement-factory-captured-branch-function",
			false
		), "statement-factory-captured-branch-definition"),
		capturedBranchOwnerDeclaration,
		capturedBranchOwnerCall,
	}, nil),
}), capturedBranchCall)

local capturedInitializedFactory = declaration(
	"statementFactoryCapturedInitialized",
	"statement-factory-captured-initialized"
)
local capturedInitializedOwnerDeclaration, capturedInitializedOwnerCall, _, _, capturedInitializedCall = capturedOwner(
	capturedInitializedFactory,
	"statement-factory-captured-initialized",
	false,
	false
)
expectExpressionFailure(document({
	localStatement(
		capturedInitializedFactory,
		"statement-factory-captured-initialized-local",
		differentTarget("statement-factory-captured-initialized-value")
	),
	functionStatement(capturedInitializedFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-captured-initialized-return"),
		"statement-factory-captured-initialized-function",
		false
	), "statement-factory-captured-initialized-definition"),
	capturedInitializedOwnerDeclaration,
	capturedInitializedOwnerCall,
}), capturedInitializedCall)

local nonfunctionFactory = declaration("statementFactoryNonfunction", "statement-factory-nonfunction")
local nonfunctionCall = localInvocation(nonfunctionFactory, "statement-factory-nonfunction-call", false)
expectExpressionFailure(document({
	localFunctionStatement(nonfunctionFactory, returningFunction(
		globalExpression("authenticated_target", "statement-factory-nonfunction-value"),
		"statement-factory-nonfunction-function",
		false
	), "statement-factory-nonfunction-declaration"),
	assignmentValue(
		nonfunctionFactory,
		"statement-factory-nonfunction-replacement",
		differentTarget("statement-factory-nonfunction-replacement-value")
	),
	callStatement(nonfunctionCall, "statement-factory-nonfunction-call-statement"),
}), nonfunctionCall)

local recursiveFactory = declaration("statementFactoryRecursive", "statement-factory-recursive")
local recursiveInnerCall = localInvocation(recursiveFactory, "statement-factory-recursive-inner", false)
local recursiveOuterCall = localInvocation(recursiveFactory, "statement-factory-recursive-outer", false)
expectExpressionFailure(document({
	localFunctionStatement(recursiveFactory, returningFunction(
		recursiveInnerCall,
		"statement-factory-recursive-function",
		false
	), "statement-factory-recursive-declaration"),
	callStatement(recursiveOuterCall, "statement-factory-recursive-outer-statement"),
}), recursiveOuterCall)
