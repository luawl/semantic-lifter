--!strict

local TemporalTargetIdentity = require("./temporal_target_identity")
local TemporalCalleeResolver = require("./temporal_callee_resolver")
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
local wrappedExpression = InvocationSupport.wrappedExpression

local authenticatedOrigin: Record = { kind = "environment", name = "authenticated_target" }
local wrappers: { string } = { "AstExprGroup", "AstExprTypeAssertion", "AstExprInstantiate" }

local function returningFunction(value: Record, prefix: string, wrapped: boolean): Record
	local returned = if wrapped then wrappedExpression(value, prefix .. "-returned") else value
	local functionValue, _ = invocationFromBody({
		{ type = "AstStatReturn", location = prefix .. "-return", list = { returned } },
	}, prefix, if wrapped then wrappers else nil, nil)
	return if wrapped then wrappedExpression(functionValue, prefix .. "-function-value") else functionValue
end

local function factoryCall(factory: Record, prefix: string, wrapped: boolean): Record
	local callee = localExpression(factory, prefix .. "-callee-read")
	if wrapped then
		callee = wrappedExpression(callee, prefix .. "-callee")
	end
	local call: Record = {
		type = "AstExprCall",
		location = prefix .. "-call",
		func = callee,
		args = {},
		self = false,
	}
	return if wrapped then wrappedExpression(call, prefix .. "-call-value") else call
end

local function appendTarget(body: { Record }, factory: Record, prefix: string, wrapped: boolean): (Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local targetCall = callExpression(target, prefix .. "-target-read")
	table.insert(body, localStatement(target, prefix .. "-target-declaration"))
	table.insert(body, assignmentValue(
		target,
		prefix .. "-current",
		factoryCall(factory, prefix .. "-factory-invocation", wrapped)
	))
	table.insert(body, callStatement(targetCall, prefix .. "-target-call-statement"))
	return targetCall, target
end

local function expectProof(prefix: string, body: { Record }, factory: Record, wrapped: boolean)
	local targetCall, target = appendTarget(body, factory, prefix, wrapped)
	local proof = verifyOrigin(document(body), targetCall, target, authenticatedOrigin)
	assert(proof.definition_location == prefix .. "-current", `{prefix} lost its aliased factory call result`)
end

local function expectExpressionFailure(fixture: Record, expression: Record)
	local analysis = TemporalTargetIdentity.analyze(fixture)
	assert(not TemporalTargetIdentity.matchesExpression(analysis, expression, authenticatedOrigin))
end

local resolverCycleLeft = declaration("localFactoryResolverCycleLeft", "local-factory-resolver-cycle-left")
local resolverCycleRight = declaration("localFactoryResolverCycleRight", "local-factory-resolver-cycle-right")
local resolverCycleDefinitions: { [string]: Record } = {
	[resolverCycleLeft.location] = localExpression(resolverCycleRight, "local-factory-resolver-cycle-right-read"),
	[resolverCycleRight.location] = localExpression(resolverCycleLeft, "local-factory-resolver-cycle-left-read"),
}
local resolverCycleStart = localExpression(resolverCycleLeft, "local-factory-resolver-cycle-start")
assert(TemporalCalleeResolver.resolve(
	resolverCycleStart,
	resolverCycleStart,
	function(_: Record, expression: Record): Record?
		local localNode = expression["local"]
		if type(localNode) ~= "table" or type((localNode :: Record).location) ~= "string" then
			return nil
		end
		return resolverCycleDefinitions[(localNode :: Record).location]
	end
) == nil, "local-factory resolver accepted an alias cycle")

local resolverWrapperCycle: Record = {
	type = "AstExprGroup",
	location = "local-factory-resolver-wrapper-cycle",
}
resolverWrapperCycle.expr = resolverWrapperCycle
assert(TemporalCalleeResolver.resolve(
	resolverWrapperCycle,
	resolverWrapperCycle,
	function(_: Record, _: Record): Record?
		return nil
	end
) == nil, "local-factory resolver accepted a transparent-wrapper cycle")

local directFactory = declaration("localFactoryAliasDirectFactory", "local-factory-alias-direct-factory")
local directAlias = declaration("localFactoryAliasDirectAlias", "local-factory-alias-direct-alias")
expectProof("local-factory-alias-direct", {
	localStatement(directFactory, "local-factory-alias-direct-factory-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-alias-direct-value"),
		"local-factory-alias-direct-function",
		false
	)),
	localStatement(
		directAlias,
		"local-factory-alias-direct-alias-declaration",
		localExpression(directFactory, "local-factory-alias-direct-alias-value")
	),
}, directAlias, false)

local wrappedFactory = declaration("localFactoryAliasWrappedFactory", "local-factory-alias-wrapped-factory")
local wrappedAlias = declaration("localFactoryAliasWrappedAlias", "local-factory-alias-wrapped-alias")
expectProof("local-factory-alias-wrapped", {
	localStatement(wrappedFactory, "local-factory-alias-wrapped-factory-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-alias-wrapped-value"),
		"local-factory-alias-wrapped-function",
		true
	)),
	localStatement(wrappedAlias, "local-factory-alias-wrapped-alias-declaration", wrappedExpression(
		localExpression(wrappedFactory, "local-factory-alias-wrapped-alias-read"),
		"local-factory-alias-wrapped-alias-value"
	)),
}, wrappedAlias, true)

local parameter = declaration("localFactoryAliasParameter", "local-factory-alias-parameter")
local parameterFunction = returningFunction(
	localExpression(parameter, "local-factory-alias-parameter-read"),
	"local-factory-alias-parameter-function",
	false
)
parameterFunction.args = { parameter }
local parameterFactory = declaration("localFactoryAliasParameterFactory", "local-factory-alias-parameter-factory")
local parameterAlias = declaration("localFactoryAliasParameterAlias", "local-factory-alias-parameter-alias")
local parameterTarget = declaration("localFactoryAliasParameterTarget", "local-factory-alias-parameter-target")
local parameterTargetCall = callExpression(parameterTarget, "local-factory-alias-parameter-target-read")
local parameterProof = verifyOrigin(document({
	localStatement(
		parameterFactory,
		"local-factory-alias-parameter-factory-declaration",
		parameterFunction
	),
	localStatement(
		parameterAlias,
		"local-factory-alias-parameter-alias-declaration",
		localExpression(parameterFactory, "local-factory-alias-parameter-alias-value")
	),
	localStatement(parameterTarget, "local-factory-alias-parameter-target-declaration"),
	assignmentValue(parameterTarget, "local-factory-alias-parameter-current", {
		type = "AstExprCall",
		location = "local-factory-alias-parameter-invocation",
		func = localExpression(parameterAlias, "local-factory-alias-parameter-callee"),
		args = { globalExpression("authenticated_target", "local-factory-alias-parameter-argument") },
		self = false,
	}),
	callStatement(parameterTargetCall, "local-factory-alias-parameter-target-call-statement"),
}), parameterTargetCall, parameterTarget, authenticatedOrigin)
assert(parameterProof.definition_location == "local-factory-alias-parameter-current")

local returnedAlias = declaration("localFactoryAliasReturnedLocal", "local-factory-alias-returned-local")
local localReturnFunction, _ = invocationFromBody({
	localStatement(
		returnedAlias,
		"local-factory-alias-local-return-declaration",
		globalExpression("authenticated_target", "local-factory-alias-local-return-value")
	),
	{
		type = "AstStatReturn",
		location = "local-factory-alias-local-return-statement",
		list = { localExpression(returnedAlias, "local-factory-alias-local-return-read") },
	},
}, "local-factory-alias-local-return-function", nil, nil)
local localReturnFactory = declaration("localFactoryAliasLocalReturnFactory", "local-factory-alias-local-return-factory")
local localReturnCallee = declaration("localFactoryAliasLocalReturnCallee", "local-factory-alias-local-return-callee")
expectProof("local-factory-alias-local-return", {
	localStatement(
		localReturnFactory,
		"local-factory-alias-local-return-factory-declaration",
		localReturnFunction
	),
	localStatement(
		localReturnCallee,
		"local-factory-alias-local-return-callee-declaration",
		localExpression(localReturnFactory, "local-factory-alias-local-return-callee-value")
	),
}, localReturnCallee, false)

local nestedInnerFactory = declaration("localFactoryAliasNestedInnerFactory", "local-factory-alias-nested-inner-factory")
local nestedInnerAlias = declaration("localFactoryAliasNestedInnerAlias", "local-factory-alias-nested-inner-alias")
local nestedOuterFactory = declaration("localFactoryAliasNestedOuterFactory", "local-factory-alias-nested-outer-factory")
local nestedOuterAlias = declaration("localFactoryAliasNestedOuterAlias", "local-factory-alias-nested-outer-alias")
expectProof("local-factory-alias-nested", {
	localStatement(nestedInnerFactory, "local-factory-alias-nested-inner-factory-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-alias-nested-value"),
		"local-factory-alias-nested-inner-function",
		false
	)),
	localStatement(
		nestedInnerAlias,
		"local-factory-alias-nested-inner-alias-declaration",
		localExpression(nestedInnerFactory, "local-factory-alias-nested-inner-alias-value")
	),
	localStatement(nestedOuterFactory, "local-factory-alias-nested-outer-factory-declaration", returningFunction(
		factoryCall(nestedInnerAlias, "local-factory-alias-nested-inner-invocation", true),
		"local-factory-alias-nested-outer-function",
		true
	)),
	localStatement(
		nestedOuterAlias,
		"local-factory-alias-nested-outer-alias-declaration",
		localExpression(nestedOuterFactory, "local-factory-alias-nested-outer-alias-value")
	),
}, nestedOuterAlias, true)

local ordinalFactory = declaration("localFactoryAliasOrdinalFactory", "local-factory-alias-ordinal-factory")
local ordinalOther = declaration("localFactoryAliasOrdinalOther", "local-factory-alias-ordinal-other")
local ordinalAlias = declaration("localFactoryAliasOrdinalAlias", "local-factory-alias-ordinal-alias")
expectProof("local-factory-alias-ordinal", {
	{
		type = "AstStatLocal",
		location = "local-factory-alias-ordinal-factory-declaration",
		vars = { ordinalOther, ordinalFactory },
		values = {
			differentTarget("local-factory-alias-ordinal-other-value"),
			returningFunction(
				globalExpression("authenticated_target", "local-factory-alias-ordinal-value"),
				"local-factory-alias-ordinal-function",
				false
			),
		},
	},
	localStatement(
		ordinalAlias,
		"local-factory-alias-ordinal-alias-declaration",
		localExpression(ordinalFactory, "local-factory-alias-ordinal-alias-value")
	),
}, ordinalAlias, false)

local fanoutFactory = declaration("localFactoryAliasFanoutFactory", "local-factory-alias-fanout-factory")
local fanoutLeft = declaration("localFactoryAliasFanoutLeft", "local-factory-alias-fanout-left")
local fanoutRight = declaration("localFactoryAliasFanoutRight", "local-factory-alias-fanout-right")
expectProof("local-factory-alias-fanout", {
	localStatement(fanoutFactory, "local-factory-alias-fanout-factory-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-alias-fanout-value"),
		"local-factory-alias-fanout-function",
		false
	)),
	localStatement(
		fanoutLeft,
		"local-factory-alias-fanout-left-declaration",
		localExpression(fanoutFactory, "local-factory-alias-fanout-left-value")
	),
	localStatement(
		fanoutRight,
		"local-factory-alias-fanout-right-declaration",
		localExpression(fanoutFactory, "local-factory-alias-fanout-right-value")
	),
	callStatement(factoryCall(fanoutLeft, "local-factory-alias-fanout-left-call", false), "local-factory-alias-fanout-left-statement"),
}, fanoutRight, false)

local snapshotFactory = declaration("localFactoryAliasSnapshotFactory", "local-factory-alias-snapshot-factory")
local snapshotAlias = declaration("localFactoryAliasSnapshotAlias", "local-factory-alias-snapshot-alias")
expectProof("local-factory-alias-snapshot", {
	localStatement(snapshotFactory, "local-factory-alias-snapshot-factory-declaration"),
	assignmentValue(snapshotFactory, "local-factory-alias-snapshot-factory-write", returningFunction(
		globalExpression("authenticated_target", "local-factory-alias-snapshot-value"),
		"local-factory-alias-snapshot-function",
		false
	)),
	localStatement(
		snapshotAlias,
		"local-factory-alias-snapshot-alias-declaration",
		localExpression(snapshotFactory, "local-factory-alias-snapshot-alias-value")
	),
	assignmentValue(snapshotFactory, "local-factory-alias-snapshot-replacement", returningFunction(
		differentTarget("local-factory-alias-snapshot-replacement-value"),
		"local-factory-alias-snapshot-replacement-function",
		false
	)),
}, snapshotAlias, false)

local assignedSource = declaration("localFactoryAliasAssignedSource", "local-factory-alias-assigned-source")
local assignedAlias = declaration("localFactoryAliasAssignedAlias", "local-factory-alias-assigned-alias")
expectProof("local-factory-alias-assigned", {
	localStatement(assignedSource, "local-factory-alias-assigned-source-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-alias-assigned-value"),
		"local-factory-alias-assigned-function",
		false
	)),
	localStatement(assignedAlias, "local-factory-alias-assigned-alias-declaration"),
	assignmentValue(
		assignedAlias,
		"local-factory-alias-assigned-alias-write",
		localExpression(assignedSource, "local-factory-alias-assigned-alias-value")
	),
}, assignedAlias, false)

local capturedFactory = declaration("localFactoryAliasCapturedFactory", "local-factory-alias-captured-factory")
local capturedAlias = declaration("localFactoryAliasCapturedAlias", "local-factory-alias-captured-alias")
local capturedTarget = declaration("localFactoryAliasCapturedTarget", "local-factory-alias-captured-target")
local capturedTargetCall = callExpression(capturedTarget, "local-factory-alias-captured-target-read")
local _, capturedOwnerCall = invocationFromBody({
	localStatement(capturedTarget, "local-factory-alias-captured-target-declaration"),
	assignmentValue(
		capturedTarget,
		"local-factory-alias-captured-current",
		factoryCall(capturedAlias, "local-factory-alias-captured-invocation", false)
	),
	callStatement(capturedTargetCall, "local-factory-alias-captured-target-call-statement"),
}, "local-factory-alias-captured-owner", nil, nil)
local capturedProof = verifyOrigin(document({
	localStatement(capturedFactory, "local-factory-alias-captured-factory-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-alias-captured-value"),
		"local-factory-alias-captured-function",
		false
	)),
	localStatement(
		capturedAlias,
		"local-factory-alias-captured-alias-declaration",
		localExpression(capturedFactory, "local-factory-alias-captured-alias-value")
	),
	callStatement(capturedOwnerCall, "local-factory-alias-captured-owner-statement"),
}), capturedTargetCall, capturedTarget, authenticatedOrigin)
assert(capturedProof.definition_location == "local-factory-alias-captured-current")

local function aliasDepthDocument(identityCount: number, prefix: string): (Record, Record, Record)
	assert(identityCount >= 1)
	local body: { Record } = {}
	local current = declaration(prefix .. "Factory1", prefix .. "-factory-1")
	table.insert(body, localStatement(current, prefix .. "-declaration-1", returningFunction(
		globalExpression("authenticated_target", prefix .. "-value"),
		prefix .. "-function",
		false
	)))
	for index = 2, identityCount do
		local alias = declaration(`{prefix}Factory{index}`, `{prefix}-factory-{index}`)
		table.insert(body, localStatement(
			alias,
			`{prefix}-declaration-{index}`,
			localExpression(current, `{prefix}-value-{index}`)
		))
		current = alias
	end
	local targetCall, target = appendTarget(body, current, prefix, false)
	return document(body), targetCall, target
end

local depth64Fixture, depth64Call, depth64Target = aliasDepthDocument(64, "local-factory-alias-depth-64")
local depth64Proof = verifyOrigin(depth64Fixture, depth64Call, depth64Target, authenticatedOrigin)
assert(depth64Proof.definition_location == "local-factory-alias-depth-64-current")

local depth65Fixture, depth65Call, depth65Target = aliasDepthDocument(65, "local-factory-alias-depth-65")
expectFailure(function()
	verifyOrigin(depth65Fixture, depth65Call, depth65Target, authenticatedOrigin)
end, "temporal target definition " .. depth65Target.location)

local nonfunctionSource = declaration("localFactoryAliasNonfunctionSource", "local-factory-alias-nonfunction-source")
local nonfunctionAlias = declaration("localFactoryAliasNonfunctionAlias", "local-factory-alias-nonfunction-alias")
local nonfunctionCall = factoryCall(nonfunctionAlias, "local-factory-alias-nonfunction", false)
expectExpressionFailure(document({
	localStatement(
		nonfunctionSource,
		"local-factory-alias-nonfunction-source-declaration",
		globalExpression("authenticated_target", "local-factory-alias-nonfunction-source-value")
	),
	localStatement(
		nonfunctionAlias,
		"local-factory-alias-nonfunction-alias-declaration",
		localExpression(nonfunctionSource, "local-factory-alias-nonfunction-alias-value")
	),
	callStatement(nonfunctionCall, "local-factory-alias-nonfunction-call-statement"),
}), nonfunctionCall)

local indexedAlias = declaration("localFactoryAliasIndexed", "local-factory-alias-indexed")
local indexedCall = factoryCall(indexedAlias, "local-factory-alias-indexed", false)
expectExpressionFailure(document({
	localStatement(indexedAlias, "local-factory-alias-indexed-declaration", {
		type = "AstExprIndexName",
		location = "local-factory-alias-indexed-value",
		expr = globalExpression("registry", "local-factory-alias-indexed-root"),
		index = "factory",
	}),
	callStatement(indexedCall, "local-factory-alias-indexed-call-statement"),
}), indexedCall)

local mutableCapturedSource = declaration(
	"localFactoryAliasMutableCapturedSource",
	"local-factory-alias-mutable-captured-source"
)
local mutableCapturedAlias = declaration(
	"localFactoryAliasMutableCapturedAlias",
	"local-factory-alias-mutable-captured-alias"
)
local mutableCapturedCall = factoryCall(
	mutableCapturedAlias,
	"local-factory-alias-mutable-captured-invocation",
	false
)
local _, mutableCapturedOwnerCall = invocationFromBody({
	callStatement(mutableCapturedCall, "local-factory-alias-mutable-captured-inner-statement"),
}, "local-factory-alias-mutable-captured-owner", nil, nil)
expectExpressionFailure(document({
	localStatement(mutableCapturedSource, "local-factory-alias-mutable-captured-source-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-alias-mutable-captured-value"),
		"local-factory-alias-mutable-captured-function",
		false
	)),
	localStatement(mutableCapturedAlias, "local-factory-alias-mutable-captured-alias-declaration"),
	assignmentValue(
		mutableCapturedAlias,
		"local-factory-alias-mutable-captured-alias-write",
		localExpression(mutableCapturedSource, "local-factory-alias-mutable-captured-alias-value")
	),
	callStatement(mutableCapturedOwnerCall, "local-factory-alias-mutable-captured-owner-statement"),
}), mutableCapturedCall)

local sameStatementSource = declaration("localFactoryAliasSameSource", "local-factory-alias-same-source")
local sameStatementAlias = declaration("localFactoryAliasSameAlias", "local-factory-alias-same-alias")
local sameStatementTarget = declaration("localFactoryAliasSameTarget", "local-factory-alias-same-target")
local sameStatementTargetCall = callExpression(sameStatementTarget, "local-factory-alias-same-target-read")
expectFailure(function()
	verifyOrigin(document({
		localStatement(sameStatementSource, "local-factory-alias-same-source-declaration", returningFunction(
			globalExpression("authenticated_target", "local-factory-alias-same-value"),
			"local-factory-alias-same-function",
			false
		)),
		localStatement(sameStatementAlias, "local-factory-alias-same-alias-declaration"),
		localStatement(sameStatementTarget, "local-factory-alias-same-target-declaration"),
		{
			type = "AstStatAssign",
			location = "local-factory-alias-same-write",
			vars = {
				localExpression(sameStatementAlias, "local-factory-alias-same-alias-write"),
				localExpression(sameStatementTarget, "local-factory-alias-same-target-write"),
			},
			values = {
				localExpression(sameStatementSource, "local-factory-alias-same-alias-value"),
				factoryCall(sameStatementAlias, "local-factory-alias-same-invocation", false),
			},
		},
		callStatement(sameStatementTargetCall, "local-factory-alias-same-target-call-statement"),
	}), sameStatementTargetCall, sameStatementTarget, authenticatedOrigin)
end, "temporal target definition " .. sameStatementTarget.location)
