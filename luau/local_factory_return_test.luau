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
local wrappedExpression = InvocationSupport.wrappedExpression

local authenticatedOrigin: Record = { kind = "environment", name = "authenticated_target" }
local wrappers: { string } = { "AstExprGroup", "AstExprTypeAssertion", "AstExprInstantiate" }

local function returnStatement(value: Record, prefix: string): Record
	return { type = "AstStatReturn", location = prefix .. "-return", list = { value } }
end

local function returningFunction(value: Record, prefix: string, wrapped: boolean): Record
	local returned = if wrapped then wrappedExpression(value, prefix .. "-returned") else value
	local functionValue, _ = invocationFromBody(
		{ returnStatement(returned, prefix) },
		prefix,
		if wrapped then wrappers else nil,
		nil
	)
	return if wrapped then wrappedExpression(functionValue, prefix .. "-function-value") else functionValue
end

local function factoryCall(factory: Record, arguments: { Record }, prefix: string, wrapped: boolean): Record
	local callee = localExpression(factory, prefix .. "-callee-read")
	if wrapped then
		callee = wrappedExpression(callee, prefix .. "-callee")
	end
	local call: Record = {
		type = "AstExprCall",
		location = prefix .. "-call",
		func = callee,
		args = arguments,
		self = false,
	}
	return if wrapped then wrappedExpression(call, prefix .. "-call-value") else call
end

local function targetBody(prefix: string, factory: Record, value: Record, prelude: { Record }?): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local targetCall = callExpression(target, prefix .. "-target-read")
	local body: { Record } = {}
	if prelude ~= nil then
		for _, statement in prelude do
			table.insert(body, statement)
		end
	end
	table.insert(body, localStatement(factory, prefix .. "-factory-declaration", value))
	table.insert(body, localStatement(target, prefix .. "-target-declaration"))
	table.insert(body, assignmentValue(
		target,
		prefix .. "-current",
		factoryCall(factory, {}, prefix .. "-factory-invocation", false)
	))
	table.insert(body, callStatement(targetCall, prefix .. "-target-call-statement"))
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), targetCall, target
end

local function expectProof(prefix: string, factoryValue: Record)
	local factory = declaration(prefix .. "Factory", prefix .. "-factory")
	local fixture, targetCall, target = targetBody(prefix, factory, factoryValue, nil)
	local proof = verifyOrigin(fixture, targetCall, target, authenticatedOrigin)
	assert(proof.definition_location == prefix .. "-current", `{prefix} lost the existing factory call result`)
end

local function expectTargetFailure(prefix: string, body: { Record }, targetCall: Record, target: Record)
	expectFailure(function()
		verifyOrigin(document(body), targetCall, target, authenticatedOrigin)
	end, "temporal target definition " .. target.location)
end

local function expectExpressionFailure(fixture: Record, expression: Record)
	local analysis = TemporalTargetIdentity.analyze(fixture)
	assert(not TemporalTargetIdentity.matchesExpression(analysis, expression, authenticatedOrigin))
end

expectProof(
	"local-factory-environment",
	returningFunction(
		globalExpression("authenticated_target", "local-factory-environment-value"),
		"local-factory-environment-function",
		false
	)
)

expectProof(
	"local-factory-wrapped",
	returningFunction(
		globalExpression("authenticated_target", "local-factory-wrapped-value"),
		"local-factory-wrapped-function",
		true
	)
)

local ordinalFactory = declaration("localFactoryOrdinalFactory", "local-factory-ordinal-factory")
local ordinalOther1 = declaration("localFactoryOrdinalOther1", "local-factory-ordinal-other-1")
local ordinalOther2 = declaration("localFactoryOrdinalOther2", "local-factory-ordinal-other-2")
local ordinalTarget = declaration("localFactoryOrdinalTarget", "local-factory-ordinal-target")
local ordinalTargetCall = callExpression(ordinalTarget, "local-factory-ordinal-target-read")
local ordinalProof = verifyOrigin(document({
	{
		type = "AstStatLocal",
		location = "local-factory-ordinal-declaration",
		vars = { ordinalOther1, ordinalFactory, ordinalOther2 },
		values = {
			differentTarget("local-factory-ordinal-other-value"),
			returningFunction(
				globalExpression("authenticated_target", "local-factory-ordinal-value"),
				"local-factory-ordinal-function",
				false
			),
		},
	},
	localStatement(ordinalTarget, "local-factory-ordinal-target-declaration"),
	assignmentValue(
		ordinalTarget,
		"local-factory-ordinal-current",
		factoryCall(ordinalFactory, {}, "local-factory-ordinal-invocation", true)
	),
	callStatement(ordinalTargetCall, "local-factory-ordinal-target-call-statement"),
}), ordinalTargetCall, ordinalTarget, authenticatedOrigin)
assert(ordinalProof.definition_location == "local-factory-ordinal-current")

local repeatedCallFactory = declaration("localFactoryRepeatedCallFactory", "local-factory-repeated-call-factory")
local repeatedCallFunction = returningFunction(
	globalExpression("authenticated_target", "local-factory-repeated-call-value"),
	"local-factory-repeated-call-function",
	false
)
local repeatedFixture, repeatedTargetCall, repeatedTarget = targetBody(
	"local-factory-repeated-call",
	repeatedCallFactory,
	repeatedCallFunction,
	{ callStatement(
		factoryCall(repeatedCallFactory, {}, "local-factory-repeated-call-discarded", false),
		"local-factory-repeated-call-discarded-statement"
	) }
)
local repeatedProof = verifyOrigin(repeatedFixture, repeatedTargetCall, repeatedTarget, authenticatedOrigin)
assert(repeatedProof.definition_location == "local-factory-repeated-call-current")

local parameter = declaration("localFactoryParameter", "local-factory-parameter")
local parameterFunction = returningFunction(
	localExpression(parameter, "local-factory-parameter-read"),
	"local-factory-parameter-function",
	false
)
local parameterFunctionValue = parameterFunction
while parameterFunctionValue.type == "AstExprGroup"
	or parameterFunctionValue.type == "AstExprTypeAssertion"
	or parameterFunctionValue.type == "AstExprInstantiate"
do
	parameterFunctionValue = parameterFunctionValue.expr
end
parameterFunctionValue.args = { parameter }
local parameterFactory = declaration("localFactoryParameterFactory", "local-factory-parameter-factory")
local parameterTarget = declaration("localFactoryParameterTarget", "local-factory-parameter-target")
local parameterTargetCall = callExpression(parameterTarget, "local-factory-parameter-target-read")
local parameterProof = verifyOrigin(document({
	localStatement(parameterFactory, "local-factory-parameter-factory-declaration", parameterFunction),
	localStatement(parameterTarget, "local-factory-parameter-target-declaration"),
	assignmentValue(parameterTarget, "local-factory-parameter-current", factoryCall(parameterFactory, {
		globalExpression("authenticated_target", "local-factory-parameter-argument"),
	}, "local-factory-parameter-invocation", false)),
	callStatement(parameterTargetCall, "local-factory-parameter-target-call-statement"),
}), parameterTargetCall, parameterTarget, authenticatedOrigin)
assert(parameterProof.definition_location == "local-factory-parameter-current")

local alias = declaration("localFactoryAliasReturn", "local-factory-alias-return")
local aliasFunction, _ = invocationFromBody({
	localStatement(
		alias,
		"local-factory-alias-return-declaration",
		globalExpression("authenticated_target", "local-factory-alias-return-value")
	),
	returnStatement(localExpression(alias, "local-factory-alias-return-read"), "local-factory-alias-return"),
}, "local-factory-alias-return-function", nil, nil)
expectProof("local-factory-alias-return", aliasFunction)

local capturedFactory = declaration("localFactoryCaptured", "local-factory-captured-factory")
local capturedTarget = declaration("localFactoryCapturedTarget", "local-factory-captured-target")
local capturedTargetCall = callExpression(capturedTarget, "local-factory-captured-target-read")
local _, capturedInvocation = invocationFromBody({
	localStatement(capturedTarget, "local-factory-captured-target-declaration"),
	assignmentValue(
		capturedTarget,
		"local-factory-captured-current",
		factoryCall(capturedFactory, {}, "local-factory-captured-invocation", false)
	),
	callStatement(capturedTargetCall, "local-factory-captured-target-call-statement"),
	assignmentValue(
		capturedTarget,
		"local-factory-captured-future-write",
		differentTarget("local-factory-captured-future-value")
	),
}, "local-factory-captured-owner", nil, nil)
local capturedProof = verifyOrigin(document({
	localStatement(capturedFactory, "local-factory-captured-factory-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-captured-value"),
		"local-factory-captured-function",
		false
	)),
	callStatement(capturedInvocation, "local-factory-captured-owner-call"),
}), capturedTargetCall, capturedTarget, authenticatedOrigin)
assert(capturedProof.definition_location == "local-factory-captured-current")

local function nestedFactoryDocument(depth: number, prefix: string): (Record, Record, Record)
	assert(depth >= 1)
	local body: { Record } = {}
	local prior: Record? = nil
	for index = 1, depth do
		local factory = declaration(`{prefix}Factory{index}`, `{prefix}-factory-{index}`)
		local returned = if prior == nil
			then globalExpression("authenticated_target", `{prefix}-value`)
			else factoryCall(prior :: Record, {}, `{prefix}-nested-call-{index}`, index % 2 == 0)
		table.insert(body, localStatement(factory, `{prefix}-factory-declaration-{index}`, returningFunction(
			returned,
			`{prefix}-function-{index}`,
			index % 2 == 0
		)))
		prior = factory
	end
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local targetCall = callExpression(target, prefix .. "-target-read")
	table.insert(body, localStatement(target, prefix .. "-target-declaration"))
	table.insert(body, assignmentValue(
		target,
		prefix .. "-current",
		factoryCall(prior :: Record, {}, prefix .. "-outer-call", false)
	))
	table.insert(body, callStatement(targetCall, prefix .. "-target-call-statement"))
	return document(body), targetCall, target
end

local depth64Fixture, depth64Call, depth64Target = nestedFactoryDocument(64, "local-factory-depth-64")
local depth64Proof = verifyOrigin(depth64Fixture, depth64Call, depth64Target, authenticatedOrigin)
assert(depth64Proof.definition_location == "local-factory-depth-64-current")

local depth65Fixture, depth65Call, depth65Target = nestedFactoryDocument(65, "local-factory-depth-65")
expectFailure(function()
	verifyOrigin(depth65Fixture, depth65Call, depth65Target, authenticatedOrigin)
end, "temporal target definition " .. depth65Target.location)

local assignmentFactory = declaration("localFactoryAssignment", "local-factory-assignment-factory")
local assignmentTarget = declaration("localFactoryAssignmentTarget", "local-factory-assignment-target")
local assignmentTargetCall = callExpression(assignmentTarget, "local-factory-assignment-target-read")
local assignmentProof = verifyOrigin(document({
	localStatement(assignmentFactory, "local-factory-assignment-factory-declaration"),
	assignmentValue(assignmentFactory, "local-factory-assignment-factory-write", returningFunction(
		globalExpression("authenticated_target", "local-factory-assignment-value"),
		"local-factory-assignment-function",
		false
	)),
	callStatement(
		factoryCall(assignmentFactory, {}, "local-factory-assignment-discarded-call", false),
		"local-factory-assignment-discarded-statement"
	),
	localStatement(assignmentTarget, "local-factory-assignment-target-declaration"),
	assignmentValue(
		assignmentTarget,
		"local-factory-assignment-current",
		factoryCall(assignmentFactory, {}, "local-factory-assignment-invocation", false)
	),
	callStatement(assignmentTargetCall, "local-factory-assignment-target-call-statement"),
}), assignmentTargetCall, assignmentTarget, authenticatedOrigin)
assert(assignmentProof.definition_location == "local-factory-assignment-current")

local writtenFactory = declaration("localFactoryWritten", "local-factory-written-factory")
local writtenTarget = declaration("localFactoryWrittenTarget", "local-factory-written-target")
local writtenTargetCall = callExpression(writtenTarget, "local-factory-written-target-read")
local writtenProof = verifyOrigin(document({
	localStatement(writtenFactory, "local-factory-written-factory-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-written-original"),
		"local-factory-written-original-function",
		false
	)),
	assignmentValue(writtenFactory, "local-factory-written-replacement", returningFunction(
		globalExpression("authenticated_target", "local-factory-written-replacement-value"),
		"local-factory-written-replacement-function",
		false
	)),
	localStatement(writtenTarget, "local-factory-written-target-declaration"),
	assignmentValue(writtenTarget, "local-factory-written-current", factoryCall(
		writtenFactory,
		{},
		"local-factory-written-invocation",
		false
	)),
	callStatement(writtenTargetCall, "local-factory-written-target-call-statement"),
	assignmentValue(writtenFactory, "local-factory-written-future", returningFunction(
		differentTarget("local-factory-written-future-value"),
		"local-factory-written-future-function",
		false
	)),
}), writtenTargetCall, writtenTarget, authenticatedOrigin)
assert(writtenProof.definition_location == "local-factory-written-current")

local prewriteFactory = declaration("localFactoryPrewrite", "local-factory-prewrite-factory")
local prewriteTarget = declaration("localFactoryPrewriteTarget", "local-factory-prewrite-target")
local prewriteTargetCall = callExpression(prewriteTarget, "local-factory-prewrite-target-read")
local prewriteProof = verifyOrigin(document({
	localStatement(prewriteFactory, "local-factory-prewrite-factory-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-prewrite-value"),
		"local-factory-prewrite-function",
		false
	)),
	localStatement(prewriteTarget, "local-factory-prewrite-target-declaration"),
	assignmentValue(
		prewriteTarget,
		"local-factory-prewrite-current",
		factoryCall(prewriteFactory, {}, "local-factory-prewrite-invocation", false)
	),
	callStatement(prewriteTargetCall, "local-factory-prewrite-target-call-statement"),
	assignmentValue(prewriteFactory, "local-factory-prewrite-future", returningFunction(
		differentTarget("local-factory-prewrite-future-value"),
		"local-factory-prewrite-future-function",
		false
	)),
}), prewriteTargetCall, prewriteTarget, authenticatedOrigin)
assert(prewriteProof.definition_location == "local-factory-prewrite-current")

local function versionedFactoryDocument(definitionCount: number, prefix: string): (Record, Record, Record)
	assert(definitionCount >= 2)
	local factory = declaration(prefix .. "Factory", prefix .. "-factory")
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local targetCall = callExpression(target, prefix .. "-target-read")
	local body: { Record } = {
		localStatement(factory, prefix .. "-factory-declaration"),
	}
	for index = 2, definitionCount do
		local returned = if index == definitionCount
			then globalExpression("authenticated_target", `{prefix}-value-{index}`)
			else differentTarget(`{prefix}-value-{index}`)
		table.insert(body, assignmentValue(factory, `{prefix}-write-{index}`, returningFunction(
			returned,
			`{prefix}-function-{index}`,
			index % 2 == 0
		)))
	end
	table.insert(body, localStatement(target, prefix .. "-target-declaration"))
	table.insert(body, assignmentValue(target, prefix .. "-current", factoryCall(
		factory,
		{},
		prefix .. "-invocation",
		false
	)))
	table.insert(body, callStatement(targetCall, prefix .. "-target-call-statement"))
	return document(body), targetCall, target
end

local versions64Fixture, versions64Call, versions64Target = versionedFactoryDocument(
	64,
	"local-factory-versions-64"
)
local versions64Proof = verifyOrigin(versions64Fixture, versions64Call, versions64Target, authenticatedOrigin)
assert(versions64Proof.definition_location == "local-factory-versions-64-current")

local versions65Fixture, versions65Call, versions65Target = versionedFactoryDocument(
	65,
	"local-factory-versions-65"
)
expectFailure(function()
	verifyOrigin(versions65Fixture, versions65Call, versions65Target, authenticatedOrigin)
end, "temporal target definition " .. versions65Target.location)

local ordinalAssignmentFactory = declaration(
	"localFactoryOrdinalAssignment",
	"local-factory-ordinal-assignment-factory"
)
local ordinalAssignmentOther = declaration("localFactoryOrdinalAssignmentOther", "local-factory-ordinal-assignment-other")
local ordinalAssignmentTarget = declaration(
	"localFactoryOrdinalAssignmentTarget",
	"local-factory-ordinal-assignment-target"
)
local ordinalAssignmentTargetCall = callExpression(
	ordinalAssignmentTarget,
	"local-factory-ordinal-assignment-target-read"
)
local ordinalAssignmentProof = verifyOrigin(document({
	localStatement(ordinalAssignmentFactory, "local-factory-ordinal-assignment-factory-declaration"),
	localStatement(ordinalAssignmentOther, "local-factory-ordinal-assignment-other-declaration"),
	{
		type = "AstStatAssign",
		location = "local-factory-ordinal-assignment-write",
		vars = {
			localExpression(ordinalAssignmentOther, "local-factory-ordinal-assignment-other-write"),
			localExpression(ordinalAssignmentFactory, "local-factory-ordinal-assignment-factory-write"),
		},
		values = {
			differentTarget("local-factory-ordinal-assignment-other-value"),
			returningFunction(
				globalExpression("authenticated_target", "local-factory-ordinal-assignment-value"),
				"local-factory-ordinal-assignment-function",
				true
			),
			differentTarget("local-factory-ordinal-assignment-extra-value"),
		},
	},
	localStatement(ordinalAssignmentTarget, "local-factory-ordinal-assignment-target-declaration"),
	assignmentValue(
		ordinalAssignmentTarget,
		"local-factory-ordinal-assignment-current",
		factoryCall(ordinalAssignmentFactory, {}, "local-factory-ordinal-assignment-invocation", true)
	),
	callStatement(ordinalAssignmentTargetCall, "local-factory-ordinal-assignment-target-call-statement"),
}), ordinalAssignmentTargetCall, ordinalAssignmentTarget, authenticatedOrigin)
assert(ordinalAssignmentProof.definition_location == "local-factory-ordinal-assignment-current")

local sameStatementFactory = declaration("localFactorySameStatement", "local-factory-same-statement-factory")
local sameStatementTarget = declaration("localFactorySameStatementTarget", "local-factory-same-statement-target")
local sameStatementTargetCall = callExpression(sameStatementTarget, "local-factory-same-statement-target-read")
expectTargetFailure("local-factory-same-statement", {
	localStatement(sameStatementFactory, "local-factory-same-statement-factory-declaration"),
	localStatement(sameStatementTarget, "local-factory-same-statement-target-declaration"),
	{
		type = "AstStatAssign",
		location = "local-factory-same-statement-write",
		vars = {
			localExpression(sameStatementFactory, "local-factory-same-statement-factory-write"),
			localExpression(sameStatementTarget, "local-factory-same-statement-target-write"),
		},
		values = {
			returningFunction(
				globalExpression("authenticated_target", "local-factory-same-statement-value"),
				"local-factory-same-statement-function",
				false
			),
			factoryCall(sameStatementFactory, {}, "local-factory-same-statement-invocation", false),
		},
	},
	callStatement(sameStatementTargetCall, "local-factory-same-statement-target-call-statement"),
}, sameStatementTargetCall, sameStatementTarget)

local branchAssignmentFactory = declaration(
	"localFactoryBranchAssignment",
	"local-factory-branch-assignment-factory"
)
local branchAssignmentCall = factoryCall(
	branchAssignmentFactory,
	{},
	"local-factory-branch-assignment-invocation",
	false
)
expectExpressionFailure(document({
	localStatement(branchAssignmentFactory, "local-factory-branch-assignment-declaration"),
	Support.branchStatement("local-factory-branch-assignment", {
		assignmentValue(branchAssignmentFactory, "local-factory-branch-assignment-write", returningFunction(
			globalExpression("authenticated_target", "local-factory-branch-assignment-value"),
			"local-factory-branch-assignment-function",
			false
		)),
	}, nil),
	callStatement(branchAssignmentCall, "local-factory-branch-assignment-call-statement"),
}), branchAssignmentCall)

local repeatedAssignmentFactory = declaration(
	"localFactoryRepeatedAssignment",
	"local-factory-repeated-assignment-factory"
)
local repeatedAssignmentCall = factoryCall(
	repeatedAssignmentFactory,
	{},
	"local-factory-repeated-assignment-invocation",
	false
)
expectExpressionFailure(document({
	localStatement(repeatedAssignmentFactory, "local-factory-repeated-assignment-declaration"),
	Support.whileStatement("local-factory-repeated-assignment-loop", {
		assignmentValue(repeatedAssignmentFactory, "local-factory-repeated-assignment-write", returningFunction(
			globalExpression("authenticated_target", "local-factory-repeated-assignment-value"),
			"local-factory-repeated-assignment-function",
			false
		)),
		callStatement(repeatedAssignmentCall, "local-factory-repeated-assignment-call-statement"),
	}),
}), repeatedAssignmentCall)

local compoundFactory = declaration("localFactoryCompound", "local-factory-compound-factory")
local compoundCall = factoryCall(compoundFactory, {}, "local-factory-compound-invocation", false)
expectExpressionFailure(document({
	localStatement(compoundFactory, "local-factory-compound-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-compound-value"),
		"local-factory-compound-function",
		false
	)),
	{
		type = "AstStatCompoundAssign",
		location = "local-factory-compound-write",
		var = localExpression(compoundFactory, "local-factory-compound-target"),
		value = differentTarget("local-factory-compound-write-value"),
		op = "Add",
	},
	callStatement(compoundCall, "local-factory-compound-call-statement"),
}), compoundCall)

local capturedAssignmentFactory = declaration(
	"localFactoryCapturedAssignment",
	"local-factory-captured-assignment-factory"
)
local capturedAssignmentCall = factoryCall(
	capturedAssignmentFactory,
	{},
	"local-factory-captured-assignment-invocation",
	false
)
local _, capturedAssignmentOwnerCall = invocationFromBody({
	callStatement(capturedAssignmentCall, "local-factory-captured-assignment-inner-statement"),
}, "local-factory-captured-assignment-owner", nil, nil)
expectExpressionFailure(document({
	localStatement(capturedAssignmentFactory, "local-factory-captured-assignment-declaration"),
	assignmentValue(capturedAssignmentFactory, "local-factory-captured-assignment-write", returningFunction(
		globalExpression("authenticated_target", "local-factory-captured-assignment-value"),
		"local-factory-captured-assignment-function",
		false
	)),
	callStatement(capturedAssignmentOwnerCall, "local-factory-captured-assignment-owner-statement"),
}), capturedAssignmentCall)

local nonfunctionFactory = declaration("localFactoryNonfunction", "local-factory-nonfunction-factory")
local nonfunctionCall = factoryCall(nonfunctionFactory, {}, "local-factory-nonfunction", false)
expectExpressionFailure(document({
	localStatement(
		nonfunctionFactory,
		"local-factory-nonfunction-declaration",
		globalExpression("authenticated_target", "local-factory-nonfunction-value")
	),
	callStatement(nonfunctionCall, "local-factory-nonfunction-call-statement"),
}), nonfunctionCall)

local beforeFactory = declaration("localFactoryBefore", "local-factory-before-factory")
local beforeCall = factoryCall(beforeFactory, {}, "local-factory-before", false)
expectExpressionFailure(document({
	callStatement(beforeCall, "local-factory-before-call-statement"),
	localStatement(beforeFactory, "local-factory-before-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-before-value"),
		"local-factory-before-function",
		false
	)),
}), beforeCall)

local cycleFactory = declaration("localFactoryCycle", "local-factory-cycle-factory")
local cycleInnerCall = factoryCall(cycleFactory, {}, "local-factory-cycle-inner", false)
local cycleOuterCall = factoryCall(cycleFactory, {}, "local-factory-cycle-outer", false)
expectExpressionFailure(document({
	localStatement(
		cycleFactory,
		"local-factory-cycle-declaration",
		returningFunction(cycleInnerCall, "local-factory-cycle-function", false)
	),
	callStatement(cycleOuterCall, "local-factory-cycle-outer-statement"),
}), cycleOuterCall)

local methodFactory = declaration("localFactoryMethod", "local-factory-method-factory")
local methodCall = factoryCall(methodFactory, {}, "local-factory-method", false)
methodCall.self = true
expectExpressionFailure(document({
	localStatement(methodFactory, "local-factory-method-declaration", returningFunction(
		globalExpression("authenticated_target", "local-factory-method-value"),
		"local-factory-method-function",
		false
	)),
	callStatement(methodCall, "local-factory-method-call-statement"),
}), methodCall)

local parameterCallee = declaration("localFactoryParameterCallee", "local-factory-parameter-callee")
local parameterCalleeCall = factoryCall(parameterCallee, {}, "local-factory-parameter-callee", false)
local parameterOwner, parameterOwnerCall = invocationFromBody({
	callStatement(parameterCalleeCall, "local-factory-parameter-callee-statement"),
}, "local-factory-parameter-callee-owner", nil, {
	returningFunction(
		globalExpression("authenticated_target", "local-factory-parameter-callee-value"),
		"local-factory-parameter-callee-argument",
		false
	),
})
parameterOwner.args = { parameterCallee }
expectExpressionFailure(document({
	callStatement(parameterOwnerCall, "local-factory-parameter-callee-owner-statement"),
}), parameterCalleeCall)

local repeatedFactory = declaration("localFactoryRepeated", "local-factory-repeated-factory")
local repeatedFactoryCall = factoryCall(repeatedFactory, {}, "local-factory-repeated", false)
expectExpressionFailure(document({
	Support.whileStatement("local-factory-repeated-loop", {
		localStatement(repeatedFactory, "local-factory-repeated-declaration", returningFunction(
			globalExpression("authenticated_target", "local-factory-repeated-value"),
			"local-factory-repeated-function",
			false
		)),
		callStatement(repeatedFactoryCall, "local-factory-repeated-call-statement"),
	}),
}), repeatedFactoryCall)

local branchFactory = declaration("localFactoryBranch", "local-factory-branch-factory")
local branchFactoryCall = factoryCall(branchFactory, {}, "local-factory-branch", false)
expectExpressionFailure(document({
	Support.branchStatement("local-factory-branch", {
		localStatement(branchFactory, "local-factory-branch-declaration", returningFunction(
			globalExpression("authenticated_target", "local-factory-branch-value"),
			"local-factory-branch-function",
			false
		)),
	}, nil),
	callStatement(branchFactoryCall, "local-factory-branch-call-statement"),
}), branchFactoryCall)

local globalFactoryCall: Record = {
	type = "AstExprCall",
	location = "local-factory-global-call",
	func = globalExpression("factory", "local-factory-global-callee"),
	args = {},
	self = false,
}
expectExpressionFailure(document({
	callStatement(globalFactoryCall, "local-factory-global-call-statement"),
}), globalFactoryCall)

local indexedFactoryCall: Record = {
	type = "AstExprCall",
	location = "local-factory-indexed-call",
	func = {
		type = "AstExprIndexName",
		location = "local-factory-indexed-callee",
		expr = globalExpression("registry", "local-factory-indexed-root"),
		index = "factory",
	},
	args = {},
	self = false,
}
expectExpressionFailure(document({
	callStatement(indexedFactoryCall, "local-factory-indexed-call-statement"),
}), indexedFactoryCall)
