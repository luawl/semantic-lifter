--!strict

local Support = require("./temporal_test_support")
local InvocationSupport = require("./temporal_invocation_test_support")
local TargetOriginReturnSelector = require("./target_origin_return_selector")
local TemporalTargetIdentity = require("./temporal_target_identity")

type Record = Support.Record

local assignmentValue = Support.assignmentValue
local block = Support.block
local callExpression = Support.callExpression
local callStatement = Support.callStatement
local declaration = Support.declaration
local differentTarget = InvocationSupport.differentTarget
local document = Support.document
local expectFailure = Support.expectFailure
local globalExpression = Support.globalExpression
local invocationFromBody = Support.invocationFromBody
local localExpression = Support.localExpression
local localStatement = Support.localStatement
local verifyOrigin = Support.verifyOrigin

local function boolean(value: boolean, prefix: string): Record
	return { type = "AstExprConstantBool", location = prefix .. "-boolean", value = value }
end

local function logicalNot(value: Record, prefix: string): Record
	return { type = "AstExprUnary", location = prefix .. "-not", op = "Not", expr = value }
end

local function shortCircuit(op: string, left: Record, right: Record, prefix: string): Record
	return { type = "AstExprBinary", location = prefix .. "-binary", op = op, left = left, right = right }
end

local function nestedLogicalNot(count: number, prefix: string): Record
	local value: Record = { type = "AstExprConstantNil", location = prefix .. "-value" }
	for index = 1, count do
		value = logicalNot(value, `{prefix}-{index}`)
	end
	return value
end

local function nestedShortCircuit(count: number, prefix: string): Record
	local value = boolean(true, prefix .. "-value")
	for index = 1, count do
		value = shortCircuit("And", boolean(true, `{prefix}-{index}-left`), value, `{prefix}-{index}`)
	end
	return value
end

local function returned(value: Record, prefix: string): Record
	return { type = "AstStatReturn", location = prefix .. "-return", list = { value } }
end

local function closureValue(prefix: string): Record
	local value, _ = invocationFromBody({
		returned(globalExpression("result", prefix .. "-result"), prefix),
	}, prefix, nil, nil)
	return value
end

local function conditionalInvocation(
	prefix: string,
	argument: Record,
	conditionOverride: Record?
): (Record, Record, Record, Record)
	local parameter = declaration(prefix .. "Flag", prefix .. "-parameter")
	local firstAllocation = closureValue(prefix .. "-first")
	local secondAllocation = closureValue(prefix .. "-second")
	local conditional: Record = {
		type = "AstStatIf",
		location = prefix .. "-if",
		condition = conditionOverride or localExpression(parameter, prefix .. "-condition"),
		thenbody = block({ returned(firstAllocation, prefix .. "-then") }, prefix .. "-then-block"),
		elsebody = block({ returned(secondAllocation, prefix .. "-else") }, prefix .. "-else-block"),
	}
	local factory, call = invocationFromBody({ conditional }, prefix .. "-factory", nil, { argument })
	factory.args = { parameter }
	factory.vararg = false
	return call, firstAllocation, secondAllocation, conditional
end

local function conditionalExpressionInvocation(
	prefix: string,
	argument: Record,
	conditionOverride: Record?
): (Record, Record, Record, Record)
	local parameter = declaration(prefix .. "Flag", prefix .. "-parameter")
	local firstAllocation = closureValue(prefix .. "-first")
	local secondAllocation = closureValue(prefix .. "-second")
	local conditional: Record = {
		type = "AstExprIfElse",
		location = prefix .. "-expression",
		condition = conditionOverride or localExpression(parameter, prefix .. "-condition"),
		trueExpr = firstAllocation,
		falseExpr = secondAllocation,
	}
	local factory, call = invocationFromBody({ returned(conditional, prefix) }, prefix .. "-factory", nil, { argument })
	factory.args = { parameter }
	factory.vararg = false
	return call, firstAllocation, secondAllocation, conditional
end

local function targetDocument(prefix: string, value: Record): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-target-read")
	return document({
		localStatement(target, prefix .. "-target-declaration"),
		assignmentValue(target, prefix .. "-current", value),
		callStatement(call, prefix .. "-call-statement"),
		assignmentValue(target, prefix .. "-future", differentTarget(prefix .. "-future-value")),
	}), call, target
end

local function origin(allocation: Record): Record
	return { kind = "closure_value", expression = allocation }
end

local function expectProof(prefix: string, value: Record, allocation: Record)
	local fixture, call, target = targetDocument(prefix, value)
	local proof = verifyOrigin(fixture, call, target, origin(allocation))
	assert(proof.definition_count == 1, `{prefix} conditional factory produced a definition set`)
	assert(proof.definition_location == prefix .. "-current", `{prefix} lost the factory-result write`)
end

local function expectRejection(prefix: string, value: Record, allocation: Record)
	local fixture, call, target = targetDocument(prefix, value)
	expectFailure(function()
		verifyOrigin(fixture, call, target, origin(allocation))
	end, "temporal target definition " .. target.location)
end

assert(
	TargetOriginReturnSelector.fixedConditionTruthiness(nestedLogicalNot(64, "conditional-not-depth-64"), nil)
		== false,
	"logical-not truthiness lost the accepted depth boundary"
)
assert(
	TargetOriginReturnSelector.fixedConditionTruthiness(nestedLogicalNot(65, "conditional-not-depth-65"), nil)
		== nil,
	"logical-not truthiness crossed its depth boundary"
)
assert(
	TargetOriginReturnSelector.fixedConditionTruthiness(nestedShortCircuit(64, "short-circuit-depth-64"), nil)
		== true,
	"short-circuit truthiness lost the accepted depth boundary"
)
assert(
	TargetOriginReturnSelector.fixedConditionTruthiness(nestedShortCircuit(65, "short-circuit-depth-65"), nil)
		== nil,
	"short-circuit truthiness crossed its depth boundary"
)
local cyclicNot = logicalNot(boolean(false, "conditional-not-cycle-value"), "conditional-not-cycle")
cyclicNot.expr = cyclicNot
assert(
	TargetOriginReturnSelector.fixedConditionTruthiness(cyclicNot, nil) == nil,
	"logical-not truthiness accepted a cyclic operand"
)

type TruthinessCase = {
	prefix: string,
	op: string,
	left: Record,
	right: Record,
	expected: boolean?,
}
local truthinessCases: { TruthinessCase } = {
	{ prefix = "short-circuit-false-and-dynamic", op = "And", left = boolean(false, "short-circuit-false-and-dynamic"), right = globalExpression("dynamic", "short-circuit-false-and-dynamic-right"), expected = false },
	{ prefix = "short-circuit-true-or-dynamic", op = "Or", left = boolean(true, "short-circuit-true-or-dynamic"), right = globalExpression("dynamic", "short-circuit-true-or-dynamic-right"), expected = true },
	{ prefix = "short-circuit-dynamic-and-nil", op = "And", left = globalExpression("dynamic", "short-circuit-dynamic-and-nil-left"), right = { type = "AstExprConstantNil", location = "short-circuit-dynamic-and-nil-right" }, expected = false },
	{ prefix = "short-circuit-dynamic-or-zero", op = "Or", left = globalExpression("dynamic", "short-circuit-dynamic-or-zero-left"), right = { type = "AstExprConstantNumber", location = "short-circuit-dynamic-or-zero-right", value = 0 }, expected = true },
	{ prefix = "short-circuit-dynamic-and-true", op = "And", left = globalExpression("dynamic", "short-circuit-dynamic-and-true-left"), right = boolean(true, "short-circuit-dynamic-and-true-right"), expected = nil },
	{ prefix = "short-circuit-dynamic-or-nil", op = "Or", left = globalExpression("dynamic", "short-circuit-dynamic-or-nil-left"), right = { type = "AstExprConstantNil", location = "short-circuit-dynamic-or-nil-right" }, expected = nil },
}
for _, case in truthinessCases do
	assert(
		TargetOriginReturnSelector.fixedConditionTruthiness(
			shortCircuit(case.op, case.left, case.right, case.prefix),
			nil
		) == case.expected,
		`{case.prefix} produced the wrong exact truthiness`
	)
end
local cyclicShortCircuit = shortCircuit(
	"And",
	boolean(true, "short-circuit-cycle-left"),
	boolean(false, "short-circuit-cycle-right"),
	"short-circuit-cycle"
)
cyclicShortCircuit.right = cyclicShortCircuit
assert(
	TargetOriginReturnSelector.fixedConditionTruthiness(cyclicShortCircuit, nil) == nil,
	"short-circuit truthiness accepted a cyclic operand"
)

local trueCall, trueAllocation, trueOther = conditionalInvocation(
	"conditional-factory-true",
	boolean(true, "conditional-factory-true"),
	nil
)
expectProof("conditional-factory-true", trueCall, trueAllocation)
expectRejection("conditional-factory-true-wrong-branch", trueCall, trueOther)

local falseCall, falseOther, falseAllocation = conditionalInvocation(
	"conditional-factory-false",
	boolean(false, "conditional-factory-false"),
	nil
)
expectProof("conditional-factory-false", falseCall, falseAllocation)
expectRejection("conditional-factory-false-wrong-branch", falseCall, falseOther)

local notNilCall, notNilAllocation, notNilOther, notNilConditional = conditionalInvocation(
	"conditional-factory-not-nil",
	{ type = "AstExprConstantNil", location = "conditional-factory-not-nil-argument" },
	nil
)
local notNilParameter = (notNilConditional.condition :: Record)["local"] :: Record
notNilConditional.condition = logicalNot(
	localExpression(notNilParameter, "conditional-factory-not-nil-condition"),
	"conditional-factory-not-nil"
)
expectProof("conditional-factory-not-nil", notNilCall, notNilAllocation)
expectRejection("conditional-factory-not-nil-wrong-branch", notNilCall, notNilOther)

local notZeroCall, notZeroOther, notZeroAllocation, notZeroConditional = conditionalInvocation(
	"conditional-factory-not-zero",
	{ type = "AstExprConstantNumber", location = "conditional-factory-not-zero-argument", value = 0 },
	nil
)
local notZeroParameter = (notZeroConditional.condition :: Record)["local"] :: Record
notZeroConditional.condition = logicalNot(
	localExpression(notZeroParameter, "conditional-factory-not-zero-condition"),
	"conditional-factory-not-zero"
)
expectProof("conditional-factory-not-zero", notZeroCall, notZeroAllocation)
expectRejection("conditional-factory-not-zero-wrong-branch", notZeroCall, notZeroOther)

local shortCircuitCall, shortCircuitAllocation, shortCircuitOther, shortCircuitConditional = conditionalInvocation(
	"conditional-factory-short-circuit",
	{ type = "AstExprConstantNil", location = "conditional-factory-short-circuit-argument" },
	nil
)
local shortCircuitParameter = (shortCircuitConditional.condition :: Record)["local"] :: Record
shortCircuitConditional.condition = shortCircuit(
	"Or",
	localExpression(shortCircuitParameter, "conditional-factory-short-circuit-condition"),
	boolean(true, "conditional-factory-short-circuit-fallback"),
	"conditional-factory-short-circuit"
)
expectProof("conditional-factory-short-circuit", shortCircuitCall, shortCircuitAllocation)
expectRejection("conditional-factory-short-circuit-wrong-branch", shortCircuitCall, shortCircuitOther)

local shortCircuitExpressionCall, shortCircuitExpressionOther, shortCircuitExpressionAllocation, shortCircuitExpression =
	conditionalExpressionInvocation(
		"conditional-expression-short-circuit",
		boolean(true, "conditional-expression-short-circuit-argument"),
		nil
	)
local shortCircuitExpressionParameter = (shortCircuitExpression.condition :: Record)["local"] :: Record
shortCircuitExpression.condition = shortCircuit(
	"And",
	localExpression(shortCircuitExpressionParameter, "conditional-expression-short-circuit-condition"),
	{ type = "AstExprConstantNil", location = "conditional-expression-short-circuit-fallback" },
	"conditional-expression-short-circuit"
)
expectProof(
	"conditional-expression-short-circuit",
	shortCircuitExpressionCall,
	shortCircuitExpressionAllocation
)
expectRejection(
	"conditional-expression-short-circuit-wrong-branch",
	shortCircuitExpressionCall,
	shortCircuitExpressionOther
)

local missingArgumentCall, missingArgumentOther, missingArgumentAllocation = conditionalInvocation(
	"conditional-factory-missing-argument",
	boolean(true, "conditional-factory-missing-argument-unused"),
	nil
)
missingArgumentCall.args = {}
expectProof("conditional-factory-missing-argument", missingArgumentCall, missingArgumentAllocation)
expectRejection(
	"conditional-factory-missing-argument-wrong-branch",
	missingArgumentCall,
	missingArgumentOther
)

local missingTailCall, missingTailOther, missingTailAllocation, missingTailConditional = conditionalInvocation(
	"conditional-factory-missing-tail",
	globalExpression("unused", "conditional-factory-missing-tail-leading"),
	nil
)
local missingTailFactory = missingTailCall.func :: Record
local missingTailParameter = (missingTailConditional.condition :: Record)["local"] :: Record
missingTailFactory.args = {
	declaration("leading", "conditional-factory-missing-tail-leading-parameter"),
	missingTailParameter,
}
expectProof("conditional-factory-missing-tail", missingTailCall, missingTailAllocation)
expectRejection("conditional-factory-missing-tail-wrong-branch", missingTailCall, missingTailOther)

local missingTailOpenCall: Record = {
	type = "AstExprCall",
	location = "conditional-factory-missing-tail-open-call",
	func = globalExpression("unknown_results", "conditional-factory-missing-tail-open-callee"),
	args = {},
	self = false,
}
missingTailCall.args = { missingTailOpenCall }
expectRejection("conditional-factory-missing-tail-open-false", missingTailCall, missingTailAllocation)
expectRejection("conditional-factory-missing-tail-open-true", missingTailCall, missingTailOther)

missingTailCall.args = { {
	type = "AstExprConstantNumber",
	location = "conditional-factory-missing-tail-malformed-number",
	value = "0",
} }
expectRejection("conditional-factory-missing-tail-malformed", missingTailCall, missingTailAllocation)

missingTailCall.args = { {
	type = "AstExprGroup",
	location = "conditional-factory-missing-tail-group",
	expr = missingTailOpenCall,
} }
expectProof("conditional-factory-missing-tail-group", missingTailCall, missingTailAllocation)

local forwardedMissingCall, forwardedMissingOther, forwardedMissingAllocation = conditionalInvocation(
	"conditional-factory-forwarded-missing-inner",
	boolean(true, "conditional-factory-forwarded-missing-unused"),
	nil
)
local forwardedMissingParameter = declaration(
	"forwardedMissing",
	"conditional-factory-forwarded-missing-parameter"
)
forwardedMissingCall.args = { localExpression(
	forwardedMissingParameter,
	"conditional-factory-forwarded-missing-argument"
) }
local forwardedMissingFactory, forwardedMissingOuterCall = invocationFromBody({
	returned(forwardedMissingCall, "conditional-factory-forwarded-missing"),
}, "conditional-factory-forwarded-missing", nil, nil)
forwardedMissingFactory.args = { forwardedMissingParameter }
forwardedMissingFactory.vararg = false
expectProof("conditional-factory-forwarded-missing", forwardedMissingOuterCall, forwardedMissingAllocation)
expectRejection(
	"conditional-factory-forwarded-missing-wrong-branch",
	forwardedMissingOuterCall,
	forwardedMissingOther
)

local varargMissingCall, varargMissingOther, varargMissingAllocation = conditionalInvocation(
	"conditional-factory-vararg-missing-inner",
	boolean(true, "conditional-factory-vararg-missing-unused"),
	nil
)
varargMissingCall.args = { {
	type = "AstExprVarargs",
	location = "conditional-factory-vararg-missing-forward",
} }
local varargMissingFactory, varargMissingOuterCall = invocationFromBody({
	returned(varargMissingCall, "conditional-factory-vararg-missing"),
}, "conditional-factory-vararg-missing", nil, nil)
varargMissingFactory.args = {}
varargMissingFactory.vararg = true
expectProof("conditional-factory-vararg-missing", varargMissingOuterCall, varargMissingAllocation)
expectRejection(
	"conditional-factory-vararg-missing-wrong-branch",
	varargMissingOuterCall,
	varargMissingOther
)

varargMissingOuterCall.args = { {
	type = "AstExprConstantNumber",
	location = "conditional-factory-vararg-number",
	value = 0,
} }
expectProof("conditional-factory-vararg-number", varargMissingOuterCall, varargMissingOther)
expectRejection("conditional-factory-vararg-number-wrong-branch", varargMissingOuterCall, varargMissingAllocation)

varargMissingOuterCall.args = { {
	type = "AstExprCall",
	location = "conditional-factory-vararg-open-call",
	func = globalExpression("unknown_results", "conditional-factory-vararg-open-callee"),
	args = {},
	self = false,
} }
expectRejection("conditional-factory-vararg-open-false", varargMissingOuterCall, varargMissingAllocation)
expectRejection("conditional-factory-vararg-open-true", varargMissingOuterCall, varargMissingOther)

local wrappedFalse: Record = {
	type = "AstExprTypeAssertion",
	location = "conditional-factory-wrapped-false-assertion",
	expr = {
		type = "AstExprGroup",
		location = "conditional-factory-wrapped-false-group",
		expr = boolean(false, "conditional-factory-wrapped-false"),
	},
}
local wrappedCall, _, wrappedAllocation = conditionalInvocation(
	"conditional-factory-wrapped-false",
	wrappedFalse,
	nil
)
expectProof("conditional-factory-wrapped-false", wrappedCall, wrappedAllocation)

local constantCall, constantAllocation = conditionalInvocation(
	"conditional-factory-constant",
	globalExpression("unused", "conditional-factory-constant-argument"),
	boolean(true, "conditional-factory-constant-condition")
)
expectProof("conditional-factory-constant", constantCall, constantAllocation)

local dynamicCall, dynamicAllocation = conditionalInvocation(
	"conditional-factory-dynamic",
	globalExpression("dynamic", "conditional-factory-dynamic-argument"),
	nil
)
expectRejection("conditional-factory-dynamic", dynamicCall, dynamicAllocation)

local malformedCall, malformedAllocation = conditionalInvocation(
	"conditional-factory-malformed",
	{ type = "AstExprConstantBool", location = "conditional-factory-malformed-argument", value = "true" },
	nil
)
expectRejection("conditional-factory-malformed", malformedCall, malformedAllocation)

local unrelatedCondition = declaration("unrelated", "conditional-factory-unrelated-local")
local unrelatedCall, unrelatedAllocation = conditionalInvocation(
	"conditional-factory-unrelated",
	boolean(true, "conditional-factory-unrelated"),
	localExpression(unrelatedCondition, "conditional-factory-unrelated-condition")
)
expectRejection("conditional-factory-unrelated", unrelatedCall, unrelatedAllocation)

local missingElseCall, missingElseAllocation, _, missingElse = conditionalInvocation(
	"conditional-factory-missing-else",
	boolean(true, "conditional-factory-missing-else"),
	nil
)
missingElse.elsebody = nil
expectRejection("conditional-factory-missing-else", missingElseCall, missingElseAllocation)

local branchWorkCall, branchWorkAllocation, _, branchWork = conditionalInvocation(
	"conditional-factory-branch-work",
	boolean(true, "conditional-factory-branch-work"),
	nil
)
table.insert((branchWork.thenbody :: Record).body, 1, callStatement(
	{
		type = "AstExprCall",
		location = "conditional-factory-branch-work-effect",
		func = globalExpression("effect", "conditional-factory-branch-work-effect-callee"),
		args = {},
		self = false,
	},
	"conditional-factory-branch-work-statement"
))
expectRejection("conditional-factory-branch-work", branchWorkCall, branchWorkAllocation)

local reassignedCall, reassignedAllocation, _, reassignedConditional = conditionalInvocation(
	"conditional-factory-reassigned",
	boolean(true, "conditional-factory-reassigned"),
	nil
)
local reassignedFactory = reassignedCall.func :: Record
local reassignedParameter = (reassignedConditional.condition :: Record)["local"] :: Record
table.insert((reassignedFactory.body :: Record).body, 1, assignmentValue(
	reassignedParameter,
	"conditional-factory-reassigned-write",
	boolean(false, "conditional-factory-reassigned-write")
))
expectRejection("conditional-factory-reassigned", reassignedCall, reassignedAllocation)

local unrelatedPrefixCall, unrelatedPrefixAllocation = conditionalInvocation(
	"conditional-factory-unrelated-prefix",
	boolean(true, "conditional-factory-unrelated-prefix"),
	nil
)
local unrelatedPrefixFactory = unrelatedPrefixCall.func :: Record
table.insert((unrelatedPrefixFactory.body :: Record).body, 1, localStatement(
	declaration("unrelatedPrefix", "conditional-factory-unrelated-prefix-local"),
	"conditional-factory-unrelated-prefix-statement",
	closureValue("conditional-factory-unrelated-prefix-allocation")
))
expectRejection("conditional-factory-unrelated-prefix", unrelatedPrefixCall, unrelatedPrefixAllocation)

local expressionTrueCall, expressionTrueAllocation, expressionTrueOther = conditionalExpressionInvocation(
	"conditional-expression-true",
	boolean(true, "conditional-expression-true"),
	nil
)
expectProof("conditional-expression-true", expressionTrueCall, expressionTrueAllocation)
expectRejection("conditional-expression-true-wrong-branch", expressionTrueCall, expressionTrueOther)

local expressionFalseCall, expressionFalseOther, expressionFalseAllocation = conditionalExpressionInvocation(
	"conditional-expression-false",
	boolean(false, "conditional-expression-false"),
	nil
)
expectProof("conditional-expression-false", expressionFalseCall, expressionFalseAllocation)
expectRejection("conditional-expression-false-wrong-branch", expressionFalseCall, expressionFalseOther)

local dynamicExpressionCall, dynamicExpressionAllocation = conditionalExpressionInvocation(
	"conditional-expression-dynamic",
	globalExpression("dynamic", "conditional-expression-dynamic-argument"),
	nil
)
expectRejection("conditional-expression-dynamic", dynamicExpressionCall, dynamicExpressionAllocation)

local function convergentConditionalExpression(prefix: string, falseTarget: string): Record
	local condition = globalExpression("dynamic", prefix .. "-condition")
	local conditional: Record = {
		type = "AstExprIfElse",
		location = prefix .. "-expression",
		condition = condition,
		trueExpr = globalExpression("authenticated_target", prefix .. "-true"),
		falseExpr = globalExpression(falseTarget, prefix .. "-false"),
	}
	local _, call = invocationFromBody({ returned(conditional, prefix) }, prefix .. "-factory", nil, nil)
	return call
end

local convergentCall = convergentConditionalExpression(
	"conditional-expression-convergent",
	"authenticated_target"
)
do
	local fixture, call, target = targetDocument("conditional-expression-convergent", convergentCall)
	local proof = verifyOrigin(fixture, call, target, { kind = "environment", name = "authenticated_target" })
	assert(proof.definition_count == 1, "dynamic conditional convergence produced a definition set")
end

local divergentCall = convergentConditionalExpression(
	"conditional-expression-divergent",
	"different_target"
)
do
	local fixture, call, target = targetDocument("conditional-expression-divergent", divergentCall)
	expectFailure(function()
		verifyOrigin(fixture, call, target, { kind = "environment", name = "authenticated_target" })
	end, "temporal target definition " .. target.location)
end

local function directConditionalMatches(
	prefix: string,
	condition: Record,
	trueTarget: string,
	falseTarget: string,
	malformedFalse: boolean?
): boolean
	local conditional: Record = {
		type = "AstExprIfElse",
		location = prefix .. "-expression",
		condition = condition,
		trueExpr = globalExpression(trueTarget, prefix .. "-true"),
		falseExpr = globalExpression(falseTarget, prefix .. "-false"),
	}
	if malformedFalse then
		conditional.falseExpr = { location = prefix .. "-malformed-false" }
	end
	local call = {
		type = "AstExprCall",
		location = prefix .. "-call",
		func = conditional,
		args = {},
		self = false,
	}
	local fixture = document({ callStatement(call, prefix .. "-statement") })
	return TemporalTargetIdentity.matchesExpression(
		TemporalTargetIdentity.analyze(fixture),
		conditional,
		{ kind = "environment", name = "authenticated_target" }
	)
end

for _, case in {
	{ prefix = "conditional-expression-direct-fixed-true", condition = boolean(true, "conditional-expression-direct-fixed-true"), trueTarget = "authenticated_target", falseTarget = "different_target", expected = true },
	{ prefix = "conditional-expression-direct-fixed-false", condition = boolean(false, "conditional-expression-direct-fixed-false"), trueTarget = "different_target", falseTarget = "authenticated_target", expected = true },
	{ prefix = "conditional-expression-direct-fixed-nil", condition = { type = "AstExprConstantNil", location = "conditional-expression-direct-fixed-nil" }, trueTarget = "different_target", falseTarget = "authenticated_target", expected = true },
	{ prefix = "conditional-expression-direct-fixed-number", condition = { type = "AstExprConstantNumber", location = "conditional-expression-direct-fixed-number", value = 0 }, trueTarget = "authenticated_target", falseTarget = "different_target", expected = true },
	{ prefix = "conditional-expression-direct-fixed-string", condition = { type = "AstExprConstantString", location = "conditional-expression-direct-fixed-string", value = "" }, trueTarget = "authenticated_target", falseTarget = "different_target", expected = true },
	{ prefix = "conditional-expression-direct-not-nil", condition = logicalNot({ type = "AstExprConstantNil", location = "conditional-expression-direct-not-nil-value" }, "conditional-expression-direct-not-nil"), trueTarget = "authenticated_target", falseTarget = "different_target", expected = true },
	{ prefix = "conditional-expression-direct-not-zero", condition = logicalNot({ type = "AstExprConstantNumber", location = "conditional-expression-direct-not-zero-value", value = 0 }, "conditional-expression-direct-not-zero"), trueTarget = "different_target", falseTarget = "authenticated_target", expected = true },
	{ prefix = "conditional-expression-direct-double-not-string", condition = logicalNot(logicalNot({ type = "AstExprConstantString", location = "conditional-expression-direct-double-not-string-value", value = "" }, "conditional-expression-direct-double-not-string-inner"), "conditional-expression-direct-double-not-string"), trueTarget = "authenticated_target", falseTarget = "different_target", expected = true },
	{ prefix = "conditional-expression-direct-dynamic-and-nil", condition = shortCircuit("And", globalExpression("dynamic", "conditional-expression-direct-dynamic-and-nil-left"), { type = "AstExprConstantNil", location = "conditional-expression-direct-dynamic-and-nil-right" }, "conditional-expression-direct-dynamic-and-nil"), trueTarget = "different_target", falseTarget = "authenticated_target", expected = true },
	{ prefix = "conditional-expression-direct-dynamic-or-zero", condition = shortCircuit("Or", globalExpression("dynamic", "conditional-expression-direct-dynamic-or-zero-left"), { type = "AstExprConstantNumber", location = "conditional-expression-direct-dynamic-or-zero-right", value = 0 }, "conditional-expression-direct-dynamic-or-zero"), trueTarget = "authenticated_target", falseTarget = "different_target", expected = true },
	{ prefix = "conditional-expression-direct-not-wrong", condition = logicalNot(boolean(false, "conditional-expression-direct-not-wrong-value"), "conditional-expression-direct-not-wrong"), trueTarget = "different_target", falseTarget = "authenticated_target", expected = false },
	{ prefix = "conditional-expression-direct-unsupported-unary", condition = { type = "AstExprUnary", location = "conditional-expression-direct-unsupported-unary", op = "Minus", expr = { type = "AstExprConstantNumber", value = 0 } }, trueTarget = "authenticated_target", falseTarget = "different_target", expected = false },
	{ prefix = "conditional-expression-direct-malformed-unary", condition = { type = "AstExprUnary", location = "conditional-expression-direct-malformed-unary", op = "Not", expr = { location = "conditional-expression-direct-malformed-unary-value" } }, trueTarget = "authenticated_target", falseTarget = "different_target", expected = false },
	{ prefix = "conditional-expression-direct-unsupported-binary", condition = shortCircuit("Add", boolean(false, "conditional-expression-direct-unsupported-binary-left"), boolean(false, "conditional-expression-direct-unsupported-binary-right"), "conditional-expression-direct-unsupported-binary"), trueTarget = "authenticated_target", falseTarget = "different_target", expected = false },
	{ prefix = "conditional-expression-direct-malformed-binary", condition = { type = "AstExprBinary", location = "conditional-expression-direct-malformed-binary", op = "And", left = boolean(false, "conditional-expression-direct-malformed-binary-left"), right = { location = "conditional-expression-direct-malformed-binary-right" } }, trueTarget = "different_target", falseTarget = "authenticated_target", expected = false },
	{ prefix = "conditional-expression-direct-fixed-wrong", condition = boolean(true, "conditional-expression-direct-fixed-wrong"), trueTarget = "different_target", falseTarget = "authenticated_target", expected = false },
	{ prefix = "conditional-expression-direct-fixed-malformed-number", condition = { type = "AstExprConstantNumber", location = "conditional-expression-direct-fixed-malformed-number", value = "0" }, trueTarget = "authenticated_target", falseTarget = "different_target", expected = false },
} do
	assert(
		directConditionalMatches(case.prefix, case.condition, case.trueTarget, case.falseTarget) == case.expected,
		`{case.prefix} selected the wrong direct conditional arm`
	)
end

assert(not directConditionalMatches(
	"conditional-expression-direct-fixed-malformed",
	boolean(true, "conditional-expression-direct-fixed-malformed"),
	"authenticated_target",
	"different_target",
	true
), "fixed direct conditional accepted a malformed unselected arm")

local function conditionalAliasDocument(
	prefix: string,
	trueIsStable: boolean,
	falseIsStable: boolean,
	condition: Record?
): (Record, Record, Record)
	local stable = declaration(prefix .. "Stable", prefix .. "-stable")
	local other = declaration(prefix .. "Other", prefix .. "-other")
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-call")
	local conditional: Record = {
		type = "AstExprIfElse",
		location = prefix .. "-expression",
		condition = condition or globalExpression("dynamic", prefix .. "-condition"),
		trueExpr = localExpression(if trueIsStable then stable else other, prefix .. "-true"),
		falseExpr = localExpression(if falseIsStable then stable else other, prefix .. "-false"),
	}
	return document({
		localStatement(stable, prefix .. "-stable-declaration", globalExpression("authenticated_target", prefix .. "-stable-value")),
		localStatement(other, prefix .. "-other-declaration", differentTarget(prefix .. "-other-value")),
		localStatement(target, prefix .. "-target-declaration", conditional),
		callStatement(call, prefix .. "-call-statement"),
	}), call, target
end

do
	local fixture, call, target = conditionalAliasDocument("conditional-expression-alias-convergent", true, true, nil)
	local proof = verifyOrigin(fixture, call, target, { kind = "environment", name = "authenticated_target" })
	assert(proof.alias_depth == 2, "conditional alias convergence lost its bounded transfer depth")
end

do
	local fixture, call, target = conditionalAliasDocument("conditional-expression-alias-divergent", true, false, nil)
	expectFailure(function()
		verifyOrigin(fixture, call, target, { kind = "environment", name = "authenticated_target" })
	end, "temporal target definition " .. target.location)
end

type FixedAliasCase = {
	prefix: string,
	condition: Record,
	trueIsStable: boolean,
	falseIsStable: boolean,
}
local fixedAliasCases: { FixedAliasCase } = {
	{ prefix = "conditional-expression-alias-fixed-number", condition = { type = "AstExprConstantNumber", location = "conditional-expression-alias-fixed-number", value = 0 }, trueIsStable = true, falseIsStable = false },
	{ prefix = "conditional-expression-alias-fixed-nil", condition = { type = "AstExprConstantNil", location = "conditional-expression-alias-fixed-nil" }, trueIsStable = false, falseIsStable = true },
	{ prefix = "conditional-expression-alias-not-number", condition = logicalNot({ type = "AstExprConstantNumber", location = "conditional-expression-alias-not-number-value", value = 0 }, "conditional-expression-alias-not-number"), trueIsStable = false, falseIsStable = true },
	{ prefix = "conditional-expression-alias-not-nil", condition = logicalNot({ type = "AstExprConstantNil", location = "conditional-expression-alias-not-nil-value" }, "conditional-expression-alias-not-nil"), trueIsStable = true, falseIsStable = false },
	{ prefix = "conditional-expression-alias-dynamic-and-nil", condition = shortCircuit("And", globalExpression("dynamic", "conditional-expression-alias-dynamic-and-nil-left"), { type = "AstExprConstantNil", location = "conditional-expression-alias-dynamic-and-nil-right" }, "conditional-expression-alias-dynamic-and-nil"), trueIsStable = false, falseIsStable = true },
	{ prefix = "conditional-expression-alias-dynamic-or-zero", condition = shortCircuit("Or", globalExpression("dynamic", "conditional-expression-alias-dynamic-or-zero-left"), { type = "AstExprConstantNumber", location = "conditional-expression-alias-dynamic-or-zero-right", value = 0 }, "conditional-expression-alias-dynamic-or-zero"), trueIsStable = true, falseIsStable = false },
}
for _, case in fixedAliasCases do
	local fixture, call, target = conditionalAliasDocument(
		case.prefix,
		case.trueIsStable,
		case.falseIsStable,
		case.condition
	)
	local proof = verifyOrigin(fixture, call, target, { kind = "environment", name = "authenticated_target" })
	assert(proof.alias_depth == 2, `{case.prefix} lost its selected alias transfer depth`)
end

local malformedExpressionCall, malformedExpressionAllocation, _, malformedExpression = conditionalExpressionInvocation(
	"conditional-expression-malformed",
	boolean(true, "conditional-expression-malformed"),
	nil
)
malformedExpression.falseExpr = { location = "conditional-expression-malformed-false" }
expectRejection("conditional-expression-malformed", malformedExpressionCall, malformedExpressionAllocation)

return true
