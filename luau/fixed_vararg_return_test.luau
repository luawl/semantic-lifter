--!strict

local TargetOriginMatcher = require("./target_origin_matcher")
local Support = require("./temporal_test_support")
local InvocationSupport = require("./temporal_invocation_test_support")

type Record = Support.Record

local authenticatedOrigin: Record = { kind = "environment", name = "authenticated_target" }

local function returnStatement(values: { Record }, prefix: string): Record
	return { type = "AstStatReturn", location = prefix .. "-return", list = values }
end

local function varargs(prefix: string): Record
	return { type = "AstExprVarargs", location = prefix .. "-varargs" }
end

local function variadicCall(
	returnValues: { Record },
	arguments: { Record },
	fixedParameterCount: number,
	prefix: string
): (Record, { Record }, Record)
	local parameters: { Record } = {}
	for index = 1, fixedParameterCount do
		table.insert(parameters, Support.declaration(`{prefix}Parameter{index}`, `{prefix}-parameter-{index}`))
	end
	local functionValue, call = Support.invocationFromBody({
		returnStatement(returnValues, prefix),
	}, prefix, nil, arguments)
	functionValue.args = parameters
	functionValue.vararg = true
	return call, parameters, functionValue
end

local function projectResult(
	source: Record,
	ordinal: number,
	width: number,
	prefix: string,
	useAsCallee: boolean?
): (Record, Record)
	assert(ordinal >= 1 and ordinal <= width)
	local selected = Support.declaration(prefix .. "Selected", prefix .. "-selected")
	local targets: { Record } = {}
	for index = 1, width do
		table.insert(targets, if index == ordinal
			then selected
			else Support.declaration(`{prefix}Ignored{index}`, `{prefix}-ignored-{index}`))
	end
	local returned = Support.localExpression(selected, prefix .. "-selected-read")
	local functionValue, call = Support.invocationFromBody({
		{
			type = "AstStatLocal",
			location = prefix .. "-projection",
			vars = targets,
			values = { source },
		},
		returnStatement({ if useAsCallee == true
			then Support.callExpression(selected, prefix .. "-selected-call")
			else returned }, prefix),
	}, prefix .. "-projection-owner", nil, nil)
	return call, functionValue
end

local function matches(value: Record): boolean
	return TargetOriginMatcher.matches(value, authenticatedOrigin, function(_expression: Record, _origin: Record): boolean
		return false
	end)
end

local function expectMatch(label: string, value: Record)
	assert(matches(value), `{label} did not preserve fixed vararg identity`)
end

local function expectNoMatch(label: string, value: Record)
	assert(not matches(value), `{label} invented fixed vararg identity`)
end

local function authenticatedCallable(prefix: string): Record
	local functionValue, _ = Support.invocationFromBody({
		returnStatement({ Support.globalExpression("authenticated_target", prefix .. "-value") }, prefix),
	}, prefix, nil, nil)
	return functionValue
end

local function nestedResultCall(selected: Record, prefix: string): Record
	local _, call = Support.invocationFromBody({
		returnStatement({
			InvocationSupport.differentTarget(prefix .. "-ignored"),
			selected,
		}, prefix),
	}, prefix, nil, nil)
	return call
end

local function fixedParameterCall(
	arguments: { Record },
	parameterCount: number,
	selectedIndex: number,
	prefix: string,
	useAsCallee: boolean
): (Record, Record, { Record })
	assert(selectedIndex >= 1 and selectedIndex <= parameterCount)
	local call, parameters, functionValue = variadicCall({}, arguments, parameterCount, prefix)
	functionValue.vararg = false
	functionValue.body.body[1].list = {
		if useAsCallee
			then Support.callExpression(parameters[selectedIndex], prefix .. "-selected-call")
			else Support.localExpression(parameters[selectedIndex], prefix .. "-selected-read"),
	}
	return call, functionValue, parameters
end

local function forwardedParameterCall(
	outerArguments: { Record },
	outerFixedParameterCount: number,
	innerArguments: { Record },
	innerParameterCount: number,
	selectedIndex: number,
	prefix: string,
	useAsCallee: boolean
): (Record, Record, { Record }, Record, { Record })
	local innerCall, innerFunction, innerParameters = fixedParameterCall(
		innerArguments,
		innerParameterCount,
		selectedIndex,
		prefix .. "-inner",
		useAsCallee
	)
	local outerCall, outerParameters, outerFunction = variadicCall(
		{ innerCall },
		outerArguments,
		outerFixedParameterCount,
		prefix
	)
	return outerCall, outerFunction, outerParameters, innerFunction, innerParameters
end

local function snapshotVarargCall(
	arguments: { Record },
	ordinal: number,
	prefix: string,
	assignmentBacked: boolean
): Record
	local selected = Support.declaration(prefix .. "Selected", prefix .. "-selected")
	local targets: { Record } = {}
	for index = 1, ordinal do
		table.insert(targets, if index == ordinal
			then selected
			else Support.declaration(`{prefix}Ignored{index}`, `{prefix}-ignored-{index}`))
	end
	local functionValue, call = Support.invocationFromBody({
		{
			type = "AstStatLocal",
			location = prefix .. "-snapshot",
			vars = targets,
			values = { varargs(prefix) },
		},
		returnStatement({ Support.localExpression(selected, prefix .. "-selected-read") }, prefix),
	}, prefix, nil, arguments)
	functionValue.vararg = true
	if assignmentBacked then
		functionValue.body.body = Support.assignmentBackedSnapshots(functionValue.body.body, prefix)
	end
	return call
end

local function nestedVarargCall(depth: number, prefix: string): Record
	assert(depth >= 1)
	local value = Support.globalExpression("authenticated_target", prefix .. "-selected")
	for index = 1, depth do
		value = variadicCall({ varargs(`{prefix}-{index}`) }, { value }, 0, `{prefix}-{index}`)
	end
	return value
end

local directCall = variadicCall({
	varargs("fixed-vararg-direct"),
}, {
	InvocationSupport.differentTarget("fixed-vararg-direct-ignored"),
	Support.globalExpression("authenticated_target", "fixed-vararg-direct-selected"),
}, 0, "fixed-vararg-direct")
expectMatch("fixed-vararg-direct", (projectResult(directCall, 2, 2, "fixed-vararg-direct", false)))

local leadingCall, leadingParameters = variadicCall({}, {
	InvocationSupport.differentTarget("fixed-vararg-leading-parameter-value"),
	InvocationSupport.differentTarget("fixed-vararg-leading-ignored"),
	Support.globalExpression("authenticated_target", "fixed-vararg-leading-selected"),
}, 1, "fixed-vararg-leading")
leadingCall.func.body.body[1].list = {
	Support.localExpression(leadingParameters[1], "fixed-vararg-leading-parameter-read"),
	varargs("fixed-vararg-leading"),
}
expectMatch("fixed-vararg-leading", (projectResult(leadingCall, 3, 3, "fixed-vararg-leading", false)))

local nestedCall = nestedResultCall(
	Support.globalExpression("authenticated_target", "fixed-vararg-final-call-selected"),
	"fixed-vararg-final-call-nested"
)
local finalCall = variadicCall({
	varargs("fixed-vararg-final-call"),
}, {
	InvocationSupport.differentTarget("fixed-vararg-final-call-leading"),
	nestedCall,
}, 0, "fixed-vararg-final-call")
expectMatch("fixed-vararg-final-call", (projectResult(finalCall, 3, 3, "fixed-vararg-final-call", false)))

local fixedFromCall = variadicCall({
	varargs("fixed-vararg-fixed-from-call"),
}, {
	nestedResultCall(
		Support.globalExpression("authenticated_target", "fixed-vararg-fixed-from-call-selected"),
		"fixed-vararg-fixed-from-call-nested"
	),
}, 1, "fixed-vararg-fixed-from-call")
expectMatch("fixed-vararg-fixed-from-call", fixedFromCall)

local fixedParameterTailCall = fixedParameterCall({
	nestedResultCall(
		Support.globalExpression("authenticated_target", "fixed-parameter-tail-direct-selected"),
		"fixed-parameter-tail-direct-nested"
	),
}, 2, 2, "fixed-parameter-tail-direct", false)
expectMatch("fixed-parameter-tail-direct", fixedParameterTailCall)

local fixedParameterLeadingCall = fixedParameterCall({
	InvocationSupport.differentTarget("fixed-parameter-tail-leading-explicit"),
	nestedResultCall(
		Support.globalExpression("authenticated_target", "fixed-parameter-tail-leading-selected"),
		"fixed-parameter-tail-leading-nested"
	),
}, 3, 3, "fixed-parameter-tail-leading", false)
expectMatch("fixed-parameter-tail-leading", fixedParameterLeadingCall)

local fixedParameterSnapshotCall, fixedParameterSnapshotFunction, fixedParameterSnapshotParameters = fixedParameterCall({
	nestedResultCall(
		Support.globalExpression("authenticated_target", "fixed-parameter-tail-snapshot-selected"),
		"fixed-parameter-tail-snapshot-nested"
	),
}, 2, 2, "fixed-parameter-tail-snapshot", false)
local fixedParameterSnapshot = Support.declaration(
	"fixedParameterTailSnapshot",
	"fixed-parameter-tail-snapshot-local"
)
fixedParameterSnapshotFunction.body.body = {
	{
		type = "AstStatLocal",
		location = "fixed-parameter-tail-snapshot-statement",
		vars = { fixedParameterSnapshot },
		values = {
			Support.localExpression(fixedParameterSnapshotParameters[2], "fixed-parameter-tail-snapshot-value"),
		},
	},
	returnStatement({
		Support.localExpression(fixedParameterSnapshot, "fixed-parameter-tail-snapshot-read"),
	}, "fixed-parameter-tail-snapshot"),
}
expectMatch("fixed-parameter-tail-snapshot", fixedParameterSnapshotCall)
fixedParameterSnapshotFunction.body.body = Support.assignmentBackedSnapshots(
	fixedParameterSnapshotFunction.body.body,
	"fixed-parameter-tail-assignment-snapshot"
)
expectMatch("fixed-parameter-tail-assignment-snapshot", fixedParameterSnapshotCall)

local fixedParameterCallableCall = fixedParameterCall({
	nestedResultCall(
		authenticatedCallable("fixed-parameter-tail-callable-selected"),
		"fixed-parameter-tail-callable-nested"
	),
}, 2, 2, "fixed-parameter-tail-callable", true)
expectMatch("fixed-parameter-tail-callable", fixedParameterCallableCall)

local fixedParameterCallerProducer = authenticatedCallable("fixed-parameter-tail-caller-producer-value")
fixedParameterCallerProducer.body.body[1].list = {
	InvocationSupport.differentTarget("fixed-parameter-tail-caller-producer-ignored"),
	Support.globalExpression("authenticated_target", "fixed-parameter-tail-caller-producer-selected"),
}
local fixedParameterCaller = Support.declaration(
	"fixedParameterTailCaller",
	"fixed-parameter-tail-caller-parameter"
)
local fixedParameterCallerResult = fixedParameterCall({
	Support.callExpression(fixedParameterCaller, "fixed-parameter-tail-caller-invocation"),
}, 2, 2, "fixed-parameter-tail-caller-inner", false)
local fixedParameterCallerFunction, fixedParameterCallerCall = Support.invocationFromBody({
	returnStatement({ fixedParameterCallerResult }, "fixed-parameter-tail-caller"),
}, "fixed-parameter-tail-caller", nil, { fixedParameterCallerProducer })
fixedParameterCallerFunction.args = { fixedParameterCaller }
expectMatch("fixed-parameter-tail-caller", fixedParameterCallerCall)

local forwardedVarargCall = forwardedParameterCall({
	InvocationSupport.differentTarget("forwarded-vararg-direct-ignored"),
	Support.globalExpression("authenticated_target", "forwarded-vararg-direct-selected"),
}, 0, { varargs("forwarded-vararg-direct") }, 2, 2, "forwarded-vararg-direct", false)
expectMatch("forwarded-vararg-direct", forwardedVarargCall)

local forwardedVarargFixedPrefixCall = forwardedParameterCall({
	InvocationSupport.differentTarget("forwarded-vararg-fixed-prefix-parameter"),
	InvocationSupport.differentTarget("forwarded-vararg-fixed-prefix-ignored"),
	Support.globalExpression("authenticated_target", "forwarded-vararg-fixed-prefix-selected"),
}, 1, { varargs("forwarded-vararg-fixed-prefix") }, 2, 2, "forwarded-vararg-fixed-prefix", false)
expectMatch("forwarded-vararg-fixed-prefix", forwardedVarargFixedPrefixCall)

local forwardedVarargFinalCall = forwardedParameterCall({
	nestedResultCall(
		Support.globalExpression("authenticated_target", "forwarded-vararg-final-call-selected"),
		"forwarded-vararg-final-call-nested"
	),
}, 0, { varargs("forwarded-vararg-final-call") }, 2, 2, "forwarded-vararg-final-call", false)
expectMatch("forwarded-vararg-final-call", forwardedVarargFinalCall)

local forwardedVarargSnapshotCall, _, _, forwardedVarargSnapshotFunction, forwardedVarargSnapshotParameters =
	forwardedParameterCall({
		InvocationSupport.differentTarget("forwarded-vararg-snapshot-ignored"),
		Support.globalExpression("authenticated_target", "forwarded-vararg-snapshot-selected"),
	}, 0, { varargs("forwarded-vararg-snapshot") }, 2, 2, "forwarded-vararg-snapshot", false)
local forwardedVarargSnapshot = Support.declaration("forwardedVarargSnapshot", "forwarded-vararg-snapshot-local")
forwardedVarargSnapshotFunction.body.body = {
	{
		type = "AstStatLocal",
		location = "forwarded-vararg-snapshot-statement",
		vars = { forwardedVarargSnapshot },
		values = {
			Support.localExpression(forwardedVarargSnapshotParameters[2], "forwarded-vararg-snapshot-value"),
		},
	},
	returnStatement({ Support.localExpression(forwardedVarargSnapshot, "forwarded-vararg-snapshot-read") },
		"forwarded-vararg-snapshot"),
}
expectMatch("forwarded-vararg-snapshot", forwardedVarargSnapshotCall)
forwardedVarargSnapshotFunction.body.body = Support.assignmentBackedSnapshots(
	forwardedVarargSnapshotFunction.body.body,
	"forwarded-vararg-assignment-snapshot"
)
expectMatch("forwarded-vararg-assignment-snapshot", forwardedVarargSnapshotCall)

local forwardedVarargCallableCall = forwardedParameterCall({
	InvocationSupport.differentTarget("forwarded-vararg-callable-ignored"),
	authenticatedCallable("forwarded-vararg-callable-selected"),
}, 0, { varargs("forwarded-vararg-callable") }, 2, 2, "forwarded-vararg-callable", true)
expectMatch("forwarded-vararg-callable", forwardedVarargCallableCall)

local nestedForwardedInner = fixedParameterCall({
	varargs("forwarded-vararg-nested-inner"),
}, 2, 2, "forwarded-vararg-nested-inner", false)
local nestedForwardedMiddle = variadicCall({ nestedForwardedInner }, {
	varargs("forwarded-vararg-nested-middle"),
}, 0, "forwarded-vararg-nested-middle")
local nestedForwardedOuter = variadicCall({ nestedForwardedMiddle }, {
	InvocationSupport.differentTarget("forwarded-vararg-nested-ignored"),
	Support.globalExpression("authenticated_target", "forwarded-vararg-nested-selected"),
}, 0, "forwarded-vararg-nested-outer")
expectMatch("forwarded-vararg-nested", nestedForwardedOuter)

local forwardedVarargNonfinalCall = forwardedParameterCall({
	Support.globalExpression("authenticated_target", "forwarded-vararg-nonfinal-selected"),
	InvocationSupport.differentTarget("forwarded-vararg-nonfinal-hidden"),
}, 0, {
	varargs("forwarded-vararg-nonfinal"),
	InvocationSupport.differentTarget("forwarded-vararg-nonfinal-trailing"),
}, 2, 1, "forwarded-vararg-nonfinal", false)
expectMatch("forwarded-vararg-nonfinal", forwardedVarargNonfinalCall)

local forwardedVarargNonfinalHiddenCall = forwardedParameterCall({
	InvocationSupport.differentTarget("forwarded-vararg-nonfinal-hidden-leading"),
	Support.globalExpression("authenticated_target", "forwarded-vararg-nonfinal-hidden-selected"),
}, 0, {
	varargs("forwarded-vararg-nonfinal-hidden"),
	InvocationSupport.differentTarget("forwarded-vararg-nonfinal-hidden-trailing"),
}, 2, 2, "forwarded-vararg-nonfinal-hidden", false)
expectNoMatch("forwarded-vararg-nonfinal-hidden", forwardedVarargNonfinalHiddenCall)

local forwardedVarargMissingCall = forwardedParameterCall({
	InvocationSupport.differentTarget("forwarded-vararg-missing-only"),
}, 0, { varargs("forwarded-vararg-missing") }, 2, 2, "forwarded-vararg-missing", false)
expectNoMatch("forwarded-vararg-missing", forwardedVarargMissingCall)

local forwardedVarargOpenTailCall = forwardedParameterCall({
	varargs("forwarded-vararg-open-tail-outer"),
}, 0, { varargs("forwarded-vararg-open-tail-inner") }, 2, 2, "forwarded-vararg-open-tail", false)
expectNoMatch("forwarded-vararg-open-tail", forwardedVarargOpenTailCall)

local forwardedBarrierInner = fixedParameterCall({
	varargs("forwarded-vararg-barrier-inner"),
}, 2, 2, "forwarded-vararg-barrier-inner", false)
local forwardedBarrierFunction, forwardedBarrierCall = Support.invocationFromBody({
	returnStatement({ forwardedBarrierInner }, "forwarded-vararg-barrier"),
}, "forwarded-vararg-barrier", nil, nil)
forwardedBarrierFunction.vararg = false
local forwardedBarrierOuterFunction, forwardedBarrierOuterCall = Support.invocationFromBody({
	returnStatement({ forwardedBarrierCall }, "forwarded-vararg-barrier-outer"),
}, "forwarded-vararg-barrier-outer", nil, {
	InvocationSupport.differentTarget("forwarded-vararg-barrier-ignored"),
	Support.globalExpression("authenticated_target", "forwarded-vararg-barrier-hidden"),
})
forwardedBarrierOuterFunction.vararg = true
expectNoMatch("forwarded-vararg-barrier", forwardedBarrierOuterCall)

local fixedParameterNonfinalCall = fixedParameterCall({
	nestedResultCall(
		Support.globalExpression("authenticated_target", "fixed-parameter-tail-nonfinal-hidden"),
		"fixed-parameter-tail-nonfinal-nested"
	),
	InvocationSupport.differentTarget("fixed-parameter-tail-nonfinal-trailing"),
}, 2, 2, "fixed-parameter-tail-nonfinal", false)
expectNoMatch("fixed-parameter-tail-nonfinal", fixedParameterNonfinalCall)

local fixedParameterMissingCall = fixedParameterCall({
	InvocationSupport.differentTarget("fixed-parameter-tail-missing-only"),
}, 2, 2, "fixed-parameter-tail-missing", false)
expectNoMatch("fixed-parameter-tail-missing", fixedParameterMissingCall)

local fixedParameterForwardedCall = fixedParameterCall({
	varargs("fixed-parameter-tail-forwarded-argument"),
}, 2, 2, "fixed-parameter-tail-forwarded", false)
expectNoMatch("fixed-parameter-tail-forwarded", fixedParameterForwardedCall)

local nonfinalArgument = variadicCall({
	varargs("fixed-vararg-nonfinal-argument"),
}, {
	nestedResultCall(
		Support.globalExpression("authenticated_target", "fixed-vararg-nonfinal-argument-hidden"),
		"fixed-vararg-nonfinal-argument-nested"
	),
	InvocationSupport.differentTarget("fixed-vararg-nonfinal-argument-trailing"),
}, 0, "fixed-vararg-nonfinal-argument")
expectNoMatch("fixed-vararg-nonfinal-argument", nonfinalArgument)

expectMatch("fixed-vararg-snapshot", snapshotVarargCall({
	InvocationSupport.differentTarget("fixed-vararg-snapshot-ignored"),
	Support.globalExpression("authenticated_target", "fixed-vararg-snapshot-selected"),
}, 2, "fixed-vararg-snapshot", false))
expectMatch("fixed-vararg-assignment-snapshot", snapshotVarargCall({
	InvocationSupport.differentTarget("fixed-vararg-assignment-snapshot-ignored"),
	Support.globalExpression("authenticated_target", "fixed-vararg-assignment-snapshot-selected"),
}, 2, "fixed-vararg-assignment-snapshot", true))

local callableCall = variadicCall({
	varargs("fixed-vararg-callable"),
}, {
	InvocationSupport.differentTarget("fixed-vararg-callable-ignored"),
	authenticatedCallable("fixed-vararg-callable-selected"),
}, 0, "fixed-vararg-callable")
expectMatch("fixed-vararg-callable", (projectResult(callableCall, 2, 2, "fixed-vararg-callable", true)))

local nonfinalCall = variadicCall({
	varargs("fixed-vararg-nonfinal"),
	InvocationSupport.differentTarget("fixed-vararg-nonfinal-trailing"),
}, {
	Support.globalExpression("authenticated_target", "fixed-vararg-nonfinal-selected"),
}, 0, "fixed-vararg-nonfinal")
expectMatch("fixed-vararg-nonfinal", (projectResult(nonfinalCall, 1, 1, "fixed-vararg-nonfinal", false)))

local nonfinalTailCall = variadicCall({
	varargs("fixed-vararg-nonfinal-tail"),
	InvocationSupport.differentTarget("fixed-vararg-nonfinal-tail-trailing"),
}, {
	InvocationSupport.differentTarget("fixed-vararg-nonfinal-tail-ignored"),
	Support.globalExpression("authenticated_target", "fixed-vararg-nonfinal-tail-hidden"),
}, 0, "fixed-vararg-nonfinal-tail")
expectNoMatch(
	"fixed-vararg-nonfinal-tail",
	(projectResult(nonfinalTailCall, 2, 2, "fixed-vararg-nonfinal-tail", false))
)

local enclosingParameter = Support.declaration("fixedVarargParameter", "fixed-vararg-parameter")
local parameterInnerCall = variadicCall({ varargs("fixed-vararg-parameter-inner") }, {
	Support.localExpression(enclosingParameter, "fixed-vararg-parameter-inner-argument"),
}, 0, "fixed-vararg-parameter-inner")
local parameterFunction, parameterCall = Support.invocationFromBody({
	returnStatement({ parameterInnerCall }, "fixed-vararg-parameter"),
}, "fixed-vararg-parameter", nil, {
	Support.globalExpression("authenticated_target", "fixed-vararg-parameter-selected"),
})
parameterFunction.args = { enclosingParameter }
expectMatch("fixed-vararg-parameter", parameterCall)

local nonVariadicCall, _, nonVariadicFunction = variadicCall({
	varargs("fixed-vararg-nonvariadic"),
}, {
	Support.globalExpression("authenticated_target", "fixed-vararg-nonvariadic-selected"),
}, 0, "fixed-vararg-nonvariadic")
nonVariadicFunction.vararg = false
expectNoMatch("fixed-vararg-nonvariadic", nonVariadicCall)

local missingCall = variadicCall({
	varargs("fixed-vararg-missing"),
}, {
	InvocationSupport.differentTarget("fixed-vararg-missing-only"),
}, 0, "fixed-vararg-missing")
expectNoMatch("fixed-vararg-missing", (projectResult(missingCall, 2, 2, "fixed-vararg-missing", false)))

local forwardedCall = variadicCall({
	varargs("fixed-vararg-forwarded"),
}, {
	varargs("fixed-vararg-forwarded-argument"),
}, 0, "fixed-vararg-forwarded")
expectNoMatch("fixed-vararg-forwarded", (projectResult(forwardedCall, 2, 2, "fixed-vararg-forwarded", false)))

for _, wrapper in { "AstExprGroup", "AstExprTypeAssertion", "AstExprInstantiate" } do
	local prefix = "fixed-vararg-final-call-" .. wrapper
	local wrappedCall = nestedResultCall(
		Support.globalExpression("authenticated_target", prefix .. "-selected"),
		prefix .. "-nested"
	)
	local source = variadicCall({ varargs(prefix) }, {
		InvocationSupport.differentTarget(prefix .. "-leading"),
		{ type = wrapper, location = prefix .. "-wrapper", expr = wrappedCall },
	}, 0, prefix)
	expectNoMatch(prefix, (projectResult(source, 3, 3, prefix, false)))
	local fixedPrefix = "fixed-parameter-tail-final-call-" .. wrapper
	local fixedWrappedCall = nestedResultCall(
		Support.globalExpression("authenticated_target", fixedPrefix .. "-selected"),
		fixedPrefix .. "-nested"
	)
	expectNoMatch(fixedPrefix, (fixedParameterCall({
		{ type = wrapper, location = fixedPrefix .. "-wrapper", expr = fixedWrappedCall },
	}, 2, 2, fixedPrefix, false)))
	local forwardedPrefix = "forwarded-vararg-wrapper-" .. wrapper
	local forwardedWrapped: Record = {
		type = wrapper,
		location = forwardedPrefix .. "-wrapper",
		expr = varargs(forwardedPrefix),
	}
	expectMatch(forwardedPrefix .. "-first", (forwardedParameterCall({
		Support.globalExpression("authenticated_target", forwardedPrefix .. "-selected"),
	}, 0, { forwardedWrapped }, 1, 1, forwardedPrefix .. "-first", false)))
	expectNoMatch(forwardedPrefix .. "-closed", (forwardedParameterCall({
		InvocationSupport.differentTarget(forwardedPrefix .. "-ignored"),
		Support.globalExpression("authenticated_target", forwardedPrefix .. "-hidden"),
	}, 0, { forwardedWrapped }, 2, 2, forwardedPrefix .. "-closed", false)))
end

local methodResult = nestedResultCall(
	Support.globalExpression("authenticated_target", "fixed-vararg-method-selected"),
	"fixed-vararg-method-nested"
)
methodResult.self = true
local methodCall = variadicCall({ varargs("fixed-vararg-method") }, {
	InvocationSupport.differentTarget("fixed-vararg-method-leading"),
	methodResult,
}, 0, "fixed-vararg-method")
expectNoMatch("fixed-vararg-method", (projectResult(methodCall, 3, 3, "fixed-vararg-method", false)))

local fixedParameterMethodResult = nestedResultCall(
	Support.globalExpression("authenticated_target", "fixed-parameter-tail-method-selected"),
	"fixed-parameter-tail-method-nested"
)
fixedParameterMethodResult.self = true
expectNoMatch("fixed-parameter-tail-method", (fixedParameterCall({
	fixedParameterMethodResult,
}, 2, 2, "fixed-parameter-tail-method", false)))

local malformedCall = variadicCall({ varargs("fixed-vararg-malformed") }, {
	Support.globalExpression("authenticated_target", "fixed-vararg-malformed-selected"),
}, 0, "fixed-vararg-malformed")
malformedCall.args.extra = InvocationSupport.differentTarget("fixed-vararg-malformed-extra")
expectNoMatch("fixed-vararg-malformed", malformedCall)

local cycleCall = variadicCall({ varargs("fixed-vararg-cycle") }, {}, 0, "fixed-vararg-cycle")
cycleCall.args = { cycleCall }
expectNoMatch("fixed-vararg-cycle", (projectResult(cycleCall, 2, 2, "fixed-vararg-cycle", false)))

local fixedParameterCycleCall = fixedParameterCall({}, 2, 2, "fixed-parameter-tail-cycle", false)
fixedParameterCycleCall.args = { fixedParameterCycleCall }
expectNoMatch("fixed-parameter-tail-cycle", fixedParameterCycleCall)

local forwardedVarargCycleCall = forwardedParameterCall({}, 0, {
	varargs("forwarded-vararg-cycle"),
}, 2, 2, "forwarded-vararg-cycle", false)
forwardedVarargCycleCall.args = { forwardedVarargCycleCall }
expectNoMatch("forwarded-vararg-cycle", forwardedVarargCycleCall)

local forwardedVarargMalformedCall = forwardedParameterCall({
	InvocationSupport.differentTarget("forwarded-vararg-malformed-ignored"),
	Support.globalExpression("authenticated_target", "forwarded-vararg-malformed-hidden"),
}, 0, { varargs("forwarded-vararg-malformed") }, 2, 2, "forwarded-vararg-malformed", false)
forwardedVarargMalformedCall.args.extra = InvocationSupport.differentTarget("forwarded-vararg-malformed-extra")
expectNoMatch("forwarded-vararg-malformed", forwardedVarargMalformedCall)

local arguments64: { Record } = {}
for index = 1, 64 do
	table.insert(arguments64, if index == 64
		then Support.globalExpression("authenticated_target", "fixed-vararg-width-64-selected")
		else InvocationSupport.differentTarget(`fixed-vararg-width-64-ignored-{index}`))
end
local width64Call = variadicCall({ varargs("fixed-vararg-width-64") }, arguments64, 0, "fixed-vararg-width-64")
expectMatch("fixed-vararg-width-64", (projectResult(width64Call, 64, 64, "fixed-vararg-width-64", false)))

local arguments65 = table.clone(arguments64)
table.insert(arguments65, InvocationSupport.differentTarget("fixed-vararg-width-65-extra"))
local width65Call = variadicCall({ varargs("fixed-vararg-width-65") }, arguments65, 0, "fixed-vararg-width-65")
expectNoMatch("fixed-vararg-width-65", (projectResult(width65Call, 64, 64, "fixed-vararg-width-65", false)))

local fixedParameterResults64: { Record } = {}
for index = 1, 64 do
	table.insert(fixedParameterResults64, if index == 64
		then Support.globalExpression("authenticated_target", "fixed-parameter-tail-width-64-selected")
		else InvocationSupport.differentTarget(`fixed-parameter-tail-width-64-ignored-{index}`))
end
local _, fixedParameterResultCall64 = Support.invocationFromBody({
	returnStatement(fixedParameterResults64, "fixed-parameter-tail-width-64-producer"),
}, "fixed-parameter-tail-width-64-producer", nil, nil)
expectMatch("fixed-parameter-tail-width-64", (fixedParameterCall({
	fixedParameterResultCall64,
}, 64, 64, "fixed-parameter-tail-width-64", false)))

local fixedParameterResults65 = table.clone(fixedParameterResults64)
table.insert(
	fixedParameterResults65,
	Support.globalExpression("authenticated_target", "fixed-parameter-tail-width-65-selected")
)
local _, fixedParameterResultCall65 = Support.invocationFromBody({
	returnStatement(fixedParameterResults65, "fixed-parameter-tail-width-65-producer"),
}, "fixed-parameter-tail-width-65-producer", nil, nil)
expectNoMatch("fixed-parameter-tail-width-65", (fixedParameterCall({
	fixedParameterResultCall65,
}, 65, 65, "fixed-parameter-tail-width-65", false)))

expectMatch("forwarded-vararg-width-64", (forwardedParameterCall(
	arguments64,
	0,
	{ varargs("forwarded-vararg-width-64") },
	64,
	64,
	"forwarded-vararg-width-64",
	false
)))
expectNoMatch("forwarded-vararg-width-65", (forwardedParameterCall(
	arguments65,
	0,
	{ varargs("forwarded-vararg-width-65") },
	65,
	65,
	"forwarded-vararg-width-65",
	false
)))

expectMatch("fixed-vararg-depth-64", nestedVarargCall(64, "fixed-vararg-depth-64"))
expectNoMatch("fixed-vararg-depth-65", nestedVarargCall(65, "fixed-vararg-depth-65"))

print("fixed invocation adjustment tests passed")
