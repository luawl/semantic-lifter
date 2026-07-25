--!strict

local TargetOriginMatcher = require("./target_origin_matcher")
local Support = require("./temporal_test_support")
local InvocationSupport = require("./temporal_invocation_test_support")
assert(require("./local_function_return_test"))
assert(require("./conditional_factory_return_test"))

type Record = Support.Record

local assignmentValue = Support.assignmentValue
local block = Support.block
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

local function returnStatement(values: any, prefix: string): Record
	return { type = "AstStatReturn", location = prefix .. "-return", list = values }
end

local function directFactory(value: Record, prefix: string, wrapped: boolean): Record
	local returned = if wrapped then wrappedExpression(value, prefix .. "-returned") else value
	local _, call = invocationFromBody(
		{ returnStatement({ returned }, prefix) },
		prefix,
		if wrapped then wrappers else nil,
		nil
	)
	return if wrapped then wrappedExpression(call, prefix .. "-call") else call
end

local function parameterFactory(
	arguments: { Record },
	parameterCount: number,
	returnIndex: number,
	prefix: string,
	wrapped: boolean
): (Record, { Record }, Record)
	assert(parameterCount >= 1 and returnIndex >= 1 and returnIndex <= parameterCount)
	local parameters: { Record } = {}
	for index = 1, parameterCount do
		table.insert(parameters, declaration(`{prefix}Parameter{index}`, `{prefix}-parameter-{index}`))
	end
	local returned: Record = localExpression(parameters[returnIndex], prefix .. "-returned-read")
	if wrapped then
		returned = wrappedExpression(returned, prefix .. "-returned")
	end
	local functionValue, call = invocationFromBody(
		{ returnStatement({ returned }, prefix) },
		prefix,
		if wrapped then wrappers else nil,
		arguments
	)
	functionValue.args = parameters
	return if wrapped then wrappedExpression(call, prefix .. "-call") else call, parameters, functionValue
end

local function aliasReturnFactory(
	initial: Record,
	depth: number,
	prefix: string,
	wrapped: boolean
): (Record, { Record }, Record, Record)
	assert(depth >= 1)
	local aliases: { Record } = {}
	local body: { Record } = {}
	local value = initial
	for index = 1, depth do
		local alias = declaration(`{prefix}Alias{index}`, `{prefix}-alias-{index}`)
		table.insert(aliases, alias)
		table.insert(body, {
			type = "AstStatLocal",
			location = `{prefix}-alias-statement-{index}`,
			vars = { alias },
			values = { if wrapped then wrappedExpression(value, `{prefix}-alias-value-{index}`) else value },
		})
		value = localExpression(alias, `{prefix}-alias-read-{index}`)
	end
	table.insert(body, returnStatement({
		if wrapped then wrappedExpression(value, prefix .. "-returned") else value,
	}, prefix))
	local functionValue, rawCall = invocationFromBody(body, prefix, if wrapped then wrappers else nil, nil)
	return if wrapped then wrappedExpression(rawCall, prefix .. "-call") else rawCall, aliases, functionValue, rawCall
end

local function assignmentSnapshotFactory(
	prefix: string,
	depth: number,
	wrapped: boolean
): (Record, { Record }, Record)
	local call, aliases, functionValue = aliasReturnFactory(
		globalExpression("authenticated_target", prefix .. "-value"),
		depth,
		prefix,
		wrapped
	)
	functionValue.body.body = Support.assignmentBackedSnapshots(functionValue.body.body, prefix)
	return call, aliases, functionValue
end

local function projectedAliasCall(
	returnValues: { Record },
	targetOrdinal: number,
	targetWidth: number,
	prefix: string,
	aliasDepth: number?
): (Record, Record, Record)
	local returnedFunction, sourceCall = invocationFromBody({
		returnStatement(returnValues, prefix .. "-source"),
	}, prefix .. "-source", nil, nil)
	local call, _, functionValue = aliasReturnFactory(sourceCall, aliasDepth or 1, prefix, false)
	Support.setSingleValueTargetOrdinal(functionValue.body.body[1], targetOrdinal, targetWidth, prefix)
	return call, returnedFunction, functionValue
end

local function useReturnedLocalAsCallee(functionValue: Record, prefix: string)
	local returnList = functionValue.body.body[#functionValue.body.body].list
	local returned = returnList[1]
	assert(type(returned) == "table" and returned.type == "AstExprLocal")
	returnList[1] = callExpression(returned["local"], prefix .. "-projected-callee")

end

local function projectedCalleeCall(
	selectedValue: Record,
	targetOrdinal: number,
	targetWidth: number,
	prefix: string,
	aliasDepth: number?
): (Record, Record)
	local values: { Record } = {}
	for index = 1, targetWidth do
		table.insert(values, if index == targetOrdinal then selectedValue else differentTarget(`{prefix}-value-{index}`))
	end
	local call, _, functionValue = projectedAliasCall(values, targetOrdinal, targetWidth, prefix, aliasDepth)
	useReturnedLocalAsCallee(functionValue, prefix)
	return call, functionValue
end

local function authenticatedCallable(prefix: string): Record
	local functionValue, _ = invocationFromBody({
		returnStatement({ globalExpression("authenticated_target", prefix .. "-value") }, prefix),
	}, prefix, nil, nil)
	return functionValue
end

local function nestedCallableResult(depth: number, prefix: string): Record
	assert(depth >= 1)
	local value = authenticatedCallable(prefix .. "-leaf")
	for index = 2, depth do
		local _, call = invocationFromBody({
			returnStatement({ value }, `{prefix}-level-{index}`),
		}, `{prefix}-level-{index}`, nil, nil)
		value = call
	end
	return value
end

local function projectedReturnTailCall(
	selectedValue: Record,
	nestedOrdinal: number,
	leadingCount: number,
	prefix: string,
	aliasDepth: number?
): (Record, Record, Record)
	assert(nestedOrdinal >= 1 and leadingCount >= 0)
	local nestedValues: { Record } = {}
	for index = 1, nestedOrdinal do
		table.insert(nestedValues, if index == nestedOrdinal
			then selectedValue
			else differentTarget(`{prefix}-nested-value-{index}`))
	end
	local _, nestedCall = invocationFromBody({
		returnStatement(nestedValues, prefix .. "-nested"),
	}, prefix .. "-nested", nil, nil)
	local outerValues: { Record } = {}
	for index = 1, leadingCount do
		table.insert(outerValues, differentTarget(`{prefix}-leading-value-{index}`))
	end
	table.insert(outerValues, nestedCall)
	local targetOrdinal = leadingCount + nestedOrdinal
	local call, sourceFunction, functionValue = projectedAliasCall(
		outerValues,
		targetOrdinal,
		targetOrdinal,
		prefix,
		aliasDepth
	)
	return call, functionValue, sourceFunction
end

local function projectionValues(width: number, selected: number, prefix: string): { Record }
	local values: { Record } = {}
	for index = 1, width do
		table.insert(values, if index == selected
			then globalExpression("authenticated_target", `{prefix}-value-{index}`)
			else differentTarget(`{prefix}-value-{index}`))
	end
	return values
end

local function targetDocument(prefix: string, value: Record, prelude: { Record }?): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local body: { Record } = {}
	if prelude ~= nil then
		for _, statement in prelude do
			table.insert(body, statement)
		end
	end
	table.insert(body, localStatement(target, prefix .. "-target-declaration"))
	table.insert(body, assignmentValue(target, prefix .. "-current", value))
	table.insert(body, callStatement(call, prefix .. "-call-statement"))
	table.insert(body, assignmentValue(target, prefix .. "-future-write", differentTarget(prefix .. "-future-value")))
	return document(body), call, target
end

local function expectProof(prefix: string, value: Record, origin: Record, prelude: { Record }?)
	local fixture, call, target = targetDocument(prefix, value, prelude)
	local proof = verifyOrigin(fixture, call, target, origin)
	assert(proof.definition_count == 1, `{prefix} direct return produced a definition set`)
	assert(proof.definition_location == prefix .. "-current", `{prefix} direct return lost its call-result write`)
end

local function expectOriginFailure(prefix: string, value: Record, prelude: { Record }?)
	local fixture, call, target = targetDocument(prefix, value, prelude)
	expectFailure(function()
		verifyOrigin(fixture, call, target, authenticatedOrigin)
	end, "temporal target definition " .. target.location)
end

local function expectMatcherFailure(value: Record)
	assert(not TargetOriginMatcher.matches(value, authenticatedOrigin, function(_expression: Record, _origin: Record): boolean
		return false
	end))
end

expectProof(
	"direct-return-environment",
	directFactory(globalExpression("authenticated_target", "direct-return-environment-value"), "direct-return-environment-factory", false),
	authenticatedOrigin,
	nil
)

expectProof(
	"direct-return-wrapped",
	directFactory(globalExpression("authenticated_target", "direct-return-wrapped-value"), "direct-return-wrapped-factory", true),
	authenticatedOrigin,
	nil
)

local source = declaration("directReturnSource", "direct-return-source")
expectProof(
	"direct-return-local",
	directFactory(localExpression(source, "direct-return-local-value"), "direct-return-local-factory", false),
	{ kind = "local_value", declaration = source },
	{ localStatement(source, "direct-return-source-declaration", differentTarget("direct-return-source-value")) }
)

local tableValue: Record = {
	type = "AstExprIndexName",
	location = "direct-return-table-value",
	expr = globalExpression("registry", "direct-return-table-root"),
	index = "handler",
}
expectProof("direct-return-table", directFactory(tableValue, "direct-return-table-factory", false), {
	kind = "table_get",
	table_origin = { kind = "environment", name = "registry" },
	key_origin = { kind = "constant_string", value = "handler" },
}, nil)

local pathValue: Record = {
	type = "AstExprIndexName",
	location = "direct-return-path-handler",
	expr = {
		type = "AstExprIndexName",
		location = "direct-return-path-layer",
		expr = globalExpression("registry", "direct-return-path-root"),
		index = "layer",
	},
	index = "handler",
}
expectProof("direct-return-path", directFactory(pathValue, "direct-return-path-factory", false), {
	kind = "access_path",
	root_origin = { kind = "environment", name = "registry" },
	key_origins = {
		{ kind = "constant_string", value = "layer" },
		{ kind = "constant_string", value = "handler" },
	},
}, nil)

expectProof(
	"parameter-return-first",
	parameterFactory({
		globalExpression("authenticated_target", "parameter-return-first-value"),
		differentTarget("parameter-return-first-other"),
	}, 2, 1, "parameter-return-first-factory", false),
	authenticatedOrigin,
	nil
)

expectProof(
	"parameter-return-middle",
	parameterFactory({
		differentTarget("parameter-return-middle-before"),
		globalExpression("authenticated_target", "parameter-return-middle-value"),
		differentTarget("parameter-return-middle-after"),
	}, 3, 2, "parameter-return-middle-factory", false),
	authenticatedOrigin,
	nil
)

local extraArgumentCall: Record = {
	type = "AstExprCall",
	location = "parameter-return-final-extra-call",
	func = globalExpression("observe_extra_argument", "parameter-return-final-extra-callee"),
	args = {},
	self = false,
}
expectProof(
	"parameter-return-final-extra",
	parameterFactory({
		differentTarget("parameter-return-final-before"),
		globalExpression("authenticated_target", "parameter-return-final-value"),
		extraArgumentCall,
	}, 2, 2, "parameter-return-final-extra-factory", false),
	authenticatedOrigin,
	nil
)

expectProof(
	"parameter-return-wrapped",
	parameterFactory({
		wrappedExpression(
			globalExpression("authenticated_target", "parameter-return-wrapped-value"),
			"parameter-return-wrapped-argument"
		),
	}, 1, 1, "parameter-return-wrapped-factory", true),
	authenticatedOrigin,
	nil
)

local nestedParameterReturn = parameterFactory({
	globalExpression("authenticated_target", "parameter-return-nested-value"),
}, 1, 1, "parameter-return-nested-inner", true)
expectProof(
	"parameter-return-nested",
	parameterFactory({ nestedParameterReturn }, 1, 1, "parameter-return-nested-outer", false),
	authenticatedOrigin,
	nil
)

local function nestedParameterFactory(depth: number, prefix: string): Record
	local value = globalExpression("authenticated_target", prefix .. "-value")
	for index = 1, depth do
		value = parameterFactory({ value }, 1, 1, `{prefix}-{index}`, index % 2 == 0)
	end
	return value
end

expectProof(
	"parameter-return-depth-64",
	nestedParameterFactory(TargetOriginMatcher.maxDirectReturnDepth, "parameter-return-depth-64-factory"),
	authenticatedOrigin,
	nil
)
expectOriginFailure(
	"parameter-return-depth-65",
	nestedParameterFactory(TargetOriginMatcher.maxDirectReturnDepth + 1, "parameter-return-depth-65-factory"),
	nil
)

local parameterSource = declaration("parameterReturnSource", "parameter-return-source")
expectProof(
	"parameter-return-local",
	parameterFactory({
		localExpression(parameterSource, "parameter-return-local-value"),
	}, 1, 1, "parameter-return-local-factory", false),
	{ kind = "local_value", declaration = parameterSource },
	{ localStatement(parameterSource, "parameter-return-source-declaration", differentTarget("parameter-return-source-value")) }
)

local parameterLocalTarget = declaration("parameterReturnLocalTarget", "parameter-return-local-target")
local parameterLocalOther = declaration("parameterReturnLocalOther", "parameter-return-local-other")
local parameterLocalCall = callExpression(parameterLocalTarget, "parameter-return-local-target-read")
local parameterLocalProof = verifyOrigin(document({
	{
		type = "AstStatLocal",
		location = "parameter-return-local-target-current",
		vars = { parameterLocalOther, parameterLocalTarget },
		values = {
			differentTarget("parameter-return-local-target-other-value"),
			parameterFactory({
				globalExpression("authenticated_target", "parameter-return-local-target-value"),
			}, 1, 1, "parameter-return-local-target-factory", false),
		},
	},
	callStatement(parameterLocalCall, "parameter-return-local-target-call-statement"),
}), parameterLocalCall, parameterLocalTarget, authenticatedOrigin)
assert(parameterLocalProof.definition_location == "parameter-return-local-target-current")

expectProof(
	"alias-return-environment",
	aliasReturnFactory(
		globalExpression("authenticated_target", "alias-return-environment-value"),
		1,
		"alias-return-environment-factory",
		false
	),
	authenticatedOrigin,
	nil
)

expectProof(
	"alias-return-wrapped",
	aliasReturnFactory(
		globalExpression("authenticated_target", "alias-return-wrapped-value"),
		3,
		"alias-return-wrapped-factory",
		true
	),
	authenticatedOrigin,
	nil
)

expectProof(
	"alias-return-table",
	aliasReturnFactory(tableValue, 2, "alias-return-table-factory", false),
	{
		kind = "table_get",
		table_origin = { kind = "environment", name = "registry" },
		key_origin = { kind = "constant_string", value = "handler" },
	},
	nil
)

local aliasSource = declaration("aliasReturnSource", "alias-return-source")
expectProof(
	"alias-return-local",
	aliasReturnFactory(
		localExpression(aliasSource, "alias-return-local-value"),
		2,
		"alias-return-local-factory",
		false
	),
	{ kind = "local_value", declaration = aliasSource },
	{ localStatement(aliasSource, "alias-return-source-declaration", differentTarget("alias-return-source-value")) }
)

local aliasParameter = declaration("aliasReturnParameter", "alias-return-parameter")
local aliasParameterCall, _, aliasParameterFunction, aliasParameterRawCall = aliasReturnFactory(
	localExpression(aliasParameter, "alias-return-parameter-read"),
	3,
	"alias-return-parameter-factory",
	true
)
aliasParameterFunction.args = { aliasParameter }
aliasParameterRawCall.args = {
	globalExpression("authenticated_target", "alias-return-parameter-argument"),
}
expectProof("alias-return-parameter", aliasParameterCall, authenticatedOrigin, nil)

expectProof(
	"alias-return-nested",
	aliasReturnFactory(
		directFactory(
			globalExpression("authenticated_target", "alias-return-nested-value"),
			"alias-return-nested-inner",
			true
		),
		2,
		"alias-return-nested-outer",
		false
	),
	authenticatedOrigin,
	nil
)

expectProof(
	"alias-return-depth-64",
	aliasReturnFactory(
		globalExpression("authenticated_target", "alias-return-depth-64-value"),
		64,
		"alias-return-depth-64-factory",
		false
	),
	authenticatedOrigin,
	nil
)
expectOriginFailure(
	"alias-return-depth-65",
	aliasReturnFactory(
		globalExpression("authenticated_target", "alias-return-depth-65-value"),
		65,
		"alias-return-depth-65-factory",
		false
	),
	nil
)

local skippedAliasCall, skippedAliases, skippedAliasFunction = aliasReturnFactory(
	globalExpression("authenticated_target", "alias-return-skipped-value"),
	2,
	"alias-return-skipped",
	false
)
skippedAliasFunction.body.body[2].values = {
	localExpression(skippedAliases[1], "alias-return-skipped-reused-read"),
}
skippedAliasFunction.body.body[3].list = {
	localExpression(skippedAliases[1], "alias-return-skipped-return"),
}
expectOriginFailure("alias-return-skipped", skippedAliasCall, nil)

local unrelatedAliasCall, unrelatedAliases, unrelatedAliasFunction = aliasReturnFactory(
	globalExpression("authenticated_target", "alias-return-unrelated-value"),
	2,
	"alias-return-unrelated",
	false
)
unrelatedAliasFunction.body.body[2].values = { differentTarget("alias-return-unrelated-snapshot") }
unrelatedAliasFunction.body.body[3].list = {
	localExpression(unrelatedAliases[1], "alias-return-unrelated-return"),
}
expectOriginFailure("alias-return-unrelated", unrelatedAliasCall, nil)

local duplicateAliasCall, duplicateAliases, duplicateAliasFunction = aliasReturnFactory(
	globalExpression("authenticated_target", "alias-return-duplicate-value"),
	2,
	"alias-return-duplicate",
	false
)
duplicateAliasFunction.body.body[2].vars = { duplicateAliases[1] }
expectMatcherFailure(duplicateAliasCall)

local multiAliasCall, multiAliases, multiAliasFunction = aliasReturnFactory(
	globalExpression("authenticated_target", "alias-return-multiple-value"),
	1,
	"alias-return-multiple",
	false
)
multiAliasFunction.body.body[1].vars = {
	multiAliases[1],
	declaration("aliasReturnMultipleSecond", "alias-return-multiple-second"),
}
expectProof("alias-return-multiple", multiAliasCall, authenticatedOrigin, nil)

local multiValueAliasCall, _, multiValueAliasFunction = aliasReturnFactory(
	globalExpression("authenticated_target", "alias-return-multiple-values-first"),
	1,
	"alias-return-multiple-values",
	false
)
local multiValueTrailing = extraArgumentCall
table.insert(multiValueAliasFunction.body.body[1].values, multiValueTrailing)
expectProof("alias-return-multiple-values", multiValueAliasCall, authenticatedOrigin, nil)
assert(multiValueAliasFunction.body.body[1].values[2] == multiValueTrailing)

local ordinalAliasCall, ordinalAliases, ordinalAliasFunction = aliasReturnFactory(
	differentTarget("alias-return-ordinal-initial"),
	1,
	"alias-return-ordinal",
	false
)
ordinalAliasFunction.body.body[1].vars = {
	declaration("aliasReturnOrdinalIgnored", "alias-return-ordinal-ignored"),
	ordinalAliases[1],
}
ordinalAliasFunction.body.body[1].values = {
	differentTarget("alias-return-ordinal-ignored-value"),
	globalExpression("authenticated_target", "alias-return-ordinal-value"),
}
expectProof("alias-return-ordinal", ordinalAliasCall, authenticatedOrigin, nil)
ordinalAliasFunction.body.body = Support.assignmentBackedSnapshots(
	ordinalAliasFunction.body.body,
	"alias-return-assignment-ordinal"
)
expectProof("alias-return-assignment-ordinal", ordinalAliasCall, authenticatedOrigin, nil)
table.remove(ordinalAliasFunction.body.body[2].vars, 1)
table.remove(ordinalAliasFunction.body.body[2].values, 1)
expectMatcherFailure(ordinalAliasCall)

local laterAliasCall, laterAliases, laterAliasFunction = aliasReturnFactory(
	globalExpression("authenticated_target", "alias-return-later-target-value"),
	1,
	"alias-return-later-target",
	false
)
local laterAlias = declaration("aliasReturnLaterTarget", "alias-return-later-target-extra")
laterAliasFunction.body.body[1].vars = { laterAliases[1], laterAlias }
laterAliasFunction.body.body[2].list = {
	localExpression(laterAlias, "alias-return-later-target-read"),
}
expectMatcherFailure(laterAliasCall)
laterAliasFunction.body.body = Support.assignmentBackedSnapshots(
	laterAliasFunction.body.body,
	"alias-return-assignment-later-target"
)
expectMatcherFailure(laterAliasCall)

local projectionTrailing: Record = {
	type = "AstExprCall",
	location = "alias-return-projection-trailing-call",
	func = globalExpression("observe", "alias-return-projection-trailing-callee"),
	args = {},
	self = false,
}
local projectionCall, projectionFunction = projectedAliasCall({
	projectionTrailing,
	globalExpression("authenticated_target", "alias-return-projection-selected"),
}, 2, 2, "alias-return-projection", 2)
expectProof("alias-return-projection", projectionCall, authenticatedOrigin, nil)
assert(projectionFunction.body.body[1].list[1] == projectionTrailing)

local projection64Call = projectedAliasCall(
	projectionValues(64, 64, "alias-return-projection-64"),
	64,
	64,
	"alias-return-projection-64"
)
expectProof("alias-return-projection-64", projection64Call, authenticatedOrigin, nil)
expectMatcherFailure((projectedAliasCall(
	projectionValues(65, 64, "alias-return-projection-return-65"),
	64,
	64,
	"alias-return-projection-return-65"
)))
expectMatcherFailure((projectedAliasCall(
	projectionValues(2, 2, "alias-return-projection-missing"),
	3,
	3,
	"alias-return-projection-missing"
)))
expectMatcherFailure((projectedAliasCall(
	projectionValues(2, 1, "alias-return-projection-wrong"),
	2,
	2,
	"alias-return-projection-wrong"
)))
local nestedProjectionSource = projectedAliasCall(
	projectionValues(2, 2, "alias-return-projection-nested-source"),
	1,
	1,
	"alias-return-projection-nested-source"
)
expectMatcherFailure((projectedAliasCall(
	{ nestedProjectionSource },
	2,
	2,
	"alias-return-projection-nested"
)))
expectMatcherFailure((projectedAliasCall(
	{ { type = "AstExprVarargs", location = "alias-return-projection-vararg-value" } },
	2,
	2,
	"alias-return-projection-vararg"
)))
for _, wrapper in wrappers do
	local prefix = "alias-return-projection-wrapped-" .. wrapper
	local call, _, functionValue = projectedAliasCall(projectionValues(2, 2, prefix), 2, 2, prefix)
	local statement = functionValue.body.body[1]
	statement.values[1] = { type = wrapper, location = prefix .. "-wrapper", expr = statement.values[1] }
	expectMatcherFailure(call)
end

local returnTailProjectionCall = projectedReturnTailCall(
	globalExpression("authenticated_target", "alias-return-tail-projection-selected"),
	2,
	1,
	"alias-return-tail-projection",
	2
)
expectProof("alias-return-tail-projection", returnTailProjectionCall, authenticatedOrigin, nil)

local returnTailAssignmentCall, returnTailAssignmentFunction = projectedReturnTailCall(
	globalExpression("authenticated_target", "alias-return-tail-assignment-selected"),
	2,
	1,
	"alias-return-tail-assignment",
	2
)
returnTailAssignmentFunction.body.body = Support.assignmentBackedSnapshots(
	returnTailAssignmentFunction.body.body,
	"alias-return-tail-assignment"
)
expectProof("alias-return-tail-assignment", returnTailAssignmentCall, authenticatedOrigin, nil)

local returnTailCallableCall, returnTailCallableFunction = projectedReturnTailCall(
	authenticatedCallable("alias-return-tail-callable-selected"),
	2,
	1,
	"alias-return-tail-callable",
	2
)
useReturnedLocalAsCallee(returnTailCallableFunction, "alias-return-tail-callable")
expectProof("alias-return-tail-callable", returnTailCallableCall, authenticatedOrigin, nil)

local returnTail64 = projectedReturnTailCall(
	globalExpression("authenticated_target", "alias-return-tail-64-selected"),
	64,
	0,
	"alias-return-tail-64",
	nil
)
expectProof("alias-return-tail-64", returnTail64, authenticatedOrigin, nil)
expectMatcherFailure((projectedReturnTailCall(
	globalExpression("authenticated_target", "alias-return-tail-65-selected"),
	65,
	0,
	"alias-return-tail-65",
	nil
)))

local returnTailWrongCall, _, returnTailWrongSource = projectedReturnTailCall(
	differentTarget("alias-return-tail-wrong-selected"),
	2,
	1,
	"alias-return-tail-wrong",
	nil
)
local returnTailWrongNestedCall = returnTailWrongSource.body.body[1].list[2]
returnTailWrongNestedCall.func.body.body[1].list[1] = globalExpression(
	"authenticated_target",
	"alias-return-tail-wrong-ignored"
)
expectMatcherFailure(returnTailWrongCall)

local returnTailWrappedCall, _, returnTailWrappedSource = projectedReturnTailCall(
	globalExpression("authenticated_target", "alias-return-tail-wrapped-selected"),
	2,
	1,
	"alias-return-tail-wrapped",
	nil
)
local returnTailWrappedList = returnTailWrappedSource.body.body[1].list
returnTailWrappedList[2] = wrappedExpression(returnTailWrappedList[2], "alias-return-tail-wrapped")
expectMatcherFailure(returnTailWrappedCall)

local returnTailMethodCall, _, returnTailMethodSource = projectedReturnTailCall(
	globalExpression("authenticated_target", "alias-return-tail-method-selected"),
	2,
	1,
	"alias-return-tail-method",
	nil
)
returnTailMethodSource.body.body[1].list[2].self = true
expectMatcherFailure(returnTailMethodCall)

expectMatcherFailure((projectedAliasCall({
	differentTarget("alias-return-tail-vararg-leading"),
	{ type = "AstExprVarargs", location = "alias-return-tail-vararg-value" },
}, 3, 3, "alias-return-tail-vararg", nil)))

local projectedCallableCall = projectedCalleeCall(
	authenticatedCallable("alias-return-projected-callee"),
	2,
	2,
	"alias-return-projected-callee",
	2
)
expectProof("alias-return-projected-callee", projectedCallableCall, authenticatedOrigin, nil)

local projectedCallableAssignmentCall, projectedCallableAssignmentFunction = projectedCalleeCall(
	authenticatedCallable("alias-return-projected-callee-assignment"),
	2,
	2,
	"alias-return-projected-callee-assignment",
	2
)
projectedCallableAssignmentFunction.body.body = Support.assignmentBackedSnapshots(
	projectedCallableAssignmentFunction.body.body,
	"alias-return-projected-callee-assignment"
)
expectProof("alias-return-projected-callee-assignment", projectedCallableAssignmentCall, authenticatedOrigin, nil)

local projectedCallable64 = projectedCalleeCall(
	authenticatedCallable("alias-return-projected-callee-64"),
	64,
	64,
	"alias-return-projected-callee-64",
	64
)
expectProof("alias-return-projected-callee-64", projectedCallable64, authenticatedOrigin, nil)
expectMatcherFailure((projectedCalleeCall(
	authenticatedCallable("alias-return-projected-callee-depth-65"),
	2,
	2,
	"alias-return-projected-callee-depth-65",
	65
)))
expectMatcherFailure((projectedCalleeCall(
	globalExpression("authenticated_target", "alias-return-projected-non-callee-value"),
	2,
	2,
	"alias-return-projected-non-callee",
	nil
)))
local projectedWrongOrdinalCall, _, projectedWrongOrdinalFunction = projectedAliasCall({
	authenticatedCallable("alias-return-projected-callee-wrong-ordinal-ignored"),
	differentTarget("alias-return-projected-callee-wrong-ordinal-selected"),
}, 2, 2, "alias-return-projected-callee-wrong-ordinal", nil)
useReturnedLocalAsCallee(projectedWrongOrdinalFunction, "alias-return-projected-callee-wrong-ordinal")
expectMatcherFailure(projectedWrongOrdinalCall)

local projectedCallableDepth64 = projectedCalleeCall(
	nestedCallableResult(64, "alias-return-projected-callee-return-depth-64"),
	2,
	2,
	"alias-return-projected-callee-return-depth-64",
	nil
)
expectProof("alias-return-projected-callee-return-depth-64", projectedCallableDepth64, authenticatedOrigin, nil)
expectMatcherFailure((projectedCalleeCall(
	nestedCallableResult(65, "alias-return-projected-callee-return-depth-65"),
	2,
	2,
	"alias-return-projected-callee-return-depth-65",
	nil
)))

local recursiveProjectedFunction, recursiveProjectedCall = invocationFromBody({
	returnStatement({ differentTarget("alias-return-projected-callee-cycle-placeholder") }, "alias-return-projected-callee-cycle"),
}, "alias-return-projected-callee-cycle", nil, nil)
recursiveProjectedFunction.body.body[1].list[1] = recursiveProjectedCall
expectMatcherFailure((projectedCalleeCall(
	recursiveProjectedCall,
	2,
	2,
	"alias-return-projected-callee-cycle",
	nil
)))

local function multiTargetAliasReturn(targetCount: number, prefix: string): Record
	local call, aliases, functionValue = aliasReturnFactory(
		globalExpression("authenticated_target", prefix .. "-value"),
		1,
		prefix,
		false
	)
	local targets: { Record } = { aliases[1] }
	for index = 2, targetCount do
		table.insert(targets, declaration(`{prefix}Target{index}`, `{prefix}-target-{index}`))
	end
	functionValue.body.body[1].vars = targets
	return call
end

local targets64Call = multiTargetAliasReturn(64, "alias-return-targets-64")
expectProof("alias-return-targets-64", targets64Call, authenticatedOrigin, nil)
expectMatcherFailure(multiTargetAliasReturn(65, "alias-return-targets-65"))

local assignmentSnapshotCall = assignmentSnapshotFactory("alias-return-assignment-snapshot", 2, true)
expectProof("alias-return-assignment-snapshot", assignmentSnapshotCall, authenticatedOrigin, nil)

local replacementSnapshotCall, replacementSnapshotAliases, replacementSnapshotFunction = assignmentSnapshotFactory(
	"alias-return-assignment-replacement",
	1,
	false
)
table.insert(replacementSnapshotFunction.body.body, 3, assignmentValue(
	replacementSnapshotAliases[1],
	"alias-return-assignment-replacement-second-write",
	differentTarget("alias-return-assignment-replacement-second-value")
))
expectMatcherFailure(replacementSnapshotCall)

local selfAssignmentCall, selfAssignmentAliases, selfAssignmentFunction = assignmentSnapshotFactory(
	"alias-return-self-assignment",
	1,
	false
)
selfAssignmentFunction.body.body[2].values = {
	localExpression(selfAssignmentAliases[1], "alias-return-self-assignment-read"),
}
expectMatcherFailure(selfAssignmentCall)

local multiAssignmentCall, multiAssignmentAliases, multiAssignmentFunction = assignmentSnapshotFactory(
	"alias-return-multi-assignment",
	1,
	false
)
table.insert(multiAssignmentFunction.body.body[2].vars, localExpression(
	multiAssignmentAliases[1],
	"alias-return-multi-assignment-duplicate-target"
))
table.insert(multiAssignmentFunction.body.body[2].values, differentTarget("alias-return-multi-assignment-duplicate-value"))
expectMatcherFailure(multiAssignmentCall)

local indexedAssignmentCall, _, indexedAssignmentFunction = assignmentSnapshotFactory(
	"alias-return-indexed-assignment",
	1,
	false
)
indexedAssignmentFunction.body.body[2].vars = { {
	type = "AstExprIndexName",
	location = "alias-return-indexed-assignment-target",
	expr = globalExpression("registry", "alias-return-indexed-assignment-root"),
	index = "handler",
} }
expectMatcherFailure(indexedAssignmentCall)

local assignmentAliasCall, assignmentAliases, assignmentAliasFunction = aliasReturnFactory(
	globalExpression("authenticated_target", "alias-return-assignment-value"),
	1,
	"alias-return-assignment",
	false
)
assignmentAliasFunction.body.body[1] = assignmentValue(
	assignmentAliases[1],
	"alias-return-assignment-write",
	globalExpression("authenticated_target", "alias-return-assignment-write-value")
)
expectMatcherFailure(assignmentAliasCall)

local effectAliasCall, _, effectAliasFunction = aliasReturnFactory(
	globalExpression("authenticated_target", "alias-return-effect-value"),
	2,
	"alias-return-effect",
	false
)
table.insert(effectAliasFunction.body.body, 2, {
	type = "AstStatExpr",
	location = "alias-return-effect-statement",
	expr = extraArgumentCall,
})
expectMatcherFailure(effectAliasCall)

local selfAlias = declaration("aliasReturnSelf", "alias-return-self-local")
local selfAliasCall, _, selfAliasFunction = aliasReturnFactory(
	localExpression(selfAlias, "alias-return-self-read"),
	1,
	"alias-return-self",
	false
)
selfAliasFunction.body.body[1].vars = { selfAlias }
expectMatcherFailure(selfAliasCall)

local forwardAliasCall, forwardAliases, forwardAliasFunction = aliasReturnFactory(
	differentTarget("alias-return-forward-initial"),
	2,
	"alias-return-forward",
	false
)
forwardAliasFunction.body.body[1].values = {
	localExpression(forwardAliases[2], "alias-return-forward-read"),
}
expectMatcherFailure(forwardAliasCall)

local malformedAliasCall, _, malformedAliasFunction = aliasReturnFactory(
	globalExpression("authenticated_target", "alias-return-malformed-value"),
	1,
	"alias-return-malformed",
	false
)
malformedAliasFunction.body.body[1].vars = {
	{ type = "AstExprGlobal", location = "alias-return-malformed-target", global = "alias" },
}
expectMatcherFailure(malformedAliasCall)

local keyedAliasCall, _, keyedAliasFunction = aliasReturnFactory(
	globalExpression("authenticated_target", "alias-return-keyed-value"),
	1,
	"alias-return-keyed",
	false
)
keyedAliasFunction.body.body[1].values = {
	globalExpression("authenticated_target", "alias-return-keyed-selected"),
	extra = differentTarget("alias-return-keyed-extra"),
} :: any
expectMatcherFailure(keyedAliasCall)

local localOrdinalTarget = declaration("directReturnLocalOrdinalTarget", "direct-return-local-ordinal-target")
local localOrdinalCall = callExpression(localOrdinalTarget, "direct-return-local-ordinal-read")
local localOrdinalOther1 = declaration("directReturnLocalOrdinalOther1", "direct-return-local-ordinal-other-1")
local localOrdinalOther2 = declaration("directReturnLocalOrdinalOther2", "direct-return-local-ordinal-other-2")
local localOrdinalProof = verifyOrigin(document({
	{
		type = "AstStatLocal",
		location = "direct-return-local-ordinal-current",
		vars = { localOrdinalOther1, localOrdinalTarget, localOrdinalOther2 },
		values = {
			differentTarget("direct-return-local-ordinal-other-value"),
			directFactory(
				globalExpression("authenticated_target", "direct-return-local-ordinal-value"),
				"direct-return-local-ordinal-factory",
				false
			),
		},
	},
	callStatement(localOrdinalCall, "direct-return-local-ordinal-call-statement"),
}), localOrdinalCall, localOrdinalTarget, authenticatedOrigin)
assert(localOrdinalProof.definition_location == "direct-return-local-ordinal-current")

local assignmentOrdinalTarget = declaration("directReturnAssignmentOrdinalTarget", "direct-return-assignment-ordinal-target")
local assignmentOrdinalOther = declaration("directReturnAssignmentOrdinalOther", "direct-return-assignment-ordinal-other")
local assignmentOrdinalCall = callExpression(assignmentOrdinalTarget, "direct-return-assignment-ordinal-read")
local assignmentOrdinalProof = verifyOrigin(document({
	localStatement(assignmentOrdinalTarget, "direct-return-assignment-ordinal-target-declaration"),
	localStatement(assignmentOrdinalOther, "direct-return-assignment-ordinal-other-declaration"),
	{
		type = "AstStatAssign",
		location = "direct-return-assignment-ordinal-current",
		vars = {
			localExpression(assignmentOrdinalTarget, "direct-return-assignment-ordinal-target-write"),
			localExpression(assignmentOrdinalOther, "direct-return-assignment-ordinal-other-write"),
		},
		values = {
			directFactory(
				globalExpression("authenticated_target", "direct-return-assignment-ordinal-value"),
				"direct-return-assignment-ordinal-factory",
				false
			),
			differentTarget("direct-return-assignment-ordinal-other-value"),
			differentTarget("direct-return-assignment-ordinal-extra-value"),
		},
	},
	callStatement(assignmentOrdinalCall, "direct-return-assignment-ordinal-call-statement"),
}), assignmentOrdinalCall, assignmentOrdinalTarget, authenticatedOrigin)
assert(assignmentOrdinalProof.definition_location == "direct-return-assignment-ordinal-current")

local function nestedFactory(depth: number, prefix: string): Record
	local value = globalExpression("authenticated_target", prefix .. "-value")
	for index = 1, depth do
		value = directFactory(value, `{prefix}-{index}`, index % 2 == 0)
	end
	return value
end

local missingArgumentCall = parameterFactory({
	{
		type = "AstExprCall",
		location = "parameter-return-missing-open-argument",
		func = globalExpression("open_argument", "parameter-return-missing-open-callee"),
		args = {},
		self = false,
	},
}, 2, 2, "parameter-return-missing", false)
expectOriginFailure("parameter-return-missing", missingArgumentCall, nil)

local wrongOrdinalCall = parameterFactory({
	globalExpression("authenticated_target", "parameter-return-wrong-ordinal-authenticated"),
	differentTarget("parameter-return-wrong-ordinal-selected"),
}, 2, 2, "parameter-return-wrong-ordinal", false)
expectOriginFailure("parameter-return-wrong-ordinal", wrongOrdinalCall, nil)

local duplicateParameterCall, duplicateParameters, duplicateParameterFunction = parameterFactory({
	differentTarget("parameter-return-duplicate-first"),
	globalExpression("authenticated_target", "parameter-return-duplicate-second"),
}, 2, 2, "parameter-return-duplicate", false)
duplicateParameterFunction.args = { duplicateParameters[2], duplicateParameters[2] }
expectOriginFailure("parameter-return-duplicate", duplicateParameterCall, nil)

local malformedParameterCall, malformedParameters, malformedParameterFunction = parameterFactory({
	globalExpression("authenticated_target", "parameter-return-malformed-value"),
}, 1, 1, "parameter-return-malformed", false)
malformedParameterFunction.args = {
	{ type = "AstExprGlobal", location = malformedParameters[1].location, global = malformedParameters[1].name },
}
expectMatcherFailure(malformedParameterCall)

local unrelatedParameterCall, _, unrelatedParameterFunction = parameterFactory({
	globalExpression("authenticated_target", "parameter-return-unrelated-value"),
}, 1, 1, "parameter-return-unrelated", false)
local unrelatedParameter = declaration("parameterReturnUnrelated", "parameter-return-unrelated-local")
unrelatedParameterFunction.body = block({
	returnStatement({ localExpression(unrelatedParameter, "parameter-return-unrelated-read") }, "parameter-return-unrelated"),
}, "parameter-return-unrelated-body")
expectOriginFailure("parameter-return-unrelated", unrelatedParameterCall, {
	localStatement(unrelatedParameter, "parameter-return-unrelated-declaration", differentTarget("parameter-return-unrelated-initial")),
})

local keyedParameterCall, _, keyedParameterFunction = parameterFactory({
	globalExpression("authenticated_target", "parameter-return-keyed-parameter-value"),
}, 1, 1, "parameter-return-keyed-parameter", false)
local keyedParameter = declaration("parameterReturnKeyed", "parameter-return-keyed-parameter-local")
keyedParameterFunction.args = { keyedParameter, extra = keyedParameter } :: any
expectMatcherFailure(keyedParameterCall)

local keyedArgumentCall = parameterFactory({
	globalExpression("authenticated_target", "parameter-return-keyed-argument-value"),
}, 1, 1, "parameter-return-keyed-argument", false)
local unwrappedKeyedArgumentCall = keyedArgumentCall
while unwrappedKeyedArgumentCall.type == "AstExprGroup"
	or unwrappedKeyedArgumentCall.type == "AstExprTypeAssertion"
	or unwrappedKeyedArgumentCall.type == "AstExprInstantiate"
do
	unwrappedKeyedArgumentCall = unwrappedKeyedArgumentCall.expr
end
unwrappedKeyedArgumentCall.args = {
	globalExpression("authenticated_target", "parameter-return-keyed-argument-selected"),
	extra = differentTarget("parameter-return-keyed-argument-extra"),
} :: any
expectMatcherFailure(keyedArgumentCall)

local cycleParameter = declaration("parameterReturnCycle", "parameter-return-cycle-parameter")
local cycleParameterFunction: Record = {
	type = "AstExprFunction",
	location = "parameter-return-cycle-function",
	args = { cycleParameter },
}
local cycleParameterCall: Record = {
	type = "AstExprCall",
	location = "parameter-return-cycle-call",
	func = cycleParameterFunction,
	args = {},
	self = false,
}
cycleParameterFunction.body = block({
	returnStatement({ localExpression(cycleParameter, "parameter-return-cycle-read") }, "parameter-return-cycle"),
}, "parameter-return-cycle-body")
cycleParameterCall.args = { cycleParameterCall }
expectMatcherFailure(cycleParameterCall)

expectProof(
	"direct-return-depth-64",
	nestedFactory(TargetOriginMatcher.maxDirectReturnDepth, "direct-return-depth-64-factory"),
	authenticatedOrigin,
	nil
)
expectOriginFailure(
	"direct-return-depth-65",
	nestedFactory(TargetOriginMatcher.maxDirectReturnDepth + 1, "direct-return-depth-65-factory"),
	nil
)

local invalidBodies: { { name: string, body: { Record } } } = {
	{ name = "empty", body = {} },
	{ name = "zero", body = { returnStatement({}, "direct-return-invalid-zero") } },
	{
		name = "multiple",
		body = {
			returnStatement({
				differentTarget("direct-return-invalid-multiple-first"),
				globalExpression("authenticated_target", "direct-return-invalid-multiple-second"),
			}, "direct-return-invalid-multiple"),
		},
	},
	{
		name = "statements",
		body = {
			{ type = "AstStatExpr", location = "direct-return-invalid-statements-effect", expr = differentTarget("direct-return-invalid-statements-value") },
			returnStatement({ globalExpression("authenticated_target", "direct-return-invalid-statements-returned") }, "direct-return-invalid-statements"),
		},
	},
	{
		name = "control",
		body = {
			Support.branchStatement(
				"direct-return-invalid-control",
				{ returnStatement({ globalExpression("authenticated_target", "direct-return-invalid-control-then-value") }, "direct-return-invalid-control-then") },
				block({ returnStatement({ globalExpression("authenticated_target", "direct-return-invalid-control-else-value") }, "direct-return-invalid-control-else") }, "direct-return-invalid-control-else-block")
			),
		},
	},
	{
		name = "open-call",
		body = {
			returnStatement({ {
				type = "AstExprCall",
				location = "direct-return-invalid-open-call-value",
				func = globalExpression("produce", "direct-return-invalid-open-call-callee"),
				args = {},
				self = false,
			} }, "direct-return-invalid-open-call"),
		},
	},
	{
		name = "vararg",
		body = { returnStatement({ { type = "AstExprVarargs", location = "direct-return-invalid-vararg-value" } }, "direct-return-invalid-vararg") },
	},
	{
		name = "wrong-origin",
		body = { returnStatement({ globalExpression("different_target", "direct-return-invalid-wrong-value") }, "direct-return-invalid-wrong") },
	},
}

local keyedValues: any = {
	globalExpression("authenticated_target", "direct-return-invalid-keyed-value"),
	extra = globalExpression("authenticated_target", "direct-return-invalid-keyed-extra"),
}
table.insert(invalidBodies, {
	name = "keyed",
	body = { returnStatement(keyedValues, "direct-return-invalid-keyed") },
})

for _, row in invalidBodies do
	local _, value = invocationFromBody(row.body, "direct-return-invalid-" .. row.name, nil, nil)
	expectOriginFailure("direct-return-invalid-" .. row.name, value, nil)
end

local _, methodCall = invocationFromBody({
	returnStatement({ globalExpression("authenticated_target", "direct-return-method-value") }, "direct-return-method"),
}, "direct-return-method-factory", nil, nil)
methodCall.self = true
expectOriginFailure("direct-return-method", methodCall, nil)

local _, malformedCall = invocationFromBody({
	returnStatement("malformed", "direct-return-malformed"),
}, "direct-return-malformed-factory", nil, nil)
expectOriginFailure("direct-return-malformed", malformedCall, nil)

local cycleFunction: Record = {
	type = "AstExprFunction",
	location = "direct-return-cycle-function",
	args = {},
}
local cycleCall: Record = {
	type = "AstExprCall",
	location = "direct-return-cycle-call",
	func = cycleFunction,
	args = {},
	self = false,
}
cycleFunction.body = block({ returnStatement({ cycleCall }, "direct-return-cycle") }, "direct-return-cycle-body")
assert(not TargetOriginMatcher.matches(cycleCall, authenticatedOrigin, function(_expression: Record, _origin: Record): boolean
	return false
end))

local wrapperCycle: Record = { type = "AstExprGroup", location = "direct-return-wrapper-cycle" }
wrapperCycle.expr = wrapperCycle
local wrapperCycleAccepted = pcall(function()
	TargetOriginMatcher.matches(wrapperCycle, authenticatedOrigin, function(_expression: Record, _origin: Record): boolean
		return false
	end)
end)
assert(not wrapperCycleAccepted)
