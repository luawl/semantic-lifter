--!strict

local AstAdmission = require("./ast_admission")
local AstFrontend = require("./ast_frontend")

local limits: AstAdmission.Limits = { max_tables = 128, max_entries = 256, max_depth = 32 }

local function inspectOk(value: any)
	local inspection, problem = AstAdmission.inspect(value, limits)
	assert(inspection ~= nil and problem == nil, if problem == nil then "unexpected identity admission failure" else problem.detail)
end

local function inspectProblem(value: any, code: string): AstAdmission.Problem
	local inspection, problem = AstAdmission.inspect(value, limits)
	assert(inspection == nil and problem ~= nil, `expected identity admission failure {code}`)
	assert((problem :: AstAdmission.Problem).code == code, `expected {code}, received {(problem :: AstAdmission.Problem).code}`)
	return problem :: AstAdmission.Problem
end

local function expectFrontendProblem(document: any, code: string, label: string)
	local result = AstFrontend.tryLift(document, { program_id = label, source_name = label })
	assert(result.program == nil and #result.diagnostics == 1, `{label} did not reject at the frontend boundary`)
	assert(result.diagnostics[1].code == code, `{label} changed frontend diagnostic code`)
end

local function runtimeLocal(name: string, location: string): any
	return { type = "AstLocal", name = name, location = location }
end

local function localReference(name: string, location: string): any
	return { type = "AstExprLocal", ["local"] = runtimeLocal(name, location) }
end

local function statementBlock(body: { any }): any
	return { type = "AstStatBlock", body = body }
end

local function document(body: { any }): any
	return { root = statementBlock(body) }
end

local function localStatement(name: string, location: string, values: { any }?): any
	return { type = "AstStatLocal", vars = { runtimeLocal(name, location) }, values = values or {} }
end

local function returnExpression(expression: any): any
	return { type = "AstStatReturn", list = { expression } }
end

local function returnLocal(name: string, location: string): any
	return returnExpression(localReference(name, location))
end

local function functionExpression(arguments: { any }, body: { any }): any
	return { type = "AstExprFunction", args = arguments, body = statementBlock(body) }
end

local copiedLocation = "copy-location"
inspectOk(statementBlock({
	localStatement("copied", copiedLocation, { { type = "AstExprConstantNil" } }),
	returnLocal("copied", copiedLocation),
}))

local inconsistentLocation = "inconsistent-copy-location"
local inconsistent = statementBlock({
	localStatement("canonical", inconsistentLocation, nil),
	returnExpression(localReference("alias", inconsistentLocation)),
})
assert(string.find(inspectProblem(inconsistent, "inconsistent_local_identity").detail, "does not match", 1, true) ~= nil)

local dangling = document({
	{ type = "AstStatReturn", list = {} },
	returnLocal("ghost", "dead-dangling-location"),
})
inspectProblem(dangling, "unresolved_local_identity")
expectFrontendProblem(dangling, "unresolved_local_identity", "dead-dangling-local-admission")

local captureLocation = "valid-capture-location"
inspectOk(document({
	localStatement("captured", captureLocation, { { type = "AstExprConstantNil" } }),
	returnExpression(functionExpression({}, { returnLocal("captured", captureLocation) })),
}))

local nestedOwnerLocation = "nested-owner-location"
local outward = document({
	localStatement("holder", "nested-holder-location", { functionExpression({}, {
		localStatement("nested", nestedOwnerLocation, { { type = "AstExprConstantNil" } }),
	}) }),
	{ type = "AstStatReturn", list = {} },
	returnLocal("nested", nestedOwnerLocation),
})
inspectProblem(outward, "invalid_local_owner")
expectFrontendProblem(outward, "invalid_local_owner", "dead-outward-local-admission")

local lateLocation = "dead-later-local-location"
local late = document({
	{ type = "AstStatReturn", list = {} },
	returnLocal("late", lateLocation),
	localStatement("late", lateLocation, nil),
})
inspectProblem(late, "invalid_local_scope")
expectFrontendProblem(late, "invalid_local_scope", "dead-later-local-admission")

local nestedScopeLocation = "dead-nested-scope-location"
local nestedScope = document({
	statementBlock({ localStatement("scoped", nestedScopeLocation, nil) }),
	{ type = "AstStatReturn", list = {} },
	returnLocal("scoped", nestedScopeLocation),
})
inspectProblem(nestedScope, "invalid_local_scope")
expectFrontendProblem(nestedScope, "invalid_local_scope", "dead-nested-scope-admission")

local initializerLocation = "initializer-binding-location"
inspectProblem(statementBlock({
	localStatement("initializer", initializerLocation, { localReference("initializer", initializerLocation) }),
}), "invalid_local_scope")

local recursiveLocation = "recursive-function-location"
inspectOk(statementBlock({ {
	type = "AstStatLocalFunction",
	name = runtimeLocal("recursive", recursiveLocation),
	func = functionExpression({}, { returnLocal("recursive", recursiveLocation) }),
} }))
local initializedFunctionLocation = "initialized-function-location"
inspectProblem(statementBlock({
	localStatement("initialized", initializedFunctionLocation, {
		functionExpression({}, { returnLocal("initialized", initializedFunctionLocation) }),
	}),
}), "invalid_local_scope")

local outerBlockLocation = "outer-block-location"
inspectOk(statementBlock({
	localStatement("outerBlock", outerBlockLocation, nil),
	statementBlock({ returnLocal("outerBlock", outerBlockLocation) }),
}))
local siblingBlockLocation = "sibling-block-location"
inspectProblem(statementBlock({
	statementBlock({ localStatement("siblingBlock", siblingBlockLocation, nil) }),
	statementBlock({ returnLocal("siblingBlock", siblingBlockLocation) }),
}), "invalid_local_scope")

local numericLocation = "numeric-loop-location"
local function numericLoop(initial: any): any
	return {
		type = "AstStatFor",
		var = runtimeLocal("index", numericLocation),
		from = initial,
		to = { type = "AstExprConstantNumber", value = 1 },
		body = statementBlock({ returnLocal("index", numericLocation) }),
	}
end
inspectOk(statementBlock({ numericLoop({ type = "AstExprConstantNumber", value = 1 }) }))
inspectProblem(statementBlock({ numericLoop(localReference("index", numericLocation)) }), "invalid_local_scope")

local genericLocation = "generic-loop-location"
local function genericLoop(source: any): any
	return {
		type = "AstStatForIn",
		vars = { runtimeLocal("item", genericLocation) },
		values = { source },
		body = statementBlock({ returnLocal("item", genericLocation) }),
	}
end
inspectOk(statementBlock({ genericLoop({ type = "AstExprGlobal", global = "iterator" }) }))
inspectProblem(statementBlock({ genericLoop(localReference("item", genericLocation)) }), "invalid_local_scope")

local repeatLocation = "repeat-condition-location"
inspectOk(statementBlock({ {
	type = "AstStatRepeat",
	body = statementBlock({ localStatement("untilLocal", repeatLocation, nil) }),
	condition = localReference("untilLocal", repeatLocation),
} }))

local parameterLocation = "function-parameter-location"
inspectOk(statementBlock({
	returnExpression(functionExpression(
		{ runtimeLocal("parameter", parameterLocation) },
		{ returnLocal("parameter", parameterLocation) }
	)),
}))

local duplicateSiblingLocation = "duplicate-sibling-location"
inspectProblem(statementBlock({
	localStatement("left", duplicateSiblingLocation, nil),
	localStatement("right", duplicateSiblingLocation, nil),
}), "duplicate_local_identity")
local duplicateNestedLocation = "duplicate-nested-location"
inspectProblem(statementBlock({
	localStatement("outer", duplicateNestedLocation, nil),
	returnExpression(functionExpression(
		{ runtimeLocal("inner", duplicateNestedLocation) },
		{}
	)),
}), "duplicate_local_identity")

local olderLocation = "same-block-older-location"
local newerLocation = "same-block-newer-location"
local olderAfterShadow = document({
	localStatement("shadowed", olderLocation, nil),
	localStatement("shadowed", newerLocation, nil),
	{ type = "AstStatReturn", list = {} },
	returnLocal("shadowed", olderLocation),
})
inspectProblem(olderAfterShadow, "shadowed_local_identity")
expectFrontendProblem(olderAfterShadow, "shadowed_local_identity", "dead-same-block-shadow-admission")

local nestedOuterLocation = "nested-shadow-outer-location"
local nestedInnerLocation = "nested-shadow-inner-location"
local outerInsideShadow = document({
	localStatement("nestedShadow", nestedOuterLocation, nil),
	statementBlock({
		localStatement("nestedShadow", nestedInnerLocation, nil),
		{ type = "AstStatReturn", list = {} },
		returnLocal("nestedShadow", nestedOuterLocation),
	}),
})
inspectProblem(outerInsideShadow, "shadowed_local_identity")
expectFrontendProblem(outerInsideShadow, "shadowed_local_identity", "dead-nested-shadow-admission")

inspectOk(document({
	localStatement("shadowed", olderLocation, nil),
	localStatement("shadowed", newerLocation, nil),
	returnLocal("shadowed", newerLocation),
}))
inspectOk(document({
	localStatement("nestedShadow", nestedOuterLocation, nil),
	statementBlock({
		returnLocal("nestedShadow", nestedOuterLocation),
		localStatement("nestedShadow", nestedInnerLocation, nil),
	}),
}))

local listFirstLocation = "same-list-first-location"
local listLastLocation = "same-list-last-location"
local function duplicateLocalList(selectedLocation: string): any
	return statementBlock({
		{
			type = "AstStatLocal",
			vars = { runtimeLocal("sameList", listFirstLocation), runtimeLocal("sameList", listLastLocation) },
			values = {},
		},
		returnLocal("sameList", selectedLocation),
	})
end
inspectOk(duplicateLocalList(listLastLocation))
inspectProblem(duplicateLocalList(listFirstLocation), "shadowed_local_identity")

local parameterFirstLocation = "same-parameter-first-location"
local parameterLastLocation = "same-parameter-last-location"
local function duplicateParameters(selectedLocation: string): any
	return statementBlock({
		returnExpression(functionExpression({
			runtimeLocal("sameParameter", parameterFirstLocation),
			runtimeLocal("sameParameter", parameterLastLocation),
		}, { returnLocal("sameParameter", selectedLocation) })),
	})
end
inspectOk(duplicateParameters(parameterLastLocation))
inspectProblem(duplicateParameters(parameterFirstLocation), "shadowed_local_identity")

local loopOuterLocation = "loop-shadow-outer-location"
local loopFirstLocation = "loop-shadow-first-location"
local loopLastLocation = "loop-shadow-last-location"
local function shadowingGenericLoop(selectedLocation: string): any
	return statementBlock({
		localStatement("loopShadow", loopOuterLocation, nil),
		{
			type = "AstStatForIn",
			vars = {
				runtimeLocal("loopShadow", loopFirstLocation),
				runtimeLocal("loopShadow", loopLastLocation),
			},
			values = { { type = "AstExprGlobal", global = "iterator" } },
			body = statementBlock({ returnLocal("loopShadow", selectedLocation) }),
		},
	})
end
inspectOk(shadowingGenericLoop(loopLastLocation))
inspectProblem(shadowingGenericLoop(loopFirstLocation), "shadowed_local_identity")
inspectProblem(shadowingGenericLoop(loopOuterLocation), "shadowed_local_identity")

local functionOuterLocation = "function-shadow-outer-location"
local functionInnerLocation = "function-shadow-inner-location"
local function recursiveShadow(selectedLocation: string): any
	return statementBlock({
		localStatement("recursiveShadow", functionOuterLocation, nil),
		{
			type = "AstStatLocalFunction",
			name = runtimeLocal("recursiveShadow", functionInnerLocation),
			func = functionExpression({}, { returnLocal("recursiveShadow", selectedLocation) }),
		},
	})
end
inspectOk(recursiveShadow(functionInnerLocation))
inspectProblem(recursiveShadow(functionOuterLocation), "shadowed_local_identity")

local declarationShapeCases: { {
	label: string,
	code: string,
	location: string,
	expected_location: string?,
	statement: any,
} } = {
	{
		label = "dead-local-vars-shape-admission",
		code = "malformed_ast",
		location = "dead-local-vars",
		statement = { type = "AstStatLocal", location = "dead-local-vars", values = {} },
	},
	{
		label = "dead-local-vars-order-admission",
		code = "malformed_ast",
		location = "dead-local-vars-order",
		statement = { type = "AstStatLocal", location = "dead-local-vars-order" },
	},
	{
		label = "dead-generic-for-vars-shape-admission",
		code = "malformed_generic_for",
		location = "dead-generic-for-vars",
		statement = {
			type = "AstStatForIn",
			location = "dead-generic-for-vars",
			values = { { type = "AstExprGlobal", global = "iterator" } },
			body = statementBlock({}),
		},
	},
	{
		label = "dead-generic-for-vars-order-admission",
		code = "malformed_generic_for",
		location = "dead-generic-for-vars-order",
		statement = { type = "AstStatForIn", location = "dead-generic-for-vars-order" },
	},
	{
		label = "dead-generic-for-empty-vars-admission",
		code = "malformed_generic_for",
		location = "dead-generic-for-empty-vars",
		statement = {
			type = "AstStatForIn",
			location = "dead-generic-for-empty-vars",
			vars = {},
			values = { { type = "AstExprGlobal", global = "iterator" } },
			body = statementBlock({}),
		},
	},
	{
		label = "dead-function-args-shape-admission",
		code = "malformed_ast",
		location = "dead-function-args",
		statement = returnExpression({
			type = "AstExprFunction",
			location = "dead-function-args",
			vararg = false,
			body = statementBlock({}),
		}),
	},
	{
		label = "dead-function-body-order-admission",
		code = "malformed_function",
		location = "dead-function-body-order",
		expected_location = "unknown",
		statement = returnExpression({
			type = "AstExprFunction",
			location = "dead-function-body-order",
			vararg = false,
		}),
	},
}
local declarationShapeFailures = {}
for _, case in declarationShapeCases do
	local caseDocument = document({ { type = "AstStatReturn", list = {} }, case.statement })
	local result = AstFrontend.tryLift(caseDocument, { program_id = case.label, source_name = case.label })
	if result.program ~= nil
		or #result.diagnostics ~= 1
		or result.diagnostics[1].code ~= case.code
		or result.diagnostics[1].location ~= (case.expected_location or case.location)
	then
		table.insert(declarationShapeFailures, case.label)
	end
end
assert(
	#declarationShapeFailures == 0,
	`declaration shape admission mismatches: {table.concat(declarationShapeFailures, ", ")}`
)

type DeclarationRoleCase = {
	label: string,
	code: string,
	missing_value: any?,
	missing_detail: string,
	name_detail: string?,
	name_first: boolean?,
}

local declarationRoleCases: { DeclarationRoleCase } = {
	{ label = "local-declaration", code = "malformed_local_declaration", missing_value = "not-an-ast-local",
		missing_detail = "local declaration variable is not an AST local" },
	{ label = "local-function", code = "malformed_local_function",
		missing_detail = "local function is missing its lexical identity" },
	{ label = "numeric-for", code = "malformed_numeric_for", missing_detail = "numeric for is missing its lexical variable",
		name_detail = "numeric-for variable has no name", name_first = true },
	{ label = "generic-for", code = "malformed_generic_for", missing_value = "not-an-ast-local",
		missing_detail = "generic-for variable is not a lexical local", name_detail = "generic-for variable has no name",
		name_first = true },
	{ label = "function-self", code = "malformed_function_parameter", missing_value = "not-an-ast-local",
		missing_detail = "function parameter is not a local declaration" },
	{ label = "function-argument", code = "malformed_function_parameter", missing_value = "not-an-ast-local",
		missing_detail = "function parameter is not a local declaration" },
}

local function declarationRoleStatement(label: string, identity: any): any
	local ownerLocation = `{label}-owner`
	if label == "local-declaration" then
		return { type = "AstStatLocal", location = ownerLocation, vars = { identity }, values = {} }
	elseif label == "local-function" then
		return { type = "AstStatLocalFunction", location = ownerLocation, name = identity, func = functionExpression({}, {}) }
	elseif label == "numeric-for" then
		return {
			type = "AstStatFor",
			location = ownerLocation,
			var = identity,
			from = { type = "AstExprConstantNumber", value = 1 },
			to = { type = "AstExprConstantNumber", value = 2 },
			body = statementBlock({}),
		}
	elseif label == "generic-for" then
		return {
			type = "AstStatForIn",
			location = ownerLocation,
			vars = { identity },
			values = { { type = "AstExprGlobal", global = "iterator" } },
			body = statementBlock({}),
		}
	end
	local functionNode = { type = "AstExprFunction", location = ownerLocation, args = {}, body = statementBlock({}) }
	if label == "function-self" then
		functionNode.self = identity
	else
		functionNode.args = { identity }
	end
	return returnExpression(functionNode)
end

local declarationRoleFailures = {}
for _, case in declarationRoleCases do
	local invalidNameLocation = `{case.label}-invalid-name`
	local invalidIdentityLocation = `{case.label}-invalid-identity`
	local nameDetail = case.name_detail or "local declaration is missing its name"
	for _, mode in { "reachable", "dead" } do
		for _, variant in {
			{ label = "missing", value = case.missing_value, detail = case.missing_detail, location = "unknown" },
			{
				label = "invalid-name",
				value = runtimeLocal("", invalidNameLocation),
				detail = nameDetail,
				location = invalidNameLocation,
			},
			{
				label = "invalid-identity",
				value = { type = "NotAstLocal", name = "", location = invalidIdentityLocation },
				detail = if case.name_first then nameDetail else "local declaration is missing its source location",
				location = invalidIdentityLocation,
			},
		} do
			local statement = declarationRoleStatement(case.label, variant.value)
			local body = if mode == "dead" then { { type = "AstStatReturn", list = {} }, statement } else { statement }
			local label = `{mode}-{case.label}-{variant.label}`
			local result = AstFrontend.tryLift(document(body), { program_id = label, source_name = label })
			local diagnostic = result.diagnostics[1]
			if result.program ~= nil
				or #result.diagnostics ~= 1
				or diagnostic.code ~= case.code
				or diagnostic.detail ~= variant.detail
				or diagnostic.location ~= variant.location
			then
				table.insert(declarationRoleFailures, label)
			end
		end
	end
end
assert(
	#declarationRoleFailures == 0,
	`declaration role admission mismatches: {table.concat(declarationRoleFailures, ", ")}`
)

return true
