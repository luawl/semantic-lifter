--!strict

local Support = require("./temporal_test_support")

type Record = Support.Record

local assignment = Support.assignment
local assignmentValue = Support.assignmentValue
local block = Support.block
local callExpression = Support.callExpression
local callStatement = Support.callStatement
local declaration = Support.declaration
local document = Support.document
local expectFailure = Support.expectFailure
local localExpression = Support.localExpression
local localStatement = Support.localStatement
local verifyOrigin = Support.verifyOrigin

local function globalExpression(name: string, location: string): Record
	return { type = "AstExprGlobal", location = location, global = name }
end

local function multiAssignment(locals: { Record }, values: { Record }, location: string): Record
	local targets: { Record } = {}
	for index, localNode in locals do
		table.insert(targets, localExpression(localNode, `{location}:target:{index}`))
	end
	return {
		type = "AstStatAssign",
		location = location,
		vars = targets,
		values = values,
	}
end

local directTarget = declaration("directTarget", "assignment-direct-target")
local directCall = callExpression(directTarget, "assignment-direct-call")
local directProof = verifyOrigin(
	document({
		localStatement(directTarget, "assignment-direct-declaration"),
		assignment(directTarget, "assignment-direct-current"),
		multiAssignment({ directTarget }, { directCall }, "assignment-direct-rewrite"),
	}),
	directCall,
	directTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(directProof.definition_location == "assignment-direct-current", "assignment RHS did not observe the incoming target")

local compoundTarget = declaration("compoundTarget", "assignment-compound-target")
local compoundCall = callExpression(compoundTarget, "assignment-compound-call")
local compoundProof = verifyOrigin(
	document({
		localStatement(compoundTarget, "assignment-compound-declaration"),
		assignment(compoundTarget, "assignment-compound-current"),
		{
			type = "AstStatCompoundAssign",
			location = "assignment-compound-rewrite",
			var = localExpression(compoundTarget, "assignment-compound-rewrite:target"),
			op = "Add",
			value = compoundCall,
		},
	}),
	compoundCall,
	compoundTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(compoundProof.definition_location == "assignment-compound-current", "compound RHS did not observe the incoming target")

local aliasStable = declaration("aliasStable", "assignment-alias-stable")
local aliasPlace = declaration("aliasPlace", "assignment-alias-place")
local aliasTarget = declaration("aliasTarget", "assignment-alias-target")
local aliasCall = callExpression(aliasTarget, "assignment-alias-call")
local aliasWrite = multiAssignment(
	{ aliasTarget, aliasPlace },
	{
		localExpression(aliasPlace, "assignment-alias-incoming"),
		globalExpression("different_target", "assignment-alias-replacement"),
	},
	"assignment-alias-simultaneous"
)
local aliasProof = verifyOrigin(
	document({
		localStatement(
			aliasStable,
			"assignment-alias-stable-declaration",
			globalExpression("authenticated_target", "assignment-alias-stable-value")
		),
		localStatement(aliasPlace, "assignment-alias-place-declaration"),
		assignmentValue(aliasPlace, "assignment-alias-current", localExpression(aliasStable, "assignment-alias-current-value")),
		localStatement(aliasTarget, "assignment-alias-target-declaration"),
		aliasWrite,
		callStatement(aliasCall, "assignment-alias-call-statement"),
	}),
	aliasCall,
	aliasTarget,
	{ kind = "environment", name = "authenticated_target" }
)
assert(aliasProof.alias_depth == 2, "simultaneous assignment lost the incoming alias identity")
assert(aliasProof.definition_location == "assignment-alias-simultaneous", "simultaneous assignment lost its target definition")

local committedTarget = declaration("committedTarget", "assignment-committed-target")
local committedCall = callExpression(committedTarget, "assignment-committed-call")
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(committedTarget, "assignment-committed-declaration"),
			assignment(committedTarget, "assignment-committed-current"),
			assignmentValue(
				committedTarget,
				"assignment-committed-replacement",
				globalExpression("different_target", "assignment-committed-replacement-value")
			),
			callStatement(committedCall, "assignment-committed-call-statement"),
		}),
		committedCall,
		committedTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "does not match its authenticated origin")

local capturedTarget = declaration("capturedTarget", "assignment-captured-target")
local capturedHolder = declaration("capturedHolder", "assignment-captured-holder")
local capturedCall = callExpression(capturedTarget, "assignment-captured-call")
local capturedFunction: Record = {
	type = "AstExprFunction",
	location = "assignment-captured-function",
	args = {},
	body = block({ callStatement(capturedCall, "assignment-captured-call-statement") }, "assignment-captured-body"),
}
expectFailure(function()
	verifyOrigin(
		document({
			localStatement(capturedTarget, "assignment-captured-declaration"),
			assignment(capturedTarget, "assignment-captured-current"),
			localStatement(capturedHolder, "assignment-captured-holder-declaration"),
			multiAssignment(
				{ capturedTarget, capturedHolder },
				{ globalExpression("different_target", "assignment-captured-replacement"), capturedFunction },
				"assignment-captured-simultaneous"
			),
		}),
		capturedCall,
		capturedTarget,
		{ kind = "environment", name = "authenticated_target" }
	)
end, "write after or inside its closure snapshot")
