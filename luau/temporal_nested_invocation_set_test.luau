--!strict

local Support = require("./temporal_test_support")
local InvocationSupport = require("./temporal_invocation_test_support")
local TemporalTargetIdentity = require("./temporal_target_identity")

type Record = Support.Record

local assignment = Support.assignment
local assignmentValue = Support.assignmentValue
local block = Support.block
local branchStatement = Support.branchStatement
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
local whileStatement = Support.whileStatement

local appendAliasBinding = InvocationSupport.appendAliasBinding
local differentTarget = InvocationSupport.differentTarget
local localFunctionStatement = InvocationSupport.localFunctionStatement
local localInvocation = InvocationSupport.localInvocation

local authenticatedOrigin: Record = { kind = "environment", name = "authenticated_target" }

local function expectProof(documentValue: Record, call: Record, target: Record, location: string)
	local proof = verifyOrigin(documentValue, call, target, authenticatedOrigin)
	assert(proof.definition_count == 1, `{location} nested invocation produced a definition set`)
	assert(proof.definition_location == location, `{location} nested future write stayed committed`)
end

local function expectOriginFailure(documentValue: Record, call: Record, target: Record)
	local location = target.location
	assert(type(location) == "string" and location ~= "")
	expectFailure(function()
		verifyOrigin(documentValue, call, target, authenticatedOrigin)
	end, "temporal target place " .. location)
end

local function writerFunction(target: Record, writer: Record, prefix: string, recursive: boolean): Record
	local body: { Record } = {
		assignmentValue(target, prefix .. "-write", differentTarget(prefix .. "-value")),
	}
	if recursive then
		table.insert(body, callStatement(localInvocation(writer, prefix .. "-recursive-call", false), prefix .. "-recursive-statement"))
	end
	local functionValue, _ = invocationFromBody(body, prefix .. "-function", nil, nil)
	return functionValue
end

local function directDocument(prefix: string, siteCount: number): (Record, Record, Record)
	assert(siteCount >= 2)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local writer = declaration(prefix .. "Writer", prefix .. "-writer")
	local functionValue = writerFunction(target, writer, prefix .. "-writer", false)
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(writer, prefix .. "-writer-declaration", functionValue),
		callStatement(call, prefix .. "-read-statement"),
	}
	for siteIndex = 1, siteCount do
		table.insert(
			body,
			callStatement(
				localInvocation(writer, `{prefix}-writer-call-{siteIndex}`, false),
				`{prefix}-writer-statement-{siteIndex}`
			)
		)
	end
	return document(body), call, target
end

local sequential, sequentialCall, sequentialTarget = directDocument("nested-set-sequential", 2)
expectProof(sequential, sequentialCall, sequentialTarget, "nested-set-sequential-current")

local bounded, boundedCall, boundedTarget = directDocument(
	"nested-set-bounded",
	TemporalTargetIdentity.maxInvocationSites
)
expectProof(bounded, boundedCall, boundedTarget, "nested-set-bounded-current")

local excessive, excessiveCall, excessiveTarget = directDocument(
	"nested-set-excessive",
	TemporalTargetIdentity.maxInvocationSites + 1
)
expectOriginFailure(excessive, excessiveCall, excessiveTarget)

local branchTarget = declaration("nestedSetBranchTarget", "nested-set-branch-target")
local branchCall = callExpression(branchTarget, "nested-set-branch-read")
local branchWriter = declaration("nestedSetBranchWriter", "nested-set-branch-writer")
local branchFunction = writerFunction(branchTarget, branchWriter, "nested-set-branch-writer", false)
local branchFixture = document({
	localStatement(branchTarget, "nested-set-branch-target-declaration"),
	assignment(branchTarget, "nested-set-branch-current"),
	localStatement(branchWriter, "nested-set-branch-writer-declaration", branchFunction),
	callStatement(branchCall, "nested-set-branch-read-statement"),
	branchStatement(
		"nested-set-branch",
		{ callStatement(localInvocation(branchWriter, "nested-set-branch-then-call", false), "nested-set-branch-then-statement") },
		block({
			callStatement(localInvocation(branchWriter, "nested-set-branch-else-call", false), "nested-set-branch-else-statement"),
		}, "nested-set-branch-else")
	),
})
expectProof(branchFixture, branchCall, branchTarget, "nested-set-branch-current")

local aliasTarget = declaration("nestedSetAliasTarget", "nested-set-alias-target")
local aliasCall = callExpression(aliasTarget, "nested-set-alias-read")
local aliasWriter = declaration("nestedSetAliasWriter", "nested-set-alias-writer")
local aliasFunction = writerFunction(aliasTarget, aliasWriter, "nested-set-alias-writer", false)
local aliasBody: { Record } = {
	localStatement(aliasTarget, "nested-set-alias-target-declaration"),
	assignment(aliasTarget, "nested-set-alias-current"),
	localStatement(aliasWriter, "nested-set-alias-writer-declaration", aliasFunction),
	callStatement(aliasCall, "nested-set-alias-read-statement"),
}
for leafIndex = 1, 2 do
	local leaf = appendAliasBinding(
		aliasBody,
		aliasWriter,
		`nested-set-alias-leaf-{leafIndex}`,
		true,
		if leafIndex == 1 then "local" else "assignment"
	)
	table.insert(
		aliasBody,
		callStatement(localInvocation(leaf, `nested-set-alias-call-{leafIndex}`, true), `nested-set-alias-statement-{leafIndex}`)
	)
end
expectProof(document(aliasBody), aliasCall, aliasTarget, "nested-set-alias-current")

local callerTarget = declaration("nestedSetCallerTarget", "nested-set-caller-target")
local callerCall = callExpression(callerTarget, "nested-set-caller-read")
local callerWriter = declaration("nestedSetCallerWriter", "nested-set-caller-writer")
local callerWriterFunction = writerFunction(callerTarget, callerWriter, "nested-set-caller-writer", false)
local caller = declaration("nestedSetCaller", "nested-set-caller")
local callerFunction, _ = invocationFromBody({
	callStatement(localInvocation(callerWriter, "nested-set-caller-writer-call", false), "nested-set-caller-writer-statement"),
}, "nested-set-caller-function", nil, nil)
expectProof(
	document({
		localStatement(callerTarget, "nested-set-caller-target-declaration"),
		assignment(callerTarget, "nested-set-caller-current"),
		localStatement(callerWriter, "nested-set-caller-writer-declaration", callerWriterFunction),
		localStatement(caller, "nested-set-caller-declaration", callerFunction),
		callStatement(callerCall, "nested-set-caller-read-statement"),
		callStatement(localInvocation(caller, "nested-set-caller-call-1", false), "nested-set-caller-statement-1"),
		callStatement(localInvocation(caller, "nested-set-caller-call-2", false), "nested-set-caller-statement-2"),
	}),
	callerCall,
	callerTarget,
	"nested-set-caller-current"
)

local function orderedFailure(prefix: string, beforeCount: number, afterCount: number): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local writer = declaration(prefix .. "Writer", prefix .. "-writer")
	local functionValue = writerFunction(target, writer, prefix .. "-writer", false)
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
		localStatement(writer, prefix .. "-writer-declaration", functionValue),
	}
	for index = 1, beforeCount do
		table.insert(body, callStatement(localInvocation(writer, `{prefix}-before-call-{index}`, false), `{prefix}-before-statement-{index}`))
	end
	table.insert(body, callStatement(call, prefix .. "-read-statement"))
	for index = 1, afterCount do
		table.insert(body, callStatement(localInvocation(writer, `{prefix}-after-call-{index}`, false), `{prefix}-after-statement-{index}`))
	end
	return document(body), call, target
end

local split, splitCall, splitTarget = orderedFailure("nested-set-split", 1, 1)
expectOriginFailure(split, splitCall, splitTarget)
local earlier, earlierCall, earlierTarget = orderedFailure("nested-set-earlier", 2, 0)
expectOriginFailure(earlier, earlierCall, earlierTarget)

local function modeFailure(prefix: string, mode: string): (Record, Record, Record)
	local target = declaration(prefix .. "Target", prefix .. "-target")
	local call = callExpression(target, prefix .. "-read")
	local writer = declaration(prefix .. "Writer", prefix .. "-writer")
	local functionValue = writerFunction(target, writer, prefix .. "-writer", mode == "recursive")
	local body: { Record } = {
		localStatement(target, prefix .. "-target-declaration"),
		assignment(target, prefix .. "-current"),
	}
	if mode == "recursive" then
		table.insert(body, localFunctionStatement(writer, functionValue, prefix .. "-writer-declaration"))
	else
		table.insert(body, localStatement(writer, prefix .. "-writer-declaration", functionValue))
	end
	table.insert(body, callStatement(call, prefix .. "-read-statement"))
	if mode == "escape" then
		table.insert(body, callStatement({
			type = "AstExprCall",
			location = prefix .. "-consumer",
			func = globalExpression("consume", prefix .. "-consumer-callee"),
			args = { localExpression(writer, prefix .. "-argument") },
			self = false,
		}, prefix .. "-consumer-statement"))
	elseif mode == "repeated" then
		table.insert(body, whileStatement(prefix .. "-loop", {
			callStatement(localInvocation(writer, prefix .. "-loop-call", false), prefix .. "-loop-statement"),
		}))
	else
		assert(mode == "recursive")
		table.insert(body, callStatement(localInvocation(writer, prefix .. "-entry-call", false), prefix .. "-entry-statement"))
	end
	return document(body), call, target
end

for _, mode in { "escape", "recursive", "repeated" } do
	local fixture, call, target = modeFailure("nested-set-" .. mode, mode)
	expectOriginFailure(fixture, call, target)
end

local failedCallerTarget = declaration("nestedSetFailedCallerTarget", "nested-set-failed-caller-target")
local failedCallerCall = callExpression(failedCallerTarget, "nested-set-failed-caller-read")
local failedCallerWriter = declaration("nestedSetFailedCallerWriter", "nested-set-failed-caller-writer")
local failedCallerWriterFunction = writerFunction(
	failedCallerTarget,
	failedCallerWriter,
	"nested-set-failed-caller-writer",
	false
)
local failedCaller = declaration("nestedSetFailedCaller", "nested-set-failed-caller")
local failedCallerFunction, _ = invocationFromBody({
	callStatement(
		localInvocation(failedCallerWriter, "nested-set-failed-caller-writer-call", false),
		"nested-set-failed-caller-writer-statement"
	),
}, "nested-set-failed-caller-function", nil, nil)
expectOriginFailure(
	document({
		localStatement(failedCallerTarget, "nested-set-failed-caller-target-declaration"),
		assignment(failedCallerTarget, "nested-set-failed-caller-current"),
		localStatement(
			failedCallerWriter,
			"nested-set-failed-caller-writer-declaration",
			failedCallerWriterFunction
		),
		localStatement(failedCaller, "nested-set-failed-caller-declaration", failedCallerFunction),
		callStatement(failedCallerCall, "nested-set-failed-caller-read-statement"),
		callStatement({
			type = "AstExprCall",
			location = "nested-set-failed-caller-consumer",
			func = globalExpression("consume", "nested-set-failed-caller-consumer-callee"),
			args = { localExpression(failedCaller, "nested-set-failed-caller-argument") },
			self = false,
		}, "nested-set-failed-caller-consumer-statement"),
	}),
	failedCallerCall,
	failedCallerTarget
)
