--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")
local LifterIR = require("./lifter_ir")

local function sameArray(left: { any }, right: { any }): boolean
	if #left ~= #right then
		return false
	end
	for index, value in left do
		if right[index] ~= value then
			return false
		end
	end
	return true
end

local function auditResolved(path: string, reresolvedPath: string?)
	local encoded = fs.readFile(path)
	if reresolvedPath ~= nil then
		assert(encoded == fs.readFile(reresolvedPath), "resolved IR is not idempotent across persisted replay")
	end
	local program: any = serde.decode("json", encoded)
	local rewrites: { any } = program.edge_rewrites
	assert(#rewrites == 6, "expected three authenticated rewrites for each root path")

	local histories: { [string]: { any } } = {}
	for _, rewrite in rewrites do
		local key = `{rewrite.source}:{rewrite.kind}`
		local history = histories[key]
		if history == nil then
			history = {}
			histories[key] = history
		end
		table.insert(history, rewrite)
	end
	local orderedHistories = {}
	for _, history in histories do
		table.insert(orderedHistories, history)
	end
	table.sort(orderedHistories, function(left, right)
		return left[1].source < right[1].source
	end)
	assert(#orderedHistories == 2, "expected two independent stable edge histories")
	local leftHistory = orderedHistories[1]
	local rightHistory = orderedHistories[2]
	assert(#leftHistory == 3 and #rightHistory == 3, "each predecessor must carry one proof, one forwarding rewrite, and one proof")
	local leftFirst, leftForward, leftSecond = leftHistory[1], leftHistory[2], leftHistory[3]
	local rightFirst, rightForward, rightSecond = rightHistory[1], rightHistory[2], rightHistory[3]
	assert(leftFirst.source == leftForward.source and leftForward.source == leftSecond.source, "left rewrite history changed stable source identity")
	assert(rightFirst.source == rightForward.source and rightForward.source == rightSecond.source, "right rewrite history changed stable source identity")
	assert(leftFirst.source ~= rightFirst.source, "independent predecessor histories were merged")
	assert(leftFirst.kind == "jump" and rightFirst.kind == "jump", "left/right edge kind changed")
	assert(leftForward.kind == "jump" and rightForward.kind == "jump", "forwarding edge kind changed")
	assert(leftSecond.kind == "jump" and rightSecond.kind == "jump", "final edge kind changed")
	assert(leftFirst.rule == "proved_branch" and rightFirst.rule == "proved_branch", "first dispatcher lacks solver authority")
	assert(leftForward.rule == "forwarding_jump" and rightForward.rule == "forwarding_jump", "glue rewrite lacks structural authority")
	assert(leftForward.certificate == nil and rightForward.certificate == nil, "structural forwarding gained a fake certificate")
	assert(leftSecond.rule == "proved_branch" and rightSecond.rule == "proved_branch", "second dispatcher lacks solver authority")
	assert(leftFirst.from.target == rightFirst.from.target, "root paths did not enter the same first dispatcher")
	assert(leftFirst.to.target == leftForward.from.target, "left first proof is disconnected from forwarding")
	assert(rightFirst.to.target == rightForward.from.target, "right first proof is disconnected from forwarding")
	assert(leftForward.to.target == leftSecond.from.target, "left forwarding is disconnected from the second proof")
	assert(rightForward.to.target == rightSecond.from.target, "right forwarding is disconnected from the second proof")
	assert(leftSecond.from.target == rightSecond.from.target, "root paths did not reach the same second dispatcher")
	assert(leftSecond.to.target ~= rightSecond.to.target, "second-hop facts leaked across root paths")

	local function queryFor(rewrite: any): any
		local certificate = program.certificates[rewrite.certificate + 1]
		assert(certificate ~= nil, "rewrite certificate is missing")
		local query = program.queries[certificate.query + 1]
		assert(query ~= nil, "rewrite query is missing")
		return query
	end
	local function hasStructuralAssumption(query: any): boolean
		for _, constraintId in query.assumptions do
			local constraint = program.constraints[constraintId + 1]
			for _, evidenceId in constraint.evidence do
				if program.evidence[evidenceId + 1].kind == "structural_derivation" then
					return true
				end
			end
		end
		return false
	end
	local function assumptionsContain(query: any, earlier: any): boolean
		local present = {}
		for _, constraintId in query.assumptions do
			present[constraintId] = true
		end
		for _, constraintId in earlier.assumptions do
			if present[constraintId] ~= true then
				return false
			end
		end
		return true
	end
	local function hasDerivedFactAtPath(query: any, path: { number }): boolean
		for _, constraintId in query.assumptions do
			if sameArray(program.constraints[constraintId + 1].path_rewrites, path) then
				return true
			end
		end
		return false
	end
	for _, constraint in program.constraints do
		assert(#constraint.evidence == 1, "backend-derived edge fact has ambiguous provenance")
		assert(program.evidence[constraint.evidence[1] + 1].kind == "structural_derivation", "chained fixture still contains a frontend solver fact")
	end

	local leftFirstQuery = queryFor(leftFirst)
	local rightFirstQuery = queryFor(rightFirst)
	local leftSecondQuery = queryFor(leftSecond)
	local rightSecondQuery = queryFor(rightSecond)
	assert(#leftFirstQuery.path_rewrites == 0 and #rightFirstQuery.path_rewrites == 0, "first-hop proof has stale history")
	assert(hasStructuralAssumption(leftFirstQuery) and hasStructuralAssumption(rightFirstQuery), "first dispatcher still depends on manual edge equality")
	assert(sameArray(leftSecondQuery.path_rewrites, { leftFirst.id, leftForward.id }), "left second-hop proof omitted structural history")
	assert(sameArray(rightSecondQuery.path_rewrites, { rightFirst.id, rightForward.id }), "right second-hop proof omitted structural history")
	assert(assumptionsContain(leftSecondQuery, leftFirstQuery), "left facts were not carried through the first proof")
	assert(assumptionsContain(rightSecondQuery, rightFirstQuery), "right facts were not carried through the first proof")
	assert(hasDerivedFactAtPath(leftSecondQuery, { leftFirst.id, leftForward.id }), "left second parameter equality was not derived at its exact path")
	assert(hasDerivedFactAtPath(rightSecondQuery, { rightFirst.id, rightForward.id }), "right second parameter equality was not derived at its exact path")
	assert(not sameArray(leftSecondQuery.assumptions, rightSecondQuery.assumptions), "unrelated predecessor assumptions were merged")
end

if process.args[1] == "audit" then
	local resolvedPath = process.args[2]
	assert(resolvedPath ~= nil and resolvedPath ~= "", "expected a resolved IR path")
	auditResolved(resolvedPath, process.args[3])
	return
end

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-chained-edge-control")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-chained-edge-control")
local evidence = { proof }
local pure = LifterIR.Effects.pure()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local probe = builder:reserveFunction({ name_hint = "chained_dispatch", evidence = evidence })
local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local entryBlock = builder:reserveBlock(probe, { name_hint = "entry", evidence = evidence })
local leftBlock = builder:reserveBlock(probe, { name_hint = "left_path", evidence = evidence })
local rightBlock = builder:reserveBlock(probe, { name_hint = "right_path", evidence = evidence })
local firstDispatchBlock = builder:reserveBlock(probe, { name_hint = "first_dispatcher", evidence = evidence })
local forwardingBlock = builder:reserveBlock(probe, { name_hint = "forwarding_glue", evidence = evidence })
local secondDispatchBlock = builder:reserveBlock(probe, { name_hint = "second_dispatcher", evidence = evidence })
local trueBlock = builder:reserveBlock(probe, { name_hint = "true_result", evidence = evidence })
local falseBlock = builder:reserveBlock(probe, { name_hint = "false_result", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(probe, entryBlock)

local selector = builder:addParameter(probe, LifterIR.Types.boolean(), "selector")
local firstCondition = builder:addBlockParameter(firstDispatchBlock, LifterIR.Types.boolean(), "first_condition")
local forwardedCondition = builder:addBlockParameter(firstDispatchBlock, LifterIR.Types.boolean(), "forwarded_condition")
local glueCondition = builder:addBlockParameter(forwardingBlock, LifterIR.Types.boolean(), "glue_condition")
local secondCondition = builder:addBlockParameter(secondDispatchBlock, LifterIR.Types.boolean(), "second_condition")
local _, copiedGlueCondition = builder:addInstruction(
	forwardingBlock,
	LifterIR.Operation.copy(glueCondition),
	{ { type = LifterIR.Types.boolean(), name_hint = "copied_glue_condition" } },
	{ effects = pure, evidence = evidence }
)

local _, leftFirst = builder:addInstruction(
	leftBlock,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(true)),
	{ { type = LifterIR.Types.boolean(), name_hint = "left_first" } },
	{ effects = pure, evidence = evidence }
)
local _, leftSecond = builder:addInstruction(
	leftBlock,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(true)),
	{ { type = LifterIR.Types.boolean(), name_hint = "left_second" } },
	{ effects = pure, evidence = evidence }
)
local _, rightFirst = builder:addInstruction(
	rightBlock,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
	{ { type = LifterIR.Types.boolean(), name_hint = "right_first" } },
	{ effects = pure, evidence = evidence }
)
local _, rightSecond = builder:addInstruction(
	rightBlock,
	LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
	{ { type = LifterIR.Types.boolean(), name_hint = "right_second" } },
	{ effects = pure, evidence = evidence }
)
local _, trueResult = builder:addInstruction(
	trueBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("left-chain")),
	{ { type = LifterIR.Types.string(), name_hint = "left_chain" } },
	{ effects = pure, evidence = evidence }
)
local _, falseResult = builder:addInstruction(
	falseBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("right-chain")),
	{ { type = LifterIR.Types.string(), name_hint = "right_chain" } },
	{ effects = pure, evidence = evidence }
)
local _, exported = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(probe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "chained_dispatch" } },
	{ effects = pure, evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exported[1] }))
builder:finalizeBlock(
	entryBlock,
	LifterIR.Terminator.branch(selector, LifterIR.Edge(leftBlock), LifterIR.Edge(rightBlock))
)
builder:finalizeBlock(
	leftBlock,
	LifterIR.Terminator.jump(LifterIR.Edge(firstDispatchBlock, { leftFirst[1], leftSecond[1] }))
)
builder:finalizeBlock(
	rightBlock,
	LifterIR.Terminator.jump(LifterIR.Edge(firstDispatchBlock, { rightFirst[1], rightSecond[1] }))
)
builder:finalizeBlock(
	firstDispatchBlock,
	LifterIR.Terminator.branch(
		firstCondition,
		LifterIR.Edge(forwardingBlock, { forwardedCondition }),
		LifterIR.Edge(forwardingBlock, { forwardedCondition })
	)
)
builder:finalizeBlock(
	forwardingBlock,
	LifterIR.Terminator.jump(LifterIR.Edge(secondDispatchBlock, { copiedGlueCondition[1] }))
)
builder:finalizeBlock(
	secondDispatchBlock,
	LifterIR.Terminator.branch(secondCondition, LifterIR.Edge(trueBlock), LifterIR.Edge(falseBlock))
)
builder:finalizeBlock(trueBlock, LifterIR.Terminator.returnValues({ trueResult[1] }))
builder:finalizeBlock(falseBlock, LifterIR.Terminator.returnValues({ falseResult[1] }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(probe)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
