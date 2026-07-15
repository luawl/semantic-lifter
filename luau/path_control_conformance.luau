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

local function auditResolved(path: string, reresolvedPath: string?, engine: string)
	assert(engine == "internal" or engine == "z3", "expected a solver engine")
	local encoded = fs.readFile(path)
	if reresolvedPath ~= nil then
		assert(encoded == fs.readFile(reresolvedPath), "resolved branch-truth IR is not byte-idempotent")
	end
	local program: any = serde.decode("json", encoded)
	assert(#program.edge_rewrites == 4, "expected forwarding and proof rewrites for both branch arms")

	local histories: { [string]: { any } } = {}
	for _, rewrite in program.edge_rewrites do
		local key = `{rewrite.source}:{rewrite.kind}`
		local history = histories[key]
		if history == nil then
			history = {}
			histories[key] = history
		end
		table.insert(history, rewrite)
	end

	local historyCount = 0
	for _, history in histories do
		historyCount += 1
		assert(#history == 2, "each branch arm must have one forwarding and one proof rewrite")
		local forwarding = history[1]
		local proved = history[2]
		assert(forwarding.source == proved.source and forwarding.kind == proved.kind, "branch history changed stable identity")
		assert(forwarding.rule == "forwarding_jump" and forwarding.certificate == nil, "first rewrite lacks structural forwarding authority")
		assert(proved.rule == "proved_branch" and proved.certificate ~= nil, "second rewrite lacks solver authority")
		assert(forwarding.to.target == proved.from.target, "branch rewrite history is disconnected")

		local certificate = program.certificates[proved.certificate + 1]
		assert(certificate ~= nil and certificate.resolution == "proved", "branch rewrite certificate is not proved")
		assert(certificate.engine == (if engine == "z3" then "z3" else "internal_facts"), "branch rewrite used the wrong solver engine")
		local query = program.queries[certificate.query + 1]
		assert(query ~= nil and sameArray(query.path_rewrites, { forwarding.id }), "branch query omitted its forwarding prefix")

		local hasRootTruth = false
		local hasPathTruth = false
		for _, constraintId in query.assumptions do
			local constraint = program.constraints[constraintId + 1]
			local edge = constraint.scope.edge
			assert(edge.source == forwarding.source and edge.kind == forwarding.kind, "query merged unrelated branch roots")
			assert(edge.target == forwarding.from.target, "query changed its original branch target")
			local record = program.evidence[constraint.evidence[1] + 1]
			assert(record.kind == "structural_derivation", "branch query retained frontend solver evidence")
			if record.locator == "backend:cfg-branch-arm-truth:v1" and #constraint.path_rewrites == 0 then
				hasRootTruth = true
			elseif record.locator == "backend:cfg-edge-argument-equality:v1" and sameArray(constraint.path_rewrites, { forwarding.id }) then
				hasPathTruth = true
			end
		end
		assert(hasRootTruth, "proved branch path omitted structural arm truth")
		assert(hasPathTruth, "proved branch path omitted normalized parameter truth")
	end
	assert(historyCount == 2, "expected two independent branch-arm histories")

	local branchFacts = 0
	local argumentFacts = 0
	for _, constraint in program.constraints do
		assert(#constraint.evidence == 1, "backend-derived fact has ambiguous provenance")
		local record = program.evidence[constraint.evidence[1] + 1]
		assert(record.kind == "structural_derivation", "fixture still contains a frontend solver fact")
		if record.locator == "backend:cfg-branch-arm-truth:v1" then
			branchFacts += 1
		elseif record.locator == "backend:cfg-edge-argument-equality:v1" then
			argumentFacts += 1
		else
			assert(false, "fixture contains unknown structural provenance")
		end
	end
	assert(branchFacts == 4, "expected one structural truth fact per branch arm")
	assert(argumentFacts == 4, "expected raw and path-normalized parameter facts")
end

if process.args[1] == "audit" then
	local resolvedPath = process.args[2]
	assert(resolvedPath ~= nil and resolvedPath ~= "", "expected a resolved IR path")
	local engine = process.args[4]
	assert(engine ~= nil, "expected the selected solver engine")
	auditResolved(resolvedPath, process.args[3], engine)
	return
end

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-edge-scoped-control")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-edge-scoped-control")
local evidence = { proof }
local pure = LifterIR.Effects.pure()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local probe = builder:reserveFunction({ name_hint = "edge_dispatch", evidence = evidence })
local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local entryBlock = builder:reserveBlock(probe, { name_hint = "entry", evidence = evidence })
local leftBlock = builder:reserveBlock(probe, { name_hint = "left_path", evidence = evidence })
local rightBlock = builder:reserveBlock(probe, { name_hint = "right_path", evidence = evidence })
local dispatchBlock = builder:reserveBlock(probe, { name_hint = "dispatcher", evidence = evidence })
local trueBlock = builder:reserveBlock(probe, { name_hint = "true_result", evidence = evidence })
local falseBlock = builder:reserveBlock(probe, { name_hint = "false_result", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(probe, entryBlock)

local selector = builder:addParameter(probe, LifterIR.Types.boolean(), "selector")
local dispatchCondition = builder:addBlockParameter(dispatchBlock, LifterIR.Types.boolean(), "dispatch_condition")
local _, trueResults = builder:addInstruction(
	trueBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("left")),
	{ { type = LifterIR.Types.string(), name_hint = "left_result" } },
	{ effects = pure, evidence = evidence }
)
local _, falseResults = builder:addInstruction(
	falseBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("right")),
	{ { type = LifterIR.Types.string(), name_hint = "right_result" } },
	{ effects = pure, evidence = evidence }
)
local _, exportedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(probe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "edge_dispatch" } },
	{ effects = pure, evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportedResults[1] }))
builder:finalizeBlock(
	entryBlock,
	LifterIR.Terminator.branch(selector, LifterIR.Edge(leftBlock), LifterIR.Edge(rightBlock))
)
builder:finalizeBlock(leftBlock, LifterIR.Terminator.jump(LifterIR.Edge(dispatchBlock, { selector })))
builder:finalizeBlock(rightBlock, LifterIR.Terminator.jump(LifterIR.Edge(dispatchBlock, { selector })))
builder:finalizeBlock(
	dispatchBlock,
	LifterIR.Terminator.branch(dispatchCondition, LifterIR.Edge(trueBlock), LifterIR.Edge(falseBlock))
)
builder:finalizeBlock(trueBlock, LifterIR.Terminator.returnValues({ trueResults[1] }))
builder:finalizeBlock(falseBlock, LifterIR.Terminator.returnValues({ falseResults[1] }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(probe)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
