--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")
local LifterIR = require("./lifter_ir")

if process.args[1] == "audit" then
	local resolvedPath = process.args[2]
	local engine = process.args[3]
	assert(resolvedPath ~= nil and resolvedPath ~= "", "expected a resolved IR path")
	assert(engine == "internal" or engine == "z3", "expected a solver engine")
	local program: any = serde.decode("json", fs.readFile(resolvedPath))
	local argumentFacts = 0
	local branchFacts = 0
	for _, constraint in program.constraints do
		assert(#constraint.evidence == 1, "derived fact has ambiguous provenance")
		local record = program.evidence[constraint.evidence[1] + 1]
		assert(record.kind == "structural_derivation", "affine fixture still contains a frontend solver fact")
		if record.locator == "backend:cfg-edge-argument-equality:v1" then
			argumentFacts += 1
		elseif record.locator == "backend:cfg-branch-arm-truth:v1" then
			branchFacts += 1
			assert(#constraint.path_rewrites == 0, "branch truth was not anchored at its stable root")
		else
			assert(false, "unknown structural fact provenance")
		end
	end
	assert(argumentFacts == 2, "affine fixture should contain two derived edge equalities")
	assert(branchFacts == 4, "affine fixture should contain two branch-arm pairs")
	if engine == "z3" then
		assert(#program.edge_rewrites == 2, "Z3 did not discharge both affine edge paths")
		for _, rewrite in program.edge_rewrites do
			assert(rewrite.rule == "proved_branch", "affine dispatcher used non-solver authority")
			local certificate = program.certificates[rewrite.certificate + 1]
			assert(certificate.engine == "z3" and certificate.resolution == "proved", "affine rewrite lacks a direct Z3 proof")
		end
	else
		assert(#program.edge_rewrites == 0, "internal facts guessed an affine edge result")
	end
	return
end

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-relational-edge-control")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-relational-edge-control")
local evidence = { proof }
local pure = LifterIR.Effects.pure()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local probe = builder:reserveFunction({ name_hint = "relational_dispatch", evidence = evidence })
local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local entryBlock = builder:reserveBlock(probe, { name_hint = "entry", evidence = evidence })
local leftBlock = builder:reserveBlock(probe, { name_hint = "left_path", evidence = evidence })
local rightBlock = builder:reserveBlock(probe, { name_hint = "right_path", evidence = evidence })
local dispatchBlock = builder:reserveBlock(probe, { name_hint = "dispatcher", evidence = evidence })
local trueBlock = builder:reserveBlock(probe, { name_hint = "matched", evidence = evidence })
local falseBlock = builder:reserveBlock(probe, { name_hint = "other", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(probe, entryBlock)

local selector = builder:addParameter(probe, LifterIR.Types.boolean(), "selector")
local dispatchState = builder:addBlockParameter(dispatchBlock, LifterIR.Types.integer(), "state")
local _, leftState = builder:addInstruction(
	leftBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("7")),
	{ { type = LifterIR.Types.integer(), name_hint = "left_state" } },
	{ effects = pure, evidence = evidence }
)
local _, rightState = builder:addInstruction(
	rightBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("8")),
	{ { type = LifterIR.Types.integer(), name_hint = "right_state" } },
	{ effects = pure, evidence = evidence }
)
local _, step = builder:addInstruction(
	dispatchBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = LifterIR.Types.integer(), name_hint = "step" } },
	{ effects = pure, evidence = evidence }
)
local _, nextState = builder:addInstruction(
	dispatchBlock,
	LifterIR.Operation.binary("add", dispatchState, step[1], "primitive"),
	{ { type = LifterIR.Types.integer(), name_hint = "next_state" } },
	{ effects = pure, evidence = evidence }
)
local _, targetState = builder:addInstruction(
	dispatchBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("8")),
	{ { type = LifterIR.Types.integer(), name_hint = "target_state" } },
	{ effects = pure, evidence = evidence }
)
local _, dispatchCondition = builder:addInstruction(
	dispatchBlock,
	LifterIR.Operation.binary("equal", nextState[1], targetState[1], "primitive"),
	{ { type = LifterIR.Types.boolean(), name_hint = "state_matches" } },
	{ effects = pure, evidence = evidence }
)
local _, trueResult = builder:addInstruction(
	trueBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("matched")),
	{ { type = LifterIR.Types.string(), name_hint = "matched" } },
	{ effects = pure, evidence = evidence }
)
local _, falseResult = builder:addInstruction(
	falseBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("other")),
	{ { type = LifterIR.Types.string(), name_hint = "other" } },
	{ effects = pure, evidence = evidence }
)
local _, exported = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(probe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "relational_dispatch" } },
	{ effects = pure, evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exported[1] }))
builder:finalizeBlock(
	entryBlock,
	LifterIR.Terminator.branch(selector, LifterIR.Edge(leftBlock), LifterIR.Edge(rightBlock))
)
builder:finalizeBlock(leftBlock, LifterIR.Terminator.jump(LifterIR.Edge(dispatchBlock, { leftState[1] })))
builder:finalizeBlock(rightBlock, LifterIR.Terminator.jump(LifterIR.Edge(dispatchBlock, { rightState[1] })))
builder:finalizeBlock(
	dispatchBlock,
	LifterIR.Terminator.branch(dispatchCondition[1], LifterIR.Edge(trueBlock), LifterIR.Edge(falseBlock))
)
builder:finalizeBlock(trueBlock, LifterIR.Terminator.returnValues({ trueResult[1] }))
builder:finalizeBlock(falseBlock, LifterIR.Terminator.returnValues({ falseResult[1] }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(probe)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
