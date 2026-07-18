--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-luau-shared-place-closure")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-luau-shared-place-closure")
local evidence = { proof }
local pure = LifterIR.Effects.pure()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local factory = builder:reserveFunction({ name_hint = "make_counter", evidence = evidence })
local counter = builder:reserveFunction({
	name_hint = "counter",
	lexical_parent = factory,
	evidence = evidence,
})

local start = builder:addParameter(factory, LifterIR.Types.integer(), "start")
local delta = builder:addParameter(counter, LifterIR.Types.integer(), "delta")
local state = builder:addLocalPlace(factory, LifterIR.Types.integer(), "state", evidence)
local capturedState = builder:addPlaceCapture(counter, LifterIR.Types.integer(), "captured_state", evidence)

local chunkBlock = builder:reserveBlock(chunk, { evidence = evidence })
local factoryBlock = builder:reserveBlock(factory, { evidence = evidence })
local counterBlock = builder:reserveBlock(counter, { evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(factory, factoryBlock)
builder:setFunctionEntry(counter, counterBlock)

local _, exportResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(factory),
	{ { type = LifterIR.Types.functionValue(), name_hint = "factory" } },
	{ effects = pure, evidence = evidence }
)
local exportedFactory = exportResults[1]

builder:addInstruction(
	factoryBlock,
	LifterIR.Operation.placeWrite(state, start),
	{},
	{ effects = LifterIR.Effects.placeWrite(), evidence = evidence }
)
local _, closureResults = builder:addInstruction(
	factoryBlock,
	LifterIR.Operation.makeClosure(counter, { LifterIR.CaptureBinding.place(state) }),
	{ { type = LifterIR.Types.functionValue(), name_hint = "counter" } },
	{ effects = pure, evidence = evidence }
)
local counterClosure = closureResults[1]

local _, readResults = builder:addInstruction(
	counterBlock,
	LifterIR.Operation.placeRead(capturedState),
	{ { type = LifterIR.Types.integer(), name_hint = "current" } },
	{ effects = LifterIR.Effects.placeRead(), evidence = evidence }
)
local current = readResults[1]
local addInstruction, addResults = builder:addInstruction(
	counterBlock,
	LifterIR.Operation.binary("add", current, delta),
	{ { type = LifterIR.Types.integer(), name_hint = "next" } },
	{ effects = pure, evidence = evidence }
)
local nextValue = addResults[1]

local primitiveDomain = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.semanticAtom(LifterIR.SemanticAtom.primitiveOperatorDomain(addInstruction))
)
local primitiveDomainConstraint = builder:addConstraint(primitiveDomain, evidence)
local primitiveDomainQuery = builder:addQuery("prove_true", { primitiveDomainConstraint }, primitiveDomain)
local primitiveDomainClaim = builder:addClaim(
	LifterIR.Entity.instruction(addInstruction),
	primitiveDomain,
	"unproven",
	true,
	evidence,
	nil,
	LifterIR.ClaimPurpose.primitiveOperatorDomain(pure),
	primitiveDomainQuery
)
builder:addInstructionClaim(addInstruction, primitiveDomainClaim)

builder:addInstruction(
	counterBlock,
	LifterIR.Operation.placeWrite(capturedState, nextValue),
	{},
	{ effects = LifterIR.Effects.placeWrite(), evidence = evidence }
)

local currentTerm = builder:addSolverTerm(LifterIR.SolverSort.integer(), LifterIR.SolverTerm.value(current))
local currentIdentity = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("equal", currentTerm, currentTerm)
)
local currentIdentityQuery = builder:addQuery("prove_true", {}, currentIdentity)
builder:addClaim(
	LifterIR.Entity.program(),
	currentIdentity,
	"unproven",
	true,
	evidence,
	nil,
	nil,
	currentIdentityQuery
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportedFactory }))
builder:finalizeBlock(factoryBlock, LifterIR.Terminator.returnValues({ counterClosure }))
builder:finalizeBlock(counterBlock, LifterIR.Terminator.returnValues({ nextValue }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(factory)
builder:finalizeFunction(counter)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
