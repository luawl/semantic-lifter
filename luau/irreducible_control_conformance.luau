--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

if process.args[1] == "audit" then
	local Audit = require("./irreducible_control_audit")
	local inputPath = process.args[2]
	local resolvedPath = process.args[3]
	local reresolvedPath = process.args[4]
	local generatedPath = process.args[5]
	assert(inputPath ~= nil and resolvedPath ~= nil and reresolvedPath ~= nil and generatedPath ~= nil, "expected audit artifacts")
	Audit.run(inputPath, resolvedPath, reresolvedPath, generatedPath)
	return
end

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-finite-irreducible-control")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-finite-irreducible-control")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local integer = LifterIR.Types.integer()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local probe = builder:reserveFunction({ name_hint = "finite_irreducible_loop", evidence = evidence })
local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local entry = builder:reserveBlock(probe, { name_hint = "entry", evidence = evidence })
local primary = builder:reserveBlock(probe, { name_hint = "loop_header", evidence = evidence })
local secondary = builder:reserveBlock(probe, { name_hint = "secondary_entry", evidence = evidence })
local exit = builder:reserveBlock(probe, { name_hint = "exit", evidence = evidence })
local semanticProbe = builder:reserveFunction({
	name_hint = "semantic_irreducible_loop",
	is_variadic = true,
	evidence = evidence,
})
local semanticEntry = builder:reserveBlock(semanticProbe, { name_hint = "entry", evidence = evidence })
local semanticPrimary = builder:reserveBlock(semanticProbe, { name_hint = "loop_header", evidence = evidence })
local semanticSecondary = builder:reserveBlock(semanticProbe, { name_hint = "semantic_secondary_entry", evidence = evidence })
local semanticExit = builder:reserveBlock(semanticProbe, { name_hint = "exit", evidence = evidence })
local selfLoopProbe = builder:reserveFunction({ name_hint = "self_loop_irreducible_loop", evidence = evidence })
local selfLoopEntry = builder:reserveBlock(selfLoopProbe, { name_hint = "entry", evidence = evidence })
local selfLoopPrimary = builder:reserveBlock(selfLoopProbe, { name_hint = "self_loop_primary", evidence = evidence })
local selfLoopSecondary = builder:reserveBlock(selfLoopProbe, { name_hint = "self_loop_secondary", evidence = evidence })
local selfLoopExit = builder:reserveBlock(selfLoopProbe, { name_hint = "exit", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(probe, entry)
builder:setFunctionEntry(semanticProbe, semanticEntry)
builder:setFunctionEntry(selfLoopProbe, selfLoopEntry)

local startSecondary = builder:addParameter(probe, LifterIR.Types.boolean(), "start_secondary")
local primaryCounter = builder:addBlockParameter(primary, integer, "counter")
local secondaryCounter = builder:addBlockParameter(secondary, integer, "forwarded_counter")
local exitCounter = builder:addBlockParameter(exit, integer, "final_counter")
local semanticStartSecondary = builder:addParameter(semanticProbe, LifterIR.Types.boolean(), "start_secondary")
local semanticTable = builder:addParameter(semanticProbe, LifterIR.Types.table(), "source_table")
local semanticKey = builder:addParameter(semanticProbe, LifterIR.Types.string(), "source_key")
local semanticObserver = builder:addParameter(semanticProbe, LifterIR.Types.functionValue(), "observer")
local semanticForwarder = builder:addParameter(semanticProbe, LifterIR.Types.functionValue(), "forwarder")
local semanticNamecallReceiver = builder:addParameter(semanticProbe, LifterIR.Types.table(), "namecall_receiver")
local semanticProtectedSuccessCallee = builder:addParameter(
	semanticProbe,
	LifterIR.Types.functionValue(),
	"protected_success_callee"
)
local semanticProtectedCallee = builder:addParameter(semanticProbe, LifterIR.Types.functionValue(), "protected_callee")
local semanticErrorHandler = builder:addParameter(semanticProbe, LifterIR.Types.functionValue(), "error_handler")
local semanticVarargs = builder:addVarargPack(semanticProbe, evidence)
local semanticPlace = builder:addLocalPlace(semanticProbe, integer, "semantic_cell", evidence)
local semanticPrimaryCounter = builder:addBlockParameter(semanticPrimary, integer, "semantic_counter")
local semanticSecondaryCounter = builder:addBlockParameter(semanticSecondary, integer, "semantic_forwarded_counter")
local semanticExitCounter = builder:addBlockParameter(semanticExit, integer, "semantic_final_counter")
local selfLoopStartSecondary = builder:addParameter(selfLoopProbe, LifterIR.Types.boolean(), "start_secondary")
local selfLoopStartCounter = builder:addParameter(selfLoopProbe, integer, "start_counter")
local selfLoopPrimaryCounter = builder:addBlockParameter(selfLoopPrimary, integer, "self_loop_primary_counter")
local selfLoopSecondaryCounter = builder:addBlockParameter(selfLoopSecondary, integer, "self_loop_secondary_counter")
local selfLoopExitCounter = builder:addBlockParameter(selfLoopExit, integer, "self_loop_final_counter")
local _, exportedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(probe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "finite_irreducible_loop" } },
	{ effects = pure, evidence = evidence }
)
local _, semanticExportedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(semanticProbe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "semantic_irreducible_loop" } },
	{ effects = pure, evidence = evidence }
)
local _, selfLoopExportedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(selfLoopProbe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "self_loop_irreducible_loop" } },
	{ effects = pure, evidence = evidence }
)
local _, zeroResults = builder:addInstruction(
	entry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = integer, name_hint = "zero" } },
	{ effects = pure, evidence = evidence }
)
local _, oneResults = builder:addInstruction(
	primary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = integer, name_hint = "one" } },
	{ effects = pure, evidence = evidence }
)
local _, nextResults = builder:addInstruction(
	primary,
	LifterIR.Operation.binary("add", primaryCounter, oneResults[1]),
	{ { type = integer, name_hint = "next_counter" } },
	{ effects = pure, evidence = evidence }
)
local _, limitResults = builder:addInstruction(
	primary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("3")),
	{ { type = integer, name_hint = "limit" } },
	{ effects = pure, evidence = evidence }
)
local _, continueResults = builder:addInstruction(
	primary,
	LifterIR.Operation.binary("less", nextResults[1], limitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "continue_loop" } },
	{ effects = pure, evidence = evidence }
)
local _, forwardedResults = builder:addInstruction(
	secondary,
	LifterIR.Operation.copy(secondaryCounter),
	{ { type = integer, name_hint = "forwarded_copy" } },
	{ effects = pure, evidence = evidence }
)
local _, semanticZeroResults = builder:addInstruction(
	semanticEntry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = integer, name_hint = "semantic_zero" } },
	{ effects = pure, evidence = evidence }
)
local _, semanticPlaceInitialResults = builder:addInstruction(
	semanticEntry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("3")),
	{ { type = integer, name_hint = "semantic_place_initial" } },
	{ effects = pure, evidence = evidence }
)
builder:addInstruction(
	semanticEntry,
	LifterIR.Operation.placeWrite(semanticPlace, semanticPlaceInitialResults[1]),
	{},
	{ effects = LifterIR.Effects.placeWrite(), evidence = evidence }
)
local _, semanticOneResults = builder:addInstruction(
	semanticPrimary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = integer, name_hint = "semantic_one" } },
	{ effects = pure, evidence = evidence }
)
local _, semanticNextResults = builder:addInstruction(
	semanticPrimary,
	LifterIR.Operation.binary("add", semanticPrimaryCounter, semanticOneResults[1]),
	{ { type = integer, name_hint = "semantic_next_counter" } },
	{ effects = pure, evidence = evidence }
)
local _, semanticLimitResults = builder:addInstruction(
	semanticPrimary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("3")),
	{ { type = integer, name_hint = "semantic_limit" } },
	{ effects = pure, evidence = evidence }
)
local _, semanticContinueResults = builder:addInstruction(
	semanticPrimary,
	LifterIR.Operation.binary("less", semanticNextResults[1], semanticLimitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "semantic_continue_loop" } },
	{ effects = pure, evidence = evidence }
)
local _, semanticReadResults = builder:addInstruction(
	semanticSecondary,
	LifterIR.Operation.tableGet(semanticTable, semanticKey, "semantic"),
	{ { type = integer, name_hint = "semantic_read_counter" } },
	{ effects = LifterIR.Effects.semanticTableRead(), evidence = evidence }
)
local _, semanticEnvironmentResults = builder:addInstruction(
	semanticSecondary,
	LifterIR.Operation.environmentGet(LifterIR.EnvironmentTarget.value(semanticTable), "counter", "semantic"),
	{ { type = integer, name_hint = "semantic_environment_counter" } },
	{ effects = LifterIR.Effects.semanticTableRead(), evidence = evidence }
)
local _, semanticNamecallResults = builder:addInstruction(
	semanticSecondary,
	LifterIR.Operation.namecall(
		semanticNamecallReceiver,
		"observe",
		{ semanticSecondaryCounter },
		LifterIR.ResultArity.fixed(1),
		semanticVarargs
	),
	{ { type = integer, name_hint = "semantic_namecall_counter" } },
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local _, semanticProtectedSuccessResults = builder:addInstruction(
	semanticSecondary,
	LifterIR.Operation.protectedCall(
		semanticProtectedSuccessCallee,
		nil,
		{ semanticSecondaryCounter },
		LifterIR.ResultArity.fixed(2),
		semanticVarargs
	),
	{
		{ type = LifterIR.Types.boolean(), name_hint = "semantic_protected_success_ok" },
		{ type = integer, name_hint = "semantic_protected_success_value" },
	},
	{ effects = LifterIR.Effects.protectedInvocation(), evidence = evidence }
)
local _, semanticProtectedPack = builder:addOpenProtectedCall(
	semanticSecondary,
	semanticProtectedCallee,
	semanticErrorHandler,
	{ semanticSecondaryCounter },
	{
		effects = LifterIR.Effects.protectedInvocation(),
		evidence = evidence,
		result_pack_shape = LifterIR.PackShape.open({ LifterIR.Types.boolean(), LifterIR.Types.string() }),
	},
	semanticVarargs
)
local _, semanticProtectedResults = builder:addInstruction(
	semanticSecondary,
	LifterIR.Operation.adjustPack(semanticProtectedPack),
	{
		{ type = LifterIR.Types.boolean(), name_hint = "semantic_protected_ok" },
		{ type = LifterIR.Types.string(), name_hint = "semantic_protected_message" },
	},
	{ effects = pure, evidence = evidence }
)
local _, semanticCallPack = builder:addOpenCall(
	semanticSecondary,
	semanticObserver,
	{
		semanticSecondaryCounter,
		semanticNamecallResults[1],
		semanticProtectedSuccessResults[1],
		semanticProtectedSuccessResults[2],
		semanticProtectedResults[1],
		semanticProtectedResults[2],
	},
	{
		effects = LifterIR.Effects.dynamicCall(),
		evidence = evidence,
		result_pack_shape = LifterIR.PackShape.open({ integer, LifterIR.Types.nilValue(), integer }),
	},
	semanticVarargs
)
local _, semanticForwardedPack = builder:addOpenCall(
	semanticSecondary,
	semanticForwarder,
	{ semanticSecondaryCounter },
	{
		effects = LifterIR.Effects.dynamicCall(),
		evidence = evidence,
		result_pack_shape = LifterIR.PackShape.open({ integer, integer }),
	},
	semanticCallPack
)
local _, semanticCallResults = builder:addInstruction(
	semanticSecondary,
	LifterIR.Operation.adjustPack(semanticForwardedPack),
	{
		{ type = integer, name_hint = "semantic_call_counter" },
		{ type = integer, name_hint = "semantic_call_mirror" },
	},
	{ effects = pure, evidence = evidence }
)
builder:addInstruction(
	semanticSecondary,
	LifterIR.Operation.tableSet(semanticTable, semanticKey, semanticCallResults[1], "semantic"),
	{},
	{ effects = LifterIR.Effects.semanticTableWrite(), evidence = evidence }
)
builder:addInstruction(
	semanticSecondary,
	LifterIR.Operation.environmentSet(
		LifterIR.EnvironmentTarget.value(semanticTable),
		"mirror",
		semanticCallResults[2],
		"semantic"
	),
	{},
	{ effects = LifterIR.Effects.semanticTableWrite(), evidence = evidence }
)
builder:addInstruction(
	semanticSecondary,
	LifterIR.Operation.placeWrite(semanticPlace, semanticCallResults[1]),
	{},
	{ effects = LifterIR.Effects.placeWrite(), evidence = evidence }
)
local _, semanticPlaceResults = builder:addInstruction(
	semanticSecondary,
	LifterIR.Operation.placeRead(semanticPlace),
	{ { type = integer, name_hint = "semantic_place_counter" } },
	{ effects = LifterIR.Effects.placeRead(), evidence = evidence }
)
local _, semanticNegatedResults = builder:addInstruction(
	semanticSecondary,
	LifterIR.Operation.unary("negate", semanticPlaceResults[1]),
	{ { type = integer, name_hint = "semantic_negated_counter" } },
	{ effects = pure, evidence = evidence }
)
local _, semanticForwardedResults = builder:addInstruction(
	semanticSecondary,
	LifterIR.Operation.unary("negate", semanticNegatedResults[1]),
	{ { type = integer, name_hint = "semantic_forwarded_copy" } },
	{ effects = pure, evidence = evidence }
)
local _, selfLoopLimitResults = builder:addInstruction(
	selfLoopPrimary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("3")),
	{ { type = integer, name_hint = "self_loop_limit" } },
	{ effects = pure, evidence = evidence }
)
local _, selfLoopContinueResults = builder:addInstruction(
	selfLoopPrimary,
	LifterIR.Operation.binary("less", selfLoopPrimaryCounter, selfLoopLimitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "self_loop_continue" } },
	{ effects = pure, evidence = evidence }
)
local _, selfLoopOneResults = builder:addInstruction(
	selfLoopSecondary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = integer, name_hint = "self_loop_one" } },
	{ effects = pure, evidence = evidence }
)
local _, selfLoopNextResults = builder:addInstruction(
	selfLoopSecondary,
	LifterIR.Operation.binary("add", selfLoopSecondaryCounter, selfLoopOneResults[1]),
	{ { type = integer, name_hint = "self_loop_next_counter" } },
	{ effects = pure, evidence = evidence }
)
local _, selfLoopRepeatLimitResults = builder:addInstruction(
	selfLoopSecondary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("2")),
	{ { type = integer, name_hint = "self_loop_repeat_limit" } },
	{ effects = pure, evidence = evidence }
)
local _, selfLoopRepeatResults = builder:addInstruction(
	selfLoopSecondary,
	LifterIR.Operation.binary("less", selfLoopNextResults[1], selfLoopRepeatLimitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "self_loop_repeat" } },
	{ effects = pure, evidence = evidence }
)
builder:finalizeBlock(
	chunkBlock,
	LifterIR.Terminator.returnValues({ exportedResults[1], semanticExportedResults[1], selfLoopExportedResults[1] })
)
builder:finalizeBlock(
	entry,
	LifterIR.Terminator.branch(
		startSecondary,
		LifterIR.Edge(secondary, { zeroResults[1] }),
		LifterIR.Edge(primary, { zeroResults[1] })
	)
)
builder:finalizeBlock(
	primary,
	LifterIR.Terminator.branch(
		continueResults[1],
		LifterIR.Edge(secondary, { nextResults[1] }),
		LifterIR.Edge(exit, { nextResults[1] })
	)
)
builder:finalizeBlock(secondary, LifterIR.Terminator.jump(LifterIR.Edge(primary, { forwardedResults[1] })))
builder:finalizeBlock(exit, LifterIR.Terminator.returnValues({ exitCounter }))
builder:finalizeBlock(
	semanticEntry,
	LifterIR.Terminator.branch(
		semanticStartSecondary,
		LifterIR.Edge(semanticSecondary, { semanticZeroResults[1] }),
		LifterIR.Edge(semanticPrimary, { semanticZeroResults[1] })
	)
)
builder:finalizeBlock(
	semanticPrimary,
	LifterIR.Terminator.branch(
		semanticContinueResults[1],
		LifterIR.Edge(semanticSecondary, { semanticNextResults[1] }),
		LifterIR.Edge(semanticExit, { semanticNextResults[1] })
	)
)
builder:finalizeBlock(
	semanticSecondary,
	LifterIR.Terminator.jump(LifterIR.Edge(semanticPrimary, { semanticForwardedResults[1] }))
)
builder:finalizeBlock(semanticExit, LifterIR.Terminator.returnValues({ semanticExitCounter }))
builder:finalizeBlock(
	selfLoopEntry,
	LifterIR.Terminator.branch(
		selfLoopStartSecondary,
		LifterIR.Edge(selfLoopSecondary, { selfLoopStartCounter }),
		LifterIR.Edge(selfLoopPrimary, { selfLoopStartCounter })
	)
)
builder:finalizeBlock(
	selfLoopPrimary,
	LifterIR.Terminator.branch(
		selfLoopContinueResults[1],
		LifterIR.Edge(selfLoopSecondary, { selfLoopPrimaryCounter }),
		LifterIR.Edge(selfLoopExit, { selfLoopPrimaryCounter })
	)
)
builder:finalizeBlock(
	selfLoopSecondary,
	LifterIR.Terminator.branch(
		selfLoopRepeatResults[1],
		LifterIR.Edge(selfLoopSecondary, { selfLoopNextResults[1] }),
		LifterIR.Edge(selfLoopPrimary, { selfLoopNextResults[1] })
	)
)
builder:finalizeBlock(selfLoopExit, LifterIR.Terminator.returnValues({ selfLoopExitCounter }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(probe)
builder:finalizeFunction(semanticProbe)
builder:finalizeFunction(selfLoopProbe)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
