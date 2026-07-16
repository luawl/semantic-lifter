--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

if process.args[1] == "audit" then
	local Audit = require("./irreducible_table_audit")
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

local builder = LifterIR.Builder.new("generic-irreducible-table-construction")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-irreducible-table-construction")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local integer = LifterIR.Types.integer()
local tableType = LifterIR.Types.table()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local worker = builder:reserveFunction({
	name_hint = "irreducible_table_worker",
	is_variadic = true,
	evidence = evidence,
})
local chunkBlock = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
local entry = builder:reserveBlock(worker, { name_hint = "entry", evidence = evidence })
local primary = builder:reserveBlock(worker, { name_hint = "loop_header", evidence = evidence })
local secondary = builder:reserveBlock(worker, { name_hint = "table_entry", evidence = evidence })
local exit = builder:reserveBlock(worker, { name_hint = "exit", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(worker, entry)

local startSecondary = builder:addParameter(worker, LifterIR.Types.boolean(), "start_secondary")
local sink = builder:addParameter(worker, tableType, "sink")
local producer = builder:addParameter(worker, LifterIR.Types.functionValue(), "tail_producer")
local workerVarargs = builder:addVarargPack(worker, evidence)
local primaryCounter = builder:addBlockParameter(primary, integer, "counter")
local secondaryCounter = builder:addBlockParameter(secondary, integer, "table_counter")
local exitCounter = builder:addBlockParameter(exit, integer, "final_counter")

local _, exportedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(worker),
	{ { type = LifterIR.Types.functionValue(), name_hint = "irreducible_table_worker" } },
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

local _, nestedKeyResults = builder:addInstruction(
	secondary,
	LifterIR.Operation.constant(LifterIR.Literal.string("nested")),
	{ { type = LifterIR.Types.string(), name_hint = "nested_key" } },
	{ effects = pure, evidence = evidence }
)
local _, emptyKeyResults = builder:addInstruction(
	secondary,
	LifterIR.Operation.constant(LifterIR.Literal.string("empty")),
	{ { type = LifterIR.Types.string(), name_hint = "empty_key" } },
	{ effects = pure, evidence = evidence }
)
local _, resultKeyResults = builder:addInstruction(
	secondary,
	LifterIR.Operation.constant(LifterIR.Literal.string("result")),
	{ { type = LifterIR.Types.string(), name_hint = "result_key" } },
	{ effects = pure, evidence = evidence }
)
local _, emptyTableResults = builder:addInstruction(
	secondary,
	LifterIR.Operation.makeTable(),
	{ { type = tableType, name_hint = "empty_table" } },
	{ effects = LifterIR.Effects.tableConstructor(), evidence = evidence }
)
local _, directTableResults = builder:addInstruction(
	secondary,
	LifterIR.Operation.makeTableLiteral(
		{ LifterIR.TableConstructorField.list(secondaryCounter) },
		workerVarargs
	),
	{ { type = tableType, name_hint = "direct_vararg_table" } },
	{ effects = LifterIR.Effects.tableConstructor(), evidence = evidence }
)
local _, producerPack = builder:addOpenCall(
	secondary,
	producer,
	{ secondaryCounter },
	{
		effects = LifterIR.Effects.dynamicCall(),
		evidence = evidence,
		result_pack_shape = LifterIR.PackShape.open({ integer, LifterIR.Types.nilValue(), integer }),
	}
)
local _, finalTableResults = builder:addInstruction(
	secondary,
	LifterIR.Operation.makeTableLiteral(
		{
			LifterIR.TableConstructorField.list(secondaryCounter),
			LifterIR.TableConstructorField.keyed(nestedKeyResults[1], directTableResults[1]),
			LifterIR.TableConstructorField.keyed(emptyKeyResults[1], emptyTableResults[1]),
		},
		producerPack
	),
	{ { type = tableType, name_hint = "constructed_table" } },
	{ effects = LifterIR.Effects.tableConstructor(), evidence = evidence }
)
builder:addInstruction(
	secondary,
	LifterIR.Operation.tableSet(sink, resultKeyResults[1], finalTableResults[1], "raw"),
	{},
	{ effects = LifterIR.Effects.rawTableWrite(), evidence = evidence }
)
local _, forwardedResults = builder:addInstruction(
	secondary,
	LifterIR.Operation.constant(LifterIR.Literal.integer("2")),
	{ { type = integer, name_hint = "forwarded_counter" } },
	{ effects = pure, evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportedResults[1] }))
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
builder:finalizeFunction(chunk)
builder:finalizeFunction(worker)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
