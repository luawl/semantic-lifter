--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output path")

local builder = LifterIR.Builder.new("generic-mixed-entry-varargs")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-mixed-entry-varargs")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local dynamic = LifterIR.Types.dynamic()
local integer = LifterIR.Types.integer()

local chunk = builder:reserveFunction({
	name_hint = "chunk",
	is_variadic = true,
	evidence = evidence,
})
local consumer = builder:addParameter(chunk, LifterIR.Types.functionValue(), "consumer")
local label = builder:addParameter(chunk, LifterIR.Types.string(), "label")
local varargs = builder:addVarargPack(chunk, evidence)
local externalValue = builder:addExternalValueBinding(integer, evidence)
local externalState = builder:addExternalPlaceBinding(integer, evidence)
local capturedValueFirst = builder:addValueCapture(chunk, integer, "captured_value_first", evidence)
local capturedValueSecond = builder:addValueCapture(chunk, integer, "captured_value_second", evidence)
local capturedStateFirst = builder:addPlaceCapture(chunk, integer, "captured_state_first", evidence)
local capturedStateSecond = builder:addPlaceCapture(chunk, integer, "captured_state_second", evidence)
local entry = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidence })
builder:setEntryFunction(chunk)
builder:setEntryBindings({ externalValue, externalValue, externalState, externalState })
builder:setFunctionEntry(chunk, entry)

builder:addInstruction(
	entry,
	LifterIR.Operation.environmentSet(LifterIR.EnvironmentTarget.ambient(), "select", consumer, "semantic"),
	{},
	{ effects = LifterIR.Effects.semanticTableWrite(), evidence = evidence }
)

local _, beforeResults = builder:addInstruction(
	entry,
	LifterIR.Operation.placeRead(capturedStateFirst),
	{ { type = integer, name_hint = "state_before_callback" } },
	{ effects = LifterIR.Effects.placeRead(), evidence = evidence }
)
local stateBeforeCallback = beforeResults[1]

local _, adjusted = builder:addInstruction(
	entry,
	LifterIR.Operation.adjustPack(varargs),
	{
		{ type = dynamic, name_hint = "tail_first" },
		{ type = dynamic, name_hint = "tail_second" },
		{ type = dynamic, name_hint = "tail_third" },
	},
	{ effects = pure, evidence = evidence }
)
local tailFirst = adjusted[1]
local tailSecond = adjusted[2]
local tailThird = adjusted[3]

local _, tableResults = builder:addInstruction(
	entry,
	LifterIR.Operation.makeTableLiteral({ LifterIR.TableConstructorField.list(label) }, varargs),
	{ { type = LifterIR.Types.table(), name_hint = "packed_tail" } },
	{ effects = LifterIR.Effects.tableConstructor(), evidence = evidence }
)
local packedTail = tableResults[1]

local _, callResults = builder:addInstruction(
	entry,
	LifterIR.Operation.call(
		consumer,
		{
			label,
			packedTail,
			tailFirst,
			tailSecond,
			tailThird,
			capturedValueFirst,
			capturedValueSecond,
			stateBeforeCallback,
		},
		LifterIR.ResultArity.fixed(1),
		varargs
	),
	{ { type = LifterIR.Types.functionValue(), name_hint = "probe" } },
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local probe = callResults[1]

local _, callbackResults = builder:addInstruction(
	entry,
	LifterIR.Operation.placeRead(capturedStateSecond),
	{ { type = integer, name_hint = "state_after_callback" } },
	{ effects = LifterIR.Effects.placeRead(), evidence = evidence }
)
local stateAfterCallback = callbackResults[1]

builder:addInstruction(
	entry,
	LifterIR.Operation.placeWrite(capturedStateFirst, capturedValueFirst),
	{},
	{ effects = LifterIR.Effects.placeWrite(), evidence = evidence }
)

local _, writeResults = builder:addInstruction(
	entry,
	LifterIR.Operation.placeRead(capturedStateSecond),
	{ { type = integer, name_hint = "state_after_write" } },
	{ effects = LifterIR.Effects.placeRead(), evidence = evidence }
)
local stateAfterWrite = writeResults[1]

builder:finalizeBlock(
	entry,
	LifterIR.Terminator.returnExpanded(
		{
			probe,
			packedTail,
			tailFirst,
			tailSecond,
			tailThird,
			capturedValueFirst,
			capturedValueSecond,
			stateBeforeCallback,
			stateAfterCallback,
			stateAfterWrite,
		},
		varargs
	)
)
builder:finalizeFunction(chunk)

fs.writeFile(outputPath, LifterIR.encodeJson(builder:finish(), true) .. "\n")
