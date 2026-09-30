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

local function auditResolved(path: string, reresolvedPath: string, engine: string)
	assert(engine == "internal" or engine == "z3", "expected a solver engine")
	local encoded = fs.readFile(path)
	assert(encoded == fs.readFile(reresolvedPath), "resolved loop IR is not byte-idempotent")
	local program: any = serde.decode("json", encoded)

	local witness: any = nil
	local witnessCount = 0
	for _, obligation in program.obligations do
		local subject = obligation.subject.control_branch
		if subject ~= nil then
			witnessCount += 1
			witness = obligation
		end
	end
	assert(witnessCount == 1, "expected one authenticated loop branch witness")
	assert(witness.status == "discharged", "loop branch witness is not discharged")
	assert(#witness.evidence > 0, "loop branch witness lost its provenance")

	local subject = witness.subject.control_branch
	local block = program.blocks[subject.block + 1]
	assert(block ~= nil and block.id == subject.block, "loop branch witness names an invalid block")
	local jump = block.terminator.jump
	assert(jump ~= nil, "proved loop branch was not consumed")
	assert(jump.target == subject.branch.then_edge.target, "loop branch selected the wrong successor")
	assert(sameArray(jump.arguments, subject.branch.then_edge.arguments), "loop branch changed selected edge arguments")

	local certificate = program.certificates[witness.certificate + 1]
	assert(certificate ~= nil and certificate.resolution == "proved", "loop branch certificate is not proved")
	assert(certificate.query == witness.query, "loop branch certificate changed query identity")
	assert(
		certificate.engine == (if engine == "z3" then "z3" else "internal_facts"),
		"loop branch witness used the wrong solver engine"
	)
	assert(
		string.sub(certificate.certificate_digest, 1, #"sha256:lifter-proof-v9:") == "sha256:lifter-proof-v9:",
		"loop branch witness does not use the authenticated branch digest"
	)

	local jumpScopes = 0
	for _, constraint in program.constraints do
		local edge = constraint.scope.edge
		if edge ~= nil and edge.source == subject.block and edge.kind == "jump" and edge.target == jump.target then
			jumpScopes += 1
		end
	end
	assert(jumpScopes == 1, "current selected jump scope was not materialized exactly once")
end

if process.args[1] == "audit" then
	local resolvedPath = process.args[2]
	local reresolvedPath = process.args[3]
	local engine = process.args[4]
	assert(resolvedPath ~= nil and resolvedPath ~= "", "expected a resolved IR path")
	assert(reresolvedPath ~= nil and reresolvedPath ~= "", "expected a re-resolved IR path")
	assert(engine ~= nil, "expected the selected solver engine")
	auditResolved(resolvedPath, reresolvedPath, engine)
	return
end

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output JSON path")

local builder = LifterIR.Builder.new("generic-luau-loop-topologies")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-luau-loop-topologies")
local evidence = { proof }
local pure = LifterIR.Effects.pure()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local exercise = builder:reserveFunction({ name_hint = "exercise_loops", evidence = evidence })
local terminalRegion = builder:reserveFunction({ name_hint = "terminal_region_loop", evidence = evidence })
local infiniteLoop = builder:reserveFunction({ name_hint = "infinite_branch_loop", evidence = evidence })
local nestedLoops: number
do
	nestedLoops = builder:reserveFunction({ name_hint = "nested_loops", evidence = evidence })
	local input = builder:addParameter(nestedLoops, LifterIR.Types.number(), "nested_input")
	local entry = builder:reserveBlock(nestedLoops, { evidence = evidence })
	local outerHeader = builder:reserveBlock(nestedLoops, { evidence = evidence })
	local innerEntry = builder:reserveBlock(nestedLoops, { evidence = evidence })
	local innerHeader = builder:reserveBlock(nestedLoops, { evidence = evidence })
	local innerBody = builder:reserveBlock(nestedLoops, { evidence = evidence })
	local outerStep = builder:reserveBlock(nestedLoops, { evidence = evidence })
	local exitBlock = builder:reserveBlock(nestedLoops, { evidence = evidence })
	local outerValue = builder:addBlockParameter(outerHeader, LifterIR.Types.number(), "outer_value")
	local outerCounter = builder:addBlockParameter(outerHeader, LifterIR.Types.integer(), "outer_counter")
	local innerEntryValue = builder:addBlockParameter(innerEntry, LifterIR.Types.number(), "inner_entry_value")
	local innerEntryOuterCounter = builder:addBlockParameter(innerEntry, LifterIR.Types.integer(), "inner_entry_outer_counter")
	local innerValue = builder:addBlockParameter(innerHeader, LifterIR.Types.number(), "inner_value")
	local innerCounter = builder:addBlockParameter(innerHeader, LifterIR.Types.integer(), "inner_counter")
	local innerOuterCounter = builder:addBlockParameter(innerHeader, LifterIR.Types.integer(), "inner_outer_counter")
	local bodyValue = builder:addBlockParameter(innerBody, LifterIR.Types.number(), "inner_body_value")
	local bodyCounter = builder:addBlockParameter(innerBody, LifterIR.Types.integer(), "inner_body_counter")
	local bodyOuterCounter = builder:addBlockParameter(innerBody, LifterIR.Types.integer(), "inner_body_outer_counter")
	local stepValue = builder:addBlockParameter(outerStep, LifterIR.Types.number(), "outer_step_value")
	local stepCounter = builder:addBlockParameter(outerStep, LifterIR.Types.integer(), "outer_step_counter")
	local returned = builder:addBlockParameter(exitBlock, LifterIR.Types.number(), "nested_returned")
	builder:setFunctionEntry(nestedLoops, entry)

	local _, zeroResults = builder:addInstruction(
		entry,
		LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
		{ { type = LifterIR.Types.integer(), name_hint = "nested_zero" } },
		{ effects = pure, evidence = evidence }
	)
	local _, outerLimitResults = builder:addInstruction(
		outerHeader,
		LifterIR.Operation.constant(LifterIR.Literal.integer("2")),
		{ { type = LifterIR.Types.integer(), name_hint = "outer_limit" } },
		{ effects = pure, evidence = evidence }
	)
	local _, outerFinishedResults = builder:addInstruction(
		outerHeader,
		LifterIR.Operation.binary("greater_equal", outerCounter, outerLimitResults[1]),
		{ { type = LifterIR.Types.boolean(), name_hint = "outer_finished" } },
		{ effects = pure, evidence = evidence }
	)
	local _, innerZeroResults = builder:addInstruction(
		innerEntry,
		LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
		{ { type = LifterIR.Types.integer(), name_hint = "inner_zero" } },
		{ effects = pure, evidence = evidence }
	)
	local _, innerLimitResults = builder:addInstruction(
		innerHeader,
		LifterIR.Operation.constant(LifterIR.Literal.integer("2")),
		{ { type = LifterIR.Types.integer(), name_hint = "inner_limit" } },
		{ effects = pure, evidence = evidence }
	)
	local _, innerFinishedResults = builder:addInstruction(
		innerHeader,
		LifterIR.Operation.binary("greater_equal", innerCounter, innerLimitResults[1]),
		{ { type = LifterIR.Types.boolean(), name_hint = "inner_finished" } },
		{ effects = pure, evidence = evidence }
	)
	local _, innerIncrementResults = builder:addInstruction(
		innerBody,
		LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
		{ { type = LifterIR.Types.integer(), name_hint = "inner_increment" } },
		{ effects = pure, evidence = evidence }
	)
	local _, innerNextResults = builder:addInstruction(
		innerBody,
		LifterIR.Operation.binary("add", bodyCounter, innerIncrementResults[1]),
		{ { type = LifterIR.Types.integer(), name_hint = "inner_next" } },
		{ effects = pure, evidence = evidence }
	)
	local _, outerIncrementResults = builder:addInstruction(
		outerStep,
		LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
		{ { type = LifterIR.Types.integer(), name_hint = "outer_increment" } },
		{ effects = pure, evidence = evidence }
	)
	local _, outerNextResults = builder:addInstruction(
		outerStep,
		LifterIR.Operation.binary("add", stepCounter, outerIncrementResults[1]),
		{ { type = LifterIR.Types.integer(), name_hint = "outer_next" } },
		{ effects = pure, evidence = evidence }
	)

	builder:finalizeBlock(entry, LifterIR.Terminator.jump(LifterIR.Edge(outerHeader, { input, zeroResults[1] })))
	builder:finalizeBlock(
		outerHeader,
		LifterIR.Terminator.branch(
			outerFinishedResults[1],
			LifterIR.Edge(exitBlock, { outerValue }),
			LifterIR.Edge(innerEntry, { outerValue, outerCounter })
		)
	)
	builder:finalizeBlock(
		innerEntry,
		LifterIR.Terminator.jump(LifterIR.Edge(innerHeader, { innerEntryValue, innerZeroResults[1], innerEntryOuterCounter }))
	)
	builder:finalizeBlock(
		innerHeader,
		LifterIR.Terminator.branch(
			innerFinishedResults[1],
			LifterIR.Edge(outerStep, { innerValue, innerOuterCounter }),
			LifterIR.Edge(innerBody, { innerValue, innerCounter, innerOuterCounter })
		)
	)
	builder:finalizeBlock(
		innerBody,
		LifterIR.Terminator.jump(LifterIR.Edge(innerHeader, { bodyValue, innerNextResults[1], bodyOuterCounter }))
	)
	builder:finalizeBlock(
		outerStep,
		LifterIR.Terminator.jump(LifterIR.Edge(outerHeader, { stepValue, outerNextResults[1] }))
	)
	builder:finalizeBlock(exitBlock, LifterIR.Terminator.returnValues({ returned }))
	builder:finalizeFunction(nestedLoops)
end

local exerciseInput = builder:addParameter(exercise, LifterIR.Types.number(), "input")
local terminalInput = builder:addParameter(terminalRegion, LifterIR.Types.number(), "terminal_input")

local chunkBlock = builder:reserveBlock(chunk, { evidence = evidence })

local exerciseEntry = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseHeader = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseLeft = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseLeftLatch = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseRightDecision = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseCleanup = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseRight = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseExit = builder:reserveBlock(exercise, { evidence = evidence })

local exerciseValue = builder:addBlockParameter(exerciseHeader, LifterIR.Types.number(), "exercise_value")
local exerciseCounter = builder:addBlockParameter(exerciseHeader, LifterIR.Types.integer(), "exercise_counter")
local leftValue = builder:addBlockParameter(exerciseLeft, LifterIR.Types.number(), "left_value")
local leftCounter = builder:addBlockParameter(exerciseLeft, LifterIR.Types.integer(), "left_counter")
local leftLatchValue = builder:addBlockParameter(exerciseLeftLatch, LifterIR.Types.number(), "left_latch_value")
local leftLatchCounter = builder:addBlockParameter(exerciseLeftLatch, LifterIR.Types.integer(), "left_latch_counter")
local rightDecisionValue = builder:addBlockParameter(exerciseRightDecision, LifterIR.Types.number(), "right_decision_value")
local rightDecisionCounter = builder:addBlockParameter(exerciseRightDecision, LifterIR.Types.integer(), "right_decision_counter")
local cleanupValue = builder:addBlockParameter(exerciseCleanup, LifterIR.Types.number(), "cleanup_value")
local rightValue = builder:addBlockParameter(exerciseRight, LifterIR.Types.number(), "right_value")
local rightCounter = builder:addBlockParameter(exerciseRight, LifterIR.Types.integer(), "right_counter")
local exerciseReturned = builder:addBlockParameter(exerciseExit, LifterIR.Types.number(), "exercise_returned")

local terminalEntry = builder:reserveBlock(terminalRegion, { evidence = evidence })
local terminalHeader = builder:reserveBlock(terminalRegion, { evidence = evidence })
local terminalDecision = builder:reserveBlock(terminalRegion, { evidence = evidence })
local terminalBody = builder:reserveBlock(terminalRegion, { evidence = evidence })
local terminalLatch = builder:reserveBlock(terminalRegion, { evidence = evidence })
local terminalReturn = builder:reserveBlock(terminalRegion, { evidence = evidence })
local terminalExit = builder:reserveBlock(terminalRegion, { evidence = evidence })

local terminalValue = builder:addBlockParameter(terminalHeader, LifterIR.Types.number(), "terminal_value")
local terminalCounter = builder:addBlockParameter(terminalHeader, LifterIR.Types.integer(), "terminal_counter")
local decisionValue = builder:addBlockParameter(terminalDecision, LifterIR.Types.number(), "decision_value")
local decisionCounter = builder:addBlockParameter(terminalDecision, LifterIR.Types.integer(), "decision_counter")
local terminalBodyValue = builder:addBlockParameter(terminalBody, LifterIR.Types.number(), "terminal_body_value")
local terminalBodyCounter = builder:addBlockParameter(terminalBody, LifterIR.Types.integer(), "terminal_body_counter")
local terminalLatchValue = builder:addBlockParameter(terminalLatch, LifterIR.Types.number(), "terminal_latch_value")
local terminalLatchCounter = builder:addBlockParameter(terminalLatch, LifterIR.Types.integer(), "terminal_latch_counter")
local earlyReturned = builder:addBlockParameter(terminalReturn, LifterIR.Types.number(), "early_returned")
local exhaustedReturned = builder:addBlockParameter(terminalExit, LifterIR.Types.number(), "exhausted_returned")

local infiniteEntry = builder:reserveBlock(infiniteLoop, { evidence = evidence })
local infiniteHeader = builder:reserveBlock(infiniteLoop, { evidence = evidence })
local infiniteLeft = builder:reserveBlock(infiniteLoop, { evidence = evidence })
local infiniteRight = builder:reserveBlock(infiniteLoop, { evidence = evidence })
local infiniteCounter = builder:addBlockParameter(infiniteHeader, LifterIR.Types.integer(), "infinite_counter")
local infiniteLeftCounter = builder:addBlockParameter(infiniteLeft, LifterIR.Types.integer(), "infinite_left_counter")
local infiniteRightCounter = builder:addBlockParameter(infiniteRight, LifterIR.Types.integer(), "infinite_right_counter")

builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(exercise, exerciseEntry)
builder:setFunctionEntry(terminalRegion, terminalEntry)
builder:setFunctionEntry(infiniteLoop, infiniteEntry)

local _, exportedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(exercise),
	{ { type = LifterIR.Types.functionValue(), name_hint = "exported" } },
	{ effects = pure, evidence = evidence }
)

local _, nestedReferenceResults = builder:addInstruction(
	exerciseEntry,
	LifterIR.Operation.functionRef(nestedLoops),
	{ { type = LifterIR.Types.functionValue(), name_hint = "nested_loops" } },
	{ effects = pure, evidence = evidence }
)
local _, nestedResults = builder:addInstruction(
	exerciseEntry,
	LifterIR.Operation.call(nestedReferenceResults[1], { exerciseInput }, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.number(), name_hint = "nested_result" } },
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local _, terminalReferenceResults = builder:addInstruction(
	exerciseEntry,
	LifterIR.Operation.functionRef(terminalRegion),
	{ { type = LifterIR.Types.functionValue(), name_hint = "terminal_region_loop" } },
	{ effects = pure, evidence = evidence }
)
local _, preparedResults = builder:addInstruction(
	exerciseEntry,
	LifterIR.Operation.call(terminalReferenceResults[1], { nestedResults[1] }, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.number(), name_hint = "prepared" } },
	{ effects = LifterIR.Effects.dynamicCall(), evidence = evidence }
)
local _, exerciseZeroResults = builder:addInstruction(
	exerciseEntry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = LifterIR.Types.integer(), name_hint = "exercise_zero" } },
	{ effects = pure, evidence = evidence }
)
local _, headerZeroResults = builder:addInstruction(
	exerciseHeader,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = LifterIR.Types.integer(), name_hint = "header_zero" } },
	{ effects = pure, evidence = evidence }
)
local _, selectLeftResults = builder:addInstruction(
	exerciseHeader,
	LifterIR.Operation.binary("equal", exerciseCounter, headerZeroResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "select_left" } },
	{ effects = pure, evidence = evidence }
)
local _, leftStepResults = builder:addInstruction(
	exerciseLeft,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = LifterIR.Types.integer(), name_hint = "left_step" } },
	{ effects = pure, evidence = evidence }
)
local _, leftNextResults = builder:addInstruction(
	exerciseLeft,
	LifterIR.Operation.binary("add", leftCounter, leftStepResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "left_next" } },
	{ effects = pure, evidence = evidence }
)
local _, continueEarlyResults = builder:addInstruction(
	exerciseLeft,
	LifterIR.Operation.binary("equal", leftCounter, headerZeroResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "continue_early" } },
	{ effects = pure, evidence = evidence }
)
local _, leftLimitResults = builder:addInstruction(
	exerciseLeftLatch,
	LifterIR.Operation.constant(LifterIR.Literal.integer("4")),
	{ { type = LifterIR.Types.integer(), name_hint = "left_limit" } },
	{ effects = pure, evidence = evidence }
)
local _, leftFinishedResults = builder:addInstruction(
	exerciseLeftLatch,
	LifterIR.Operation.binary("greater_equal", leftLatchCounter, leftLimitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "left_finished" } },
	{ effects = pure, evidence = evidence }
)
local _, breakLimitResults = builder:addInstruction(
	exerciseRightDecision,
	LifterIR.Operation.constant(LifterIR.Literal.integer("2")),
	{ { type = LifterIR.Types.integer(), name_hint = "break_limit" } },
	{ effects = pure, evidence = evidence }
)
local _, breaksEarlyResults = builder:addInstruction(
	exerciseRightDecision,
	LifterIR.Operation.binary("greater_equal", rightDecisionCounter, breakLimitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "breaks_early" } },
	{ effects = pure, evidence = evidence }
)
local _, cleanupZeroResults = builder:addInstruction(
	exerciseCleanup,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = LifterIR.Types.integer(), name_hint = "cleanup_zero" } },
	{ effects = pure, evidence = evidence }
)
local _, cleanedValueResults = builder:addInstruction(
	exerciseCleanup,
	LifterIR.Operation.binary("add", cleanupValue, cleanupZeroResults[1]),
	{ { type = LifterIR.Types.number(), name_hint = "cleaned_value" } },
	{ effects = pure, evidence = evidence }
)
local _, rightStepResults = builder:addInstruction(
	exerciseRight,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = LifterIR.Types.integer(), name_hint = "right_step" } },
	{ effects = pure, evidence = evidence }
)
local _, rightNextResults = builder:addInstruction(
	exerciseRight,
	LifterIR.Operation.binary("add", rightCounter, rightStepResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "right_next" } },
	{ effects = pure, evidence = evidence }
)
local _, rightLimitResults = builder:addInstruction(
	exerciseRight,
	LifterIR.Operation.constant(LifterIR.Literal.integer("4")),
	{ { type = LifterIR.Types.integer(), name_hint = "right_limit" } },
	{ effects = pure, evidence = evidence }
)
local _, rightFinishedResults = builder:addInstruction(
	exerciseRight,
	LifterIR.Operation.binary("greater_equal", rightNextResults[1], rightLimitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "right_finished" } },
	{ effects = pure, evidence = evidence }
)

local _, terminalZeroResults = builder:addInstruction(
	terminalEntry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = LifterIR.Types.integer(), name_hint = "terminal_zero" } },
	{ effects = pure, evidence = evidence }
)
local _, returnLimitResults = builder:addInstruction(
	terminalDecision,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = LifterIR.Types.integer(), name_hint = "return_limit" } },
	{ effects = pure, evidence = evidence }
)
local _, returnsEarlyResults = builder:addInstruction(
	terminalDecision,
	LifterIR.Operation.binary("greater_equal", decisionCounter, returnLimitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "returns_early" } },
	{ effects = pure, evidence = evidence }
)
local _, terminalStepResults = builder:addInstruction(
	terminalBody,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = LifterIR.Types.integer(), name_hint = "terminal_step" } },
	{ effects = pure, evidence = evidence }
)
local _, terminalNextResults = builder:addInstruction(
	terminalBody,
	LifterIR.Operation.binary("add", terminalBodyCounter, terminalStepResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "terminal_next" } },
	{ effects = pure, evidence = evidence }
)
local _, terminalLimitResults = builder:addInstruction(
	terminalLatch,
	LifterIR.Operation.constant(LifterIR.Literal.integer("3")),
	{ { type = LifterIR.Types.integer(), name_hint = "terminal_limit" } },
	{ effects = pure, evidence = evidence }
)
local _, terminalFinishedResults = builder:addInstruction(
	terminalLatch,
	LifterIR.Operation.binary("greater_equal", terminalLatchCounter, terminalLimitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "terminal_finished" } },
	{ effects = pure, evidence = evidence }
)

local _, infiniteZeroResults = builder:addInstruction(
	infiniteEntry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = LifterIR.Types.integer(), name_hint = "infinite_zero" } },
	{ effects = pure, evidence = evidence }
)
local _, infiniteSelectResults = builder:addInstruction(
	infiniteHeader,
	LifterIR.Operation.binary("equal", infiniteCounter, infiniteCounter),
	{ { type = LifterIR.Types.boolean(), name_hint = "infinite_select" } },
	{ effects = pure, evidence = evidence }
)
local _, infiniteLeftStepResults = builder:addInstruction(
	infiniteLeft,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = LifterIR.Types.integer(), name_hint = "infinite_left_step" } },
	{ effects = pure, evidence = evidence }
)
local _, infiniteLeftNextResults = builder:addInstruction(
	infiniteLeft,
	LifterIR.Operation.binary("add", infiniteLeftCounter, infiniteLeftStepResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "infinite_left_next" } },
	{ effects = pure, evidence = evidence }
)
local _, infiniteRightStepResults = builder:addInstruction(
	infiniteRight,
	LifterIR.Operation.constant(LifterIR.Literal.integer("2")),
	{ { type = LifterIR.Types.integer(), name_hint = "infinite_right_step" } },
	{ effects = pure, evidence = evidence }
)
local _, infiniteRightNextResults = builder:addInstruction(
	infiniteRight,
	LifterIR.Operation.binary("add", infiniteRightCounter, infiniteRightStepResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "infinite_right_next" } },
	{ effects = pure, evidence = evidence }
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportedResults[1] }))
builder:finalizeBlock(
	exerciseEntry,
	LifterIR.Terminator.jump(LifterIR.Edge(exerciseHeader, { preparedResults[1], exerciseZeroResults[1] }))
)
builder:finalizeBlock(
	exerciseHeader,
	LifterIR.Terminator.branch(
		selectLeftResults[1],
		LifterIR.Edge(exerciseLeft, { exerciseValue, exerciseCounter }),
		LifterIR.Edge(exerciseRightDecision, { exerciseValue, exerciseCounter })
	)
)
builder:finalizeBlock(
	exerciseLeft,
	LifterIR.Terminator.branch(
		continueEarlyResults[1],
		LifterIR.Edge(exerciseHeader, { leftValue, leftNextResults[1] }),
		LifterIR.Edge(exerciseLeftLatch, { leftValue, leftNextResults[1] })
	)
)
builder:finalizeBlock(
	exerciseLeftLatch,
	LifterIR.Terminator.branch(
		leftFinishedResults[1],
		LifterIR.Edge(exerciseExit, { leftLatchValue }),
		LifterIR.Edge(exerciseHeader, { leftLatchValue, leftLatchCounter })
	)
)
builder:finalizeBlock(
	exerciseRightDecision,
	LifterIR.Terminator.branch(
		breaksEarlyResults[1],
		LifterIR.Edge(exerciseCleanup, { rightDecisionValue }),
		LifterIR.Edge(exerciseRight, { rightDecisionValue, rightDecisionCounter })
	)
)
builder:finalizeBlock(
	exerciseCleanup,
	LifterIR.Terminator.jump(LifterIR.Edge(exerciseExit, { cleanedValueResults[1] }))
)
builder:finalizeBlock(
	exerciseRight,
	LifterIR.Terminator.branch(
		rightFinishedResults[1],
		LifterIR.Edge(exerciseExit, { rightValue }),
		LifterIR.Edge(exerciseHeader, { rightValue, rightNextResults[1] })
	)
)
builder:finalizeBlock(exerciseExit, LifterIR.Terminator.returnValues({ exerciseReturned }))

builder:finalizeBlock(
	terminalEntry,
	LifterIR.Terminator.jump(LifterIR.Edge(terminalHeader, { terminalInput, terminalZeroResults[1] }))
)
builder:finalizeBlock(
	terminalHeader,
	LifterIR.Terminator.jump(LifterIR.Edge(terminalDecision, { terminalValue, terminalCounter }))
)
builder:finalizeBlock(
	terminalDecision,
	LifterIR.Terminator.branch(
		returnsEarlyResults[1],
		LifterIR.Edge(terminalReturn, { decisionValue }),
		LifterIR.Edge(terminalBody, { decisionValue, decisionCounter })
	)
)
builder:finalizeBlock(
	terminalBody,
	LifterIR.Terminator.jump(LifterIR.Edge(terminalLatch, { terminalBodyValue, terminalNextResults[1] }))
)
builder:finalizeBlock(
	terminalLatch,
	LifterIR.Terminator.branch(
		terminalFinishedResults[1],
		LifterIR.Edge(terminalExit, { terminalLatchValue }),
		LifterIR.Edge(terminalHeader, { terminalLatchValue, terminalLatchCounter })
	)
)
builder:finalizeBlock(terminalReturn, LifterIR.Terminator.returnValues({ earlyReturned }))
builder:finalizeBlock(terminalExit, LifterIR.Terminator.returnValues({ exhaustedReturned }))

builder:finalizeBlock(
	infiniteEntry,
	LifterIR.Terminator.jump(LifterIR.Edge(infiniteHeader, { infiniteZeroResults[1] }))
)
builder:finalizeBlock(
	infiniteHeader,
	LifterIR.Terminator.branch(
		infiniteSelectResults[1],
		LifterIR.Edge(infiniteLeft, { infiniteCounter }),
		LifterIR.Edge(infiniteRight, { infiniteCounter })
	)
)
builder:finalizeBlock(
	infiniteLeft,
	LifterIR.Terminator.jump(LifterIR.Edge(infiniteHeader, { infiniteLeftNextResults[1] }))
)
builder:finalizeBlock(
	infiniteRight,
	LifterIR.Terminator.jump(LifterIR.Edge(infiniteHeader, { infiniteRightNextResults[1] }))
)

builder:finalizeFunction(chunk)
builder:finalizeFunction(exercise)
builder:finalizeFunction(terminalRegion)
builder:finalizeFunction(infiniteLoop)

local encoded = LifterIR.encodeJson(builder:finish(), true)
local decoded = serde.decode("json", encoded)
assert(decoded.schema_version == "lifter_ir_v1", "serialized schema version did not round-trip")
assert(decoded.program_id == "generic-luau-loop-topologies", "serialized program ID did not round-trip")
fs.writeFile(outputPath, encoded .. "\n")
