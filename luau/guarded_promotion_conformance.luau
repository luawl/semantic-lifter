--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")

local LifterIR = require("./lifter_ir")

local mode = process.args[1]
assert(mode ~= nil and mode ~= "", "expected an output path or audit mode")

if mode == "audit" then
	local resolvedPath = process.args[2]
	local generatedPath = process.args[3]
	local expectedEngine = process.args[4]
	assert(resolvedPath ~= nil and generatedPath ~= nil and expectedEngine ~= nil, "expected resolved IR, generated Luau, and engine")
	local resolved = serde.decode("json", fs.readFile(resolvedPath))
	local shiftedValue = nil
	local conditionValue = nil
	local numericConditionValue = nil
	local unguardedNumericConditionValue = nil
	for _, value in resolved.values do
		if value.name_hint == "shifted" then
			shiftedValue = value.id
		elseif value.name_hint == "shift_identity" then
			conditionValue = value.id
		elseif value.name_hint == "numeric_identity" then
			numericConditionValue = value.id
		elseif value.name_hint == "unguarded_numeric_inequality" then
			unguardedNumericConditionValue = value.id
		end
	end
	assert(
		shiftedValue ~= nil
			and conditionValue ~= nil
			and numericConditionValue ~= nil
			and unguardedNumericConditionValue ~= nil,
		"guarded promotion values were not preserved"
	)

	local shiftDefinition = nil
	local conditionDefinition = nil
	local numericConditionDefinition = nil
	local unguardedNumericConditionDefinition = nil
	for _, term in resolved.solver_terms do
		local definition = term.operation.value_definition
		if definition ~= nil and definition.value == shiftedValue then
			shiftDefinition = term
		elseif definition ~= nil and definition.value == conditionValue then
			conditionDefinition = term
		elseif definition ~= nil and definition.value == numericConditionValue then
			numericConditionDefinition = term
		elseif definition ~= nil and definition.value == unguardedNumericConditionValue then
			unguardedNumericConditionDefinition = term
		end
	end
	assert(shiftDefinition ~= nil, "Zig did not promote the variable shift")
	assert(conditionDefinition ~= nil, "Zig did not promote the guarded branch condition")
	assert(numericConditionDefinition ~= nil, "Zig did not promote guarded numeric equality")
	assert(unguardedNumericConditionDefinition ~= nil, "Zig did not promote total unguarded numeric inequality")
	assert(shiftDefinition.operation.value_definition.valid_when == 2, "promoted shift did not reuse the admitted guard")

	local function totalNumericGuard(definitionTerm, sourceOperator: string): number
		local definition = definitionTerm.operation.value_definition
		assert(definition.valid_when == nil, "total numeric equality retained a partial-definition precondition")
		local expression = resolved.solver_terms[definition.expression + 1]
		if sourceOperator == "not_equal" then
			local totalEquality = expression.operation.logical_not
			assert(totalEquality ~= nil, "numeric inequality is not the exact negation of total equality")
			expression = resolved.solver_terms[totalEquality + 1]
		end
		local conjunction = expression.operation.binary
		assert(conjunction ~= nil and conjunction.operator == "logical_and", "numeric equality lost its total NaN formula")
		local rawEquality = resolved.solver_terms[conjunction.right + 1].operation.binary
		assert(rawEquality ~= nil and rawEquality.operator == "equal", "numeric equality lost its dynamic value relation")
		return conjunction.left
	end

	assert(totalNumericGuard(numericConditionDefinition, "equal") == 6, "numeric equality did not reuse the admitted NaN guard")
	totalNumericGuard(unguardedNumericConditionDefinition, "not_equal")

	local guardedShiftQuery = nil
	local guardedShiftNegatedQuery = nil
	local guardedNumericQuery = nil
	local guardedNumericNegatedQuery = nil
	local hasUnguardedNumericQuery = false
	for _, query in resolved.queries do
		local goal = resolved.solver_terms[query.goal + 1]
		local negatedGoal = goal.operation.logical_not
		if query.goal == conditionDefinition.id then
			for _, assumption in query.assumptions do
				if assumption == 0 then
					guardedShiftQuery = query
				end
			end
		elseif negatedGoal == conditionDefinition.id then
			guardedShiftNegatedQuery = query
		elseif query.goal == numericConditionDefinition.id then
			for _, assumption in query.assumptions do
				if assumption == 1 then
					guardedNumericQuery = query
				end
			end
		elseif negatedGoal == numericConditionDefinition.id then
			guardedNumericNegatedQuery = query
		elseif query.goal == unguardedNumericConditionDefinition.id
			or negatedGoal == unguardedNumericConditionDefinition.id
		then
			hasUnguardedNumericQuery = true
		end
	end
	assert(guardedShiftQuery ~= nil, "generated control query omitted the shift guard assumption")
	assert(guardedShiftNegatedQuery ~= nil, "generated control query omitted the guarded shift opposite arm")
	assert(guardedNumericQuery ~= nil, "generated control query omitted the numeric NaN guard assumption")
	assert(guardedNumericNegatedQuery ~= nil, "generated control query omitted the guarded numeric opposite arm")
	assert(not hasUnguardedNumericQuery, "unconstrained numeric branch acquired speculative control work")
	local guardedShiftCertificate = nil
	local guardedShiftNegatedCertificate = nil
	local guardedNumericCertificate = nil
	local guardedNumericNegatedCertificate = nil
	for _, certificate in resolved.certificates do
		if certificate.query == guardedShiftQuery.id and certificate.resolution == "proved" then
			guardedShiftCertificate = certificate
		elseif certificate.query == guardedShiftNegatedQuery.id then
			guardedShiftNegatedCertificate = certificate
		elseif certificate.query == guardedNumericQuery.id and certificate.resolution == "proved" then
			guardedNumericCertificate = certificate
		elseif certificate.query == guardedNumericNegatedQuery.id then
			guardedNumericNegatedCertificate = certificate
		end
	end
	assert(guardedShiftCertificate ~= nil, "guarded shift query was not certified")
	assert(guardedNumericCertificate ~= nil, "guarded numeric query was not certified")
	assert(
		guardedShiftCertificate.engine == expectedEngine and guardedNumericCertificate.engine == expectedEngine,
		"guarded promotion used the wrong solver engine"
	)
	if expectedEngine == "z3" then
		assert(
			guardedShiftNegatedCertificate ~= nil
				and guardedShiftNegatedCertificate.resolution == "disproved"
				and guardedShiftNegatedCertificate.model ~= nil,
			"Z3 did not preserve the guarded shift opposite-arm countermodel"
		)
		assert(
			guardedNumericNegatedCertificate ~= nil
				and guardedNumericNegatedCertificate.resolution == "disproved"
				and guardedNumericNegatedCertificate.model ~= nil,
			"Z3 did not preserve the guarded numeric opposite-arm countermodel"
		)
	else
		assert(
			guardedShiftNegatedCertificate == nil and guardedNumericNegatedCertificate == nil,
			"internal facts invented an unknown opposite-arm countermodel"
		)
	end

	local conditionInstruction = resolved.instructions[resolved.values[conditionValue + 1].origin.instruction_result.instruction + 1]
	local guardedBlock = resolved.blocks[conditionInstruction.block + 1]
	assert(guardedBlock.terminator.jump ~= nil, "proved guarded branch was not rewritten")
	local numericConditionInstruction =
		resolved.instructions[resolved.values[numericConditionValue + 1].origin.instruction_result.instruction + 1]
	local numericGuardedBlock = resolved.blocks[numericConditionInstruction.block + 1]
	assert(numericGuardedBlock.terminator.jump ~= nil, "proved numeric guard branch was not rewritten")
	local unguardedNumericInstruction =
		resolved.instructions[resolved.values[unguardedNumericConditionValue + 1].origin.instruction_result.instruction + 1]
	local unguardedNumericBlock = resolved.blocks[unguardedNumericInstruction.block + 1]
	assert(unguardedNumericBlock.terminator.branch ~= nil, "unguarded numeric branch was rewritten without a domain proof")
	local generated = fs.readFile(generatedPath)
	assert(string.find(generated, "4294967295", 1, true) == nil, "dead guarded branch remained in generated Luau")
	assert(string.find(generated, "numeric-unreachable", 1, true) == nil, "dead numeric guard branch remained in generated Luau")
	assert(string.find(generated, "~=", 1, true) ~= nil, "unguarded numeric equality disappeared from generated Luau")
	assert(string.find(generated, "bit32.lshift", 1, true) ~= nil, "live guarded shift disappeared from generated Luau")
	return
end

local outputPath = mode
local builder = LifterIR.Builder.new("generic-guarded-solver-promotion")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-guarded-solver-promotion")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local u32 = LifterIR.Types.integer(32, false)
local boolean = LifterIR.Types.boolean()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local probe = builder:reserveFunction({ name_hint = "guarded_probe", evidence = evidence })
local count = builder:addParameter(probe, u32, "count")
local numericProbe = builder:reserveFunction({ name_hint = "guarded_numeric_probe", evidence = evidence })
local numericValue = builder:addParameter(numericProbe, LifterIR.Types.number(), "numeric_value")
local unguardedNumericProbe = builder:reserveFunction({ name_hint = "unguarded_numeric_probe", evidence = evidence })
local unguardedNumericValue = builder:addParameter(unguardedNumericProbe, LifterIR.Types.number(), "unguarded_numeric_value")
local chunkBlock = builder:reserveBlock(chunk, { evidence = evidence })
local rangeBlock = builder:reserveBlock(probe, { evidence = evidence })
local shiftBlock = builder:reserveBlock(probe, { evidence = evidence })
local outOfRangeBlock = builder:reserveBlock(probe, { evidence = evidence })
local matchedBlock = builder:reserveBlock(probe, { evidence = evidence })
local unreachableBlock = builder:reserveBlock(probe, { evidence = evidence })
local numericEntry = builder:reserveBlock(numericProbe, { evidence = evidence })
local numericMatched = builder:reserveBlock(numericProbe, { evidence = evidence })
local numericUnreachable = builder:reserveBlock(numericProbe, { evidence = evidence })
local unguardedNumericEntry = builder:reserveBlock(unguardedNumericProbe, { evidence = evidence })
local unguardedNumericNan = builder:reserveBlock(unguardedNumericProbe, { evidence = evidence })
local unguardedNumericFinite = builder:reserveBlock(unguardedNumericProbe, { evidence = evidence })

builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(probe, rangeBlock)
builder:setFunctionEntry(numericProbe, numericEntry)
builder:setFunctionEntry(unguardedNumericProbe, unguardedNumericEntry)

local _, exportedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(probe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "exported" } },
	{ effects = pure, evidence = evidence }
)
local _, numericExportResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(numericProbe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "numeric_exported" } },
	{ effects = pure, evidence = evidence }
)
local _, unguardedNumericExportResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(unguardedNumericProbe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "unguarded_numeric_exported" } },
	{ effects = pure, evidence = evidence }
)

local _, limitResults = builder:addInstruction(
	rangeBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("32")),
	{ { type = u32, name_hint = "shift_limit" } },
	{ effects = pure, evidence = evidence }
)
local _, inRangeResults = builder:addInstruction(
	rangeBlock,
	LifterIR.Operation.binary("less", count, limitResults[1], "primitive"),
	{ { type = boolean, name_hint = "in_range" } },
	{ effects = pure, evidence = evidence }
)
local _, leftResults = builder:addInstruction(
	shiftBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("6")),
	{ { type = u32, name_hint = "left" } },
	{ effects = pure, evidence = evidence }
)
local _, shiftedResults = builder:addInstruction(
	shiftBlock,
	LifterIR.Operation.binary("shift_left", leftResults[1], count, "primitive", LifterIR.ShiftBehavior.luauBit32),
	{ { type = u32, name_hint = "shifted" } },
	{ effects = pure, evidence = evidence }
)
local _, equivalentShiftResults = builder:addInstruction(
	shiftBlock,
	LifterIR.Operation.binary("shift_left", leftResults[1], count, "primitive", LifterIR.ShiftBehavior.luauBit32),
	{ { type = u32, name_hint = "equivalent_shift" } },
	{ effects = pure, evidence = evidence }
)
local _, identityResults = builder:addInstruction(
	shiftBlock,
	LifterIR.Operation.binary("equal", shiftedResults[1], equivalentShiftResults[1], "primitive"),
	{ { type = boolean, name_hint = "shift_identity" } },
	{ effects = pure, evidence = evidence }
)

local function addU32(block: number, value: string, nameHint: string): number
	local _, results = builder:addInstruction(
		block,
		LifterIR.Operation.constant(LifterIR.Literal.integer(value)),
		{ { type = u32, name_hint = nameHint } },
		{ effects = pure, evidence = evidence }
	)
	return results[1]
end

local outOfRange = addU32(outOfRangeBlock, "0", "out_of_range")
local unreachable = addU32(unreachableBlock, "4294967295", "guarded_unreachable")

local _, numericIdentityResults = builder:addInstruction(
	numericEntry,
	LifterIR.Operation.binary("equal", numericValue, numericValue, "primitive"),
	{ { type = boolean, name_hint = "numeric_identity" } },
	{ effects = pure, evidence = evidence }
)
local _, numericMatchedResults = builder:addInstruction(
	numericMatched,
	LifterIR.Operation.constant(LifterIR.Literal.string("numeric-matched")),
	{ { type = LifterIR.Types.string(), name_hint = "numeric_matched" } },
	{ effects = pure, evidence = evidence }
)
local _, numericUnreachableResults = builder:addInstruction(
	numericUnreachable,
	LifterIR.Operation.constant(LifterIR.Literal.string("numeric-unreachable")),
	{ { type = LifterIR.Types.string(), name_hint = "numeric_unreachable" } },
	{ effects = pure, evidence = evidence }
)

local _, unguardedNumericConditionResults = builder:addInstruction(
	unguardedNumericEntry,
	LifterIR.Operation.binary("not_equal", unguardedNumericValue, unguardedNumericValue, "primitive"),
	{ { type = boolean, name_hint = "unguarded_numeric_inequality" } },
	{ effects = pure, evidence = evidence }
)
local _, unguardedNumericNanResults = builder:addInstruction(
	unguardedNumericNan,
	LifterIR.Operation.constant(LifterIR.Literal.string("nan")),
	{ { type = LifterIR.Types.string(), name_hint = "nan_result" } },
	{ effects = pure, evidence = evidence }
)
local _, unguardedNumericFiniteResults = builder:addInstruction(
	unguardedNumericFinite,
	LifterIR.Operation.constant(LifterIR.Literal.string("finite")),
	{ { type = LifterIR.Types.string(), name_hint = "finite_result" } },
	{ effects = pure, evidence = evidence }
)

local bitVectorSort = LifterIR.SolverSort.bitVector(32, false)
local countTerm = builder:addSolverTerm(bitVectorSort, LifterIR.SolverTerm.value(count))
local limitTerm = builder:addSolverTerm(bitVectorSort, LifterIR.SolverTerm.bitVectorLiteral("32", 32))
local shiftGuard = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("less", countTerm, limitTerm)
)
builder:addConstraint(shiftGuard, evidence, LifterIR.ConstraintScope.block(shiftBlock))

local dynamicSort = LifterIR.SolverSort.dynamicValue()
local numericValueTerm = builder:addSolverTerm(dynamicSort, LifterIR.SolverTerm.value(numericValue))
local numericIsNaN = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.dynamicNumberIsNaN(numericValueTerm)
)
local numericNotNaN = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.logicalNot(numericIsNaN)
)
local numericGuard = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("logical_and", numericNotNaN, numericNotNaN)
)
builder:addConstraint(numericGuard, evidence, LifterIR.ConstraintScope.block(numericEntry))

builder:finalizeBlock(
	chunkBlock,
	LifterIR.Terminator.returnValues({ exportedResults[1], numericExportResults[1], unguardedNumericExportResults[1] })
)
builder:finalizeBlock(
	rangeBlock,
	LifterIR.Terminator.branch(
		inRangeResults[1],
		LifterIR.Edge(shiftBlock, {}),
		LifterIR.Edge(outOfRangeBlock, {})
	)
)
builder:finalizeBlock(
	shiftBlock,
	LifterIR.Terminator.branch(
		identityResults[1],
		LifterIR.Edge(matchedBlock, {}),
		LifterIR.Edge(unreachableBlock, {})
	)
)
builder:finalizeBlock(outOfRangeBlock, LifterIR.Terminator.returnValues({ outOfRange }))
builder:finalizeBlock(matchedBlock, LifterIR.Terminator.returnValues({ shiftedResults[1] }))
builder:finalizeBlock(unreachableBlock, LifterIR.Terminator.returnValues({ unreachable }))
builder:finalizeBlock(
	numericEntry,
	LifterIR.Terminator.branch(
		numericIdentityResults[1],
		LifterIR.Edge(numericMatched, {}),
		LifterIR.Edge(numericUnreachable, {})
	)
)
builder:finalizeBlock(numericMatched, LifterIR.Terminator.returnValues({ numericMatchedResults[1] }))
builder:finalizeBlock(numericUnreachable, LifterIR.Terminator.returnValues({ numericUnreachableResults[1] }))
builder:finalizeBlock(
	unguardedNumericEntry,
	LifterIR.Terminator.branch(
		unguardedNumericConditionResults[1],
		LifterIR.Edge(unguardedNumericNan, {}),
		LifterIR.Edge(unguardedNumericFinite, {})
	)
)
builder:finalizeBlock(unguardedNumericNan, LifterIR.Terminator.returnValues({ unguardedNumericNanResults[1] }))
builder:finalizeBlock(unguardedNumericFinite, LifterIR.Terminator.returnValues({ unguardedNumericFiniteResults[1] }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(probe)
builder:finalizeFunction(numericProbe)
builder:finalizeFunction(unguardedNumericProbe)

local encoded = LifterIR.encodeJson(builder:finish(), true)
local decoded = serde.decode("json", encoded)
assert(#decoded.solver_terms == 7, "guarded frontend should author only the canonical guards")
assert(#decoded.constraints == 2 and #decoded.queries == 0, "guarded frontend crossed the promotion boundary")
for _, term in decoded.solver_terms do
	assert(term.operation.value_definition == nil, "guarded frontend unexpectedly authored a value definition")
end
fs.writeFile(outputPath, encoded .. "\n")
