--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")

local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output JSON path")

local builder = LifterIR.Builder.new("generic-luau-u32-numerics")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-luau-u32-numerics")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local u32 = LifterIR.Types.integer(32, false)

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local exercise = builder:reserveFunction({ name_hint = "exercise_u32", evidence = evidence })
local left = builder:addParameter(exercise, u32, "left")
local right = builder:addParameter(exercise, u32, "right")
local chunkBlock = builder:reserveBlock(chunk, { evidence = evidence })
local exerciseBlock = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseArithmeticBlock = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseDivisionBlock = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseStringBlock = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseStringIdentityBlock = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseMatchedBlock = builder:reserveBlock(exercise, { evidence = evidence })
local exerciseUnreachableBlock = builder:reserveBlock(exercise, { evidence = evidence })

builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(exercise, exerciseBlock)

local _, exportedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(exercise),
	{ { type = LifterIR.Types.functionValue(), name_hint = "exported" } },
	{ effects = pure, evidence = evidence }
)

local function addBinary(
	operator: string,
	leftValue: number,
	rightValue: number,
	nameHint: string,
	shiftBehaviorOverride: string?
): number
	local shiftBehavior = if operator == "shift_left" or operator == "shift_right"
		then shiftBehaviorOverride or LifterIR.ShiftBehavior.luauBit32
		else nil
	local _, results = builder:addInstruction(
		exerciseBlock,
		LifterIR.Operation.binary(operator, leftValue, rightValue, "primitive", shiftBehavior),
		{ { type = u32, name_hint = nameHint } },
		{ effects = pure, evidence = evidence }
	)
	return results[1]
end

local andResult = addBinary("bit_and", left, right, "and_result")
local orResult = addBinary("bit_or", left, right, "or_result")
local xorResult = addBinary("bit_xor", left, right, "xor_result")
local leftShiftResult = addBinary("shift_left", left, right, "left_shift_result")
local rightShiftResult = addBinary("shift_right", left, right, "right_shift_result")
local zeroSaturatingLeftShiftResult = addBinary(
	"shift_left",
	left,
	right,
	"zero_saturating_left_shift_result",
	LifterIR.ShiftBehavior.zeroSaturating
)
local zeroSaturatingRightShiftResult = addBinary(
	"shift_right",
	left,
	right,
	"zero_saturating_right_shift_result",
	LifterIR.ShiftBehavior.zeroSaturating
)
local _, notResults = builder:addInstruction(
	exerciseBlock,
	LifterIR.Operation.unary("bit_not", left, "primitive"),
	{ { type = u32, name_hint = "not_result" } },
	{ effects = pure, evidence = evidence }
)
local _, negativeZeroResults = builder:addInstruction(
	exerciseBlock,
	LifterIR.Operation.constant(LifterIR.Literal.number(-0.0)),
	{ { type = LifterIR.Types.number(), name_hint = "negative_zero" } },
	{ effects = pure, evidence = evidence }
)
local _, fractionResults = builder:addInstruction(
	exerciseBlock,
	LifterIR.Operation.constant(LifterIR.Literal.number(0.1)),
	{ { type = LifterIR.Types.number(), name_hint = "fraction" } },
	{ effects = pure, evidence = evidence }
)

local function addConstant(literal: any, valueType: any, nameHint: string): number
	local _, results = builder:addInstruction(
		exerciseBlock,
		LifterIR.Operation.constant(literal),
		{ { type = valueType, name_hint = nameHint } },
		{ effects = pure, evidence = evidence }
	)
	return results[1]
end

local function addSourceBinary(
	operator: string,
	leftValue: number,
	rightValue: number,
	valueType: any,
	nameHint: string
): number
	local _, results = builder:addInstruction(
		exerciseBlock,
		LifterIR.Operation.binary(operator, leftValue, rightValue),
		{ { type = valueType, name_hint = nameHint } },
		{ effects = pure, evidence = evidence }
	)
	return results[1]
end

local seven = addConstant(LifterIR.Literal.integer("7"), LifterIR.Types.integer(), "seven")
local three = addConstant(LifterIR.Literal.integer("3"), LifterIR.Types.integer(), "three")
local two = addConstant(LifterIR.Literal.integer("2"), LifterIR.Types.integer(), "two")
local summed = addSourceBinary("add", seven, three, LifterIR.Types.integer(), "summed")
local subtracted = addSourceBinary("subtract", seven, three, LifterIR.Types.integer(), "subtracted")
local multiplied = addSourceBinary("multiply", seven, three, LifterIR.Types.integer(), "multiplied")
local quotient = addSourceBinary("divide", seven, two, LifterIR.Types.number(), "quotient")
local numberFloored = addSourceBinary("floor_divide", quotient, two, LifterIR.Types.number(), "number_floored")
local expectedNumberFloor = addConstant(
	LifterIR.Literal.number(1.0),
	LifterIR.Types.number(),
	"expected_number_floor"
)
local numberFloorMatches = addSourceBinary(
	"equal",
	numberFloored,
	expectedNumberFloor,
	LifterIR.Types.boolean(),
	"number_floor_matches"
)
local numberModulo = addSourceBinary("modulo", quotient, two, LifterIR.Types.number(), "number_modulo")
local expectedNumberModulo = addConstant(
	LifterIR.Literal.number(1.5),
	LifterIR.Types.number(),
	"expected_number_modulo"
)
local numberModuloMatches = addSourceBinary(
	"equal",
	numberModulo,
	expectedNumberModulo,
	LifterIR.Types.boolean(),
	"number_modulo_matches"
)
local finiteOrdering = addSourceBinary(
	"less",
	fractionResults[1],
	quotient,
	LifterIR.Types.boolean(),
	"finite_number_ordering"
)
local floored = addSourceBinary("floor_divide", seven, three, LifterIR.Types.integer(), "floored")
local remainder = addSourceBinary("modulo", seven, three, LifterIR.Types.integer(), "remainder")
local powered = addSourceBinary("power", two, three, LifterIR.Types.number(), "powered")
local expectedPower = addConstant(LifterIR.Literal.number(8.0), LifterIR.Types.number(), "expected_power")
local powerMatches = addSourceBinary(
	"equal",
	powered,
	expectedPower,
	LifterIR.Types.boolean(),
	"power_matches"
)
local _, negatedResults = builder:addInstruction(
	exerciseBlock,
	LifterIR.Operation.unary("negate", seven),
	{ { type = LifterIR.Types.integer(), name_hint = "negated" } },
	{ effects = pure, evidence = evidence }
)
local firstText = addConstant(LifterIR.Literal.string("ab"), LifterIR.Types.string(), "first_text")
local secondText = addConstant(LifterIR.Literal.string("cd"), LifterIR.Types.string(), "second_text")
local concatenated = addSourceBinary("concat", firstText, secondText, LifterIR.Types.string(), "concatenated")
local expectedConcatenation = addConstant(
	LifterIR.Literal.string("abcd"),
	LifterIR.Types.string(),
	"expected_concatenation"
)
local concatenationMatches = addSourceBinary(
	"equal",
	concatenated,
	expectedConcatenation,
	LifterIR.Types.boolean(),
	"concatenation_matches"
)
local orderingUpperBound = addConstant(
	LifterIR.Literal.string("abce"),
	LifterIR.Types.string(),
	"ordering_upper_bound"
)
local concatenatedOrdered = addSourceBinary(
	"less",
	concatenated,
	orderingUpperBound,
	LifterIR.Types.boolean(),
	"concatenated_ordered"
)
local runtimeOrderingFacts = addSourceBinary(
	"logical_and",
	finiteOrdering,
	concatenatedOrdered,
	LifterIR.Types.boolean(),
	"runtime_ordering_facts"
)
local stringAndOrderingFacts = addSourceBinary(
	"logical_and",
	concatenationMatches,
	runtimeOrderingFacts,
	LifterIR.Types.boolean(),
	"string_and_ordering_facts"
)
local stringFloorAndOrderingFacts = addSourceBinary(
	"logical_and",
	stringAndOrderingFacts,
	numberFloorMatches,
	LifterIR.Types.boolean(),
	"string_floor_and_ordering_facts"
)
local stringFloorModuloAndOrderingFacts = addSourceBinary(
	"logical_and",
	stringFloorAndOrderingFacts,
	numberModuloMatches,
	LifterIR.Types.boolean(),
	"string_floor_modulo_and_ordering_facts"
)
local stringAndNumberFacts = addSourceBinary(
	"logical_and",
	stringFloorModuloAndOrderingFacts,
	powerMatches,
	LifterIR.Types.boolean(),
	"string_and_number_facts"
)
local _, lengthResults = builder:addInstruction(
	exerciseBlock,
	LifterIR.Operation.unary("length", concatenated),
	{ { type = LifterIR.Types.integer(), name_hint = "text_length" } },
	{ effects = pure, evidence = evidence }
)
local four = addConstant(LifterIR.Literal.integer("4"), LifterIR.Types.integer(), "four")
local lengthMatches = addSourceBinary(
	"equal",
	lengthResults[1],
	four,
	LifterIR.Types.boolean(),
	"concatenated_length_matches"
)
local exactBitLeft = addConstant(LifterIR.Literal.integer("305419896"), u32, "exact_bit_left")
local exactBitMask = addConstant(LifterIR.Literal.integer("252645135"), u32, "exact_bit_mask")
local exactBitAnd = addBinary("bit_and", exactBitLeft, exactBitMask, "exact_bit_and")
local expectedExactBitAnd = addConstant(LifterIR.Literal.integer("33818120"), u32, "expected_exact_bit_and")
local exactBitwiseMatches = addSourceBinary(
	"equal",
	exactBitAnd,
	expectedExactBitAnd,
	LifterIR.Types.boolean(),
	"exact_bitwise_matches"
)
local falseValue = addConstant(LifterIR.Literal.boolean(false), LifterIR.Types.boolean(), "false_value")
local trueValue = addConstant(LifterIR.Literal.boolean(true), LifterIR.Types.boolean(), "true_value")
local either = addSourceBinary("logical_or", falseValue, trueValue, LifterIR.Types.boolean(), "either")
local booleanAndBitwiseFacts = addSourceBinary(
	"logical_and",
	either,
	exactBitwiseMatches,
	LifterIR.Types.boolean(),
	"boolean_and_bitwise_facts"
)
local allRuntimeFacts = addSourceBinary(
	"logical_and",
	stringAndNumberFacts,
	booleanAndBitwiseFacts,
	LifterIR.Types.boolean(),
	"all_runtime_facts"
)
local different = addSourceBinary("not_equal", seven, three, LifterIR.Types.boolean(), "different")
local ordered = addSourceBinary("less_equal", three, seven, LifterIR.Types.boolean(), "ordered")
local positiveInfinity = addConstant(
	LifterIR.Literal.specialNumber("positive_infinity"),
	LifterIR.Types.number(),
	"positive_infinity"
)
local positiveInfinityCopy = addConstant(
	LifterIR.Literal.specialNumber("positive_infinity"),
	LifterIR.Types.number(),
	"positive_infinity_copy"
)
local negativeInfinity = addConstant(
	LifterIR.Literal.specialNumber("negative_infinity"),
	LifterIR.Types.number(),
	"negative_infinity"
)
local notANumber = addConstant(LifterIR.Literal.specialNumber("nan"), LifterIR.Types.number(), "not_a_number")
local _, negatedInfinityResults = builder:addInstruction(
	exerciseBlock,
	LifterIR.Operation.unary("negate", positiveInfinity),
	{ { type = LifterIR.Types.number(), name_hint = "negated_positive_infinity" } },
	{ effects = pure, evidence = evidence }
)
local negatedPositiveInfinity = negatedInfinityResults[1]
local negationMatches = addSourceBinary(
	"equal",
	negatedPositiveInfinity,
	negativeInfinity,
	LifterIR.Types.boolean(),
	"negated_infinity_matches"
)
local cancelledInfinity = addSourceBinary(
	"add",
	positiveInfinity,
	negativeInfinity,
	LifterIR.Types.number(),
	"cancelled_infinity"
)
local cancelledInfinityIsNan = addSourceBinary(
	"not_equal",
	cancelledInfinity,
	cancelledInfinity,
	LifterIR.Types.boolean(),
	"cancelled_infinity_is_nan"
)
local dividedByNegativeZero = addSourceBinary(
	"divide",
	seven,
	negativeZeroResults[1],
	LifterIR.Types.number(),
	"divided_by_negative_zero"
)
local divisionMatches = addSourceBinary(
	"equal",
	dividedByNegativeZero,
	negativeInfinity,
	LifterIR.Types.boolean(),
	"division_matches_negative_infinity"
)
local equalInfinities = addSourceBinary(
	"equal",
	positiveInfinity,
	positiveInfinityCopy,
	LifterIR.Types.boolean(),
	"equal_infinities"
)
local distinctInfinities = addSourceBinary(
	"not_equal",
	positiveInfinity,
	negativeInfinity,
	LifterIR.Types.boolean(),
	"distinct_infinities"
)
local nanSelfInequality = addSourceBinary(
	"not_equal",
	notANumber,
	notANumber,
	LifterIR.Types.boolean(),
	"nan_self_inequality"
)

local integerSort = LifterIR.SolverSort.integer()
local sevenTerm = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.value(seven))
local threeTerm = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.value(three))
local divisorNonzero = builder:addSolverTerm(LifterIR.SolverSort.boolean(), LifterIR.SolverTerm.isNonzero(threeTerm))
local floorExpression = builder:addSolverTerm(
	integerSort,
	LifterIR.SolverTerm.division("integer_floor", sevenTerm, threeTerm, divisorNonzero)
)
local floorDefinition = builder:addSolverTerm(
	integerSort,
	LifterIR.SolverTerm.valueDefinition(floored, floorExpression)
)
local remainderExpression = builder:addSolverTerm(
	integerSort,
	LifterIR.SolverTerm.remainder("integer_floor", sevenTerm, threeTerm, divisorNonzero)
)
local remainderDefinition = builder:addSolverTerm(
	integerSort,
	LifterIR.SolverTerm.valueDefinition(remainder, remainderExpression)
)
local expectedFloor = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.value(two))
local expectedRemainder = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral("1"))
local floorDefinitionExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("equal", floorDefinition, expectedFloor)
)
local remainderDefinitionExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("equal", remainderDefinition, expectedRemainder)
)
local negationExpression = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.arithmeticNegate(sevenTerm))
local negationDefinition = builder:addSolverTerm(
	integerSort,
	LifterIR.SolverTerm.valueDefinition(negatedResults[1], negationExpression)
)
local expectedNegation = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral("-7"))
local negationDefinitionExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("equal", negationDefinition, expectedNegation)
)
local floorRemainderDefinitionsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("logical_and", floorDefinitionExact, remainderDefinitionExact)
)
local partialUnaryDefinitionsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("logical_and", floorRemainderDefinitionsExact, negationDefinitionExact)
)
local function addIntegerBinaryDefinition(
	operator: string,
	leftOperand: number,
	rightOperand: number,
	value: number,
	expected: string
): number
	local expression = builder:addSolverTerm(
		integerSort,
		LifterIR.SolverTerm.binary(operator, leftOperand, rightOperand)
	)
	local definition = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.valueDefinition(value, expression))
	local expectedTerm = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral(expected))
	return builder:addSolverTerm(
		LifterIR.SolverSort.boolean(),
		LifterIR.SolverTerm.binary("equal", definition, expectedTerm)
	)
end

local addDefinitionExact = addIntegerBinaryDefinition("add", sevenTerm, threeTerm, summed, "10")
local subtractDefinitionExact = addIntegerBinaryDefinition("subtract", sevenTerm, threeTerm, subtracted, "4")
local multiplyDefinitionExact = addIntegerBinaryDefinition("multiply", sevenTerm, threeTerm, multiplied, "21")
local addSubtractDefinitionsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("logical_and", addDefinitionExact, subtractDefinitionExact)
)
local integerDefinitionsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("logical_and", addSubtractDefinitionsExact, multiplyDefinitionExact)
)
local booleanSort = LifterIR.SolverSort.boolean()
local falseTerm = builder:addSolverTerm(booleanSort, LifterIR.SolverTerm.value(falseValue))
local trueTerm = builder:addSolverTerm(booleanSort, LifterIR.SolverTerm.value(trueValue))
local expectedTrue = builder:addSolverTerm(booleanSort, LifterIR.SolverTerm.booleanLiteral(true))

local function addBooleanBinaryDefinition(
	operator: string,
	leftOperand: number,
	rightOperand: number,
	value: number
): number
	local expression = builder:addSolverTerm(
		booleanSort,
		LifterIR.SolverTerm.binary(operator, leftOperand, rightOperand)
	)
	local definition = builder:addSolverTerm(booleanSort, LifterIR.SolverTerm.valueDefinition(value, expression))
	return builder:addSolverTerm(
		booleanSort,
		LifterIR.SolverTerm.binary("equal", definition, expectedTrue)
	)
end

local logicalOrDefinitionExact = addBooleanBinaryDefinition("logical_or", falseTerm, trueTerm, either)
local inequalityDefinitionExact = addBooleanBinaryDefinition("not_equal", sevenTerm, threeTerm, different)
local orderingDefinitionExact = addBooleanBinaryDefinition("less_equal", threeTerm, sevenTerm, ordered)
local comparisonDefinitionsExact = builder:addSolverTerm(
	booleanSort,
	LifterIR.SolverTerm.binary("logical_and", inequalityDefinitionExact, orderingDefinitionExact)
)
local booleanDefinitionsExact = builder:addSolverTerm(
	booleanSort,
	LifterIR.SolverTerm.binary("logical_and", logicalOrDefinitionExact, comparisonDefinitionsExact)
)
local exactNormalizedDefinitions = builder:addSolverTerm(
	booleanSort,
	LifterIR.SolverTerm.binary("logical_and", integerDefinitionsExact, booleanDefinitionsExact)
)
local sourceDefinitionsExact = builder:addSolverTerm(
	booleanSort,
	LifterIR.SolverTerm.binary("logical_and", partialUnaryDefinitionsExact, exactNormalizedDefinitions)
)
local bitVectorSort = LifterIR.SolverSort.bitVector(32, false)
local exactBitAndTerm = builder:addSolverTerm(bitVectorSort, LifterIR.SolverTerm.value(exactBitAnd))
local exactBitAndLiteral = builder:addSolverTerm(
	bitVectorSort,
	LifterIR.SolverTerm.bitVectorLiteral("33818120", 32)
)
local exactBitAndLiteralMatches = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("equal", exactBitAndTerm, exactBitAndLiteral)
)
local leftTerm = builder:addSolverTerm(bitVectorSort, LifterIR.SolverTerm.value(left))
local rightTerm = builder:addSolverTerm(bitVectorSort, LifterIR.SolverTerm.value(right))
local shiftLimit = builder:addSolverTerm(bitVectorSort, LifterIR.SolverTerm.bitVectorLiteral("32", 32))
local shiftGuard = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("less", rightTerm, shiftLimit)
)

local function addBitBinaryDefinition(
	operator: string,
	value: number,
	rightOperand: number?,
	validWhen: number?
): number
	local expression = builder:addSolverTerm(
		bitVectorSort,
		LifterIR.SolverTerm.binary(operator, leftTerm, rightOperand or rightTerm)
	)
	local definition = builder:addSolverTerm(
		bitVectorSort,
		LifterIR.SolverTerm.valueDefinition(value, expression, validWhen)
	)
	return builder:addSolverTerm(
		LifterIR.SolverSort.boolean(),
		LifterIR.SolverTerm.binary("equal", definition, expression)
	)
end

local andDefinitionExact = addBitBinaryDefinition("bit_and", andResult)
local orDefinitionExact = addBitBinaryDefinition("bit_or", orResult)
local xorDefinitionExact = addBitBinaryDefinition("bit_xor", xorResult)
local leftShiftDefinitionExact = addBitBinaryDefinition("shift_left", leftShiftResult, rightTerm, shiftGuard)
local rightShiftDefinitionExact = addBitBinaryDefinition("shift_right", rightShiftResult, rightTerm, shiftGuard)
local zeroSaturatingLeftShiftDefinitionExact =
	addBitBinaryDefinition("shift_left", zeroSaturatingLeftShiftResult, rightTerm)
local zeroSaturatingRightShiftDefinitionExact =
	addBitBinaryDefinition("shift_right", zeroSaturatingRightShiftResult, rightTerm)
local notExpression = builder:addSolverTerm(bitVectorSort, LifterIR.SolverTerm.bitVectorNot(leftTerm))
local notDefinition = builder:addSolverTerm(
	bitVectorSort,
	LifterIR.SolverTerm.valueDefinition(notResults[1], notExpression)
)
local notDefinitionExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("equal", notDefinition, notExpression)
)
local andOrDefinitionsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("logical_and", andDefinitionExact, orDefinitionExact)
)
local xorNotDefinitionsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("logical_and", xorDefinitionExact, notDefinitionExact)
)
local coreBitDefinitionsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("logical_and", andOrDefinitionsExact, xorNotDefinitionsExact)
)
local luauShiftDefinitionsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("logical_and", leftShiftDefinitionExact, rightShiftDefinitionExact)
)
local zeroSaturatingShiftDefinitionsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary(
		"logical_and",
		zeroSaturatingLeftShiftDefinitionExact,
		zeroSaturatingRightShiftDefinitionExact
	)
)
local shiftDefinitionsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("logical_and", luauShiftDefinitionsExact, zeroSaturatingShiftDefinitionsExact)
)
local bitDefinitionsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("logical_and", coreBitDefinitionsExact, shiftDefinitionsExact)
)
local allSourceDefinitionsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary(
		"logical_and",
		sourceDefinitionsExact,
		builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", bitDefinitionsExact, exactBitAndLiteralMatches)
		)
	)
)
local divisorConstraint = builder:addConstraint(divisorNonzero, evidence)
local shiftConstraint = builder:addConstraint(shiftGuard, evidence)
local sourceDefinitionQuery = builder:addQuery(
	"prove_true",
	{ divisorConstraint, shiftConstraint },
	allSourceDefinitionsExact
)
builder:addClaim(
	LifterIR.Entity.program(),
	allSourceDefinitionsExact,
	"unproven",
	true,
	evidence,
	nil,
	nil,
	sourceDefinitionQuery
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportedResults[1] }))
builder:finalizeBlock(
	exerciseBlock,
	LifterIR.Terminator.branch(
		negationMatches,
		LifterIR.Edge(exerciseArithmeticBlock),
		LifterIR.Edge(exerciseUnreachableBlock)
	)
)
builder:finalizeBlock(
	exerciseArithmeticBlock,
	LifterIR.Terminator.branch(
		cancelledInfinityIsNan,
		LifterIR.Edge(exerciseDivisionBlock),
		LifterIR.Edge(exerciseUnreachableBlock)
	)
)
builder:finalizeBlock(
	exerciseDivisionBlock,
	LifterIR.Terminator.branch(
		divisionMatches,
		LifterIR.Edge(exerciseStringBlock),
		LifterIR.Edge(exerciseUnreachableBlock)
	)
)
builder:finalizeBlock(
	exerciseStringBlock,
	LifterIR.Terminator.branch(
		lengthMatches,
		LifterIR.Edge(exerciseStringIdentityBlock),
		LifterIR.Edge(exerciseUnreachableBlock)
	)
)
builder:finalizeBlock(
	exerciseStringIdentityBlock,
	LifterIR.Terminator.branch(
		allRuntimeFacts,
		LifterIR.Edge(exerciseMatchedBlock),
		LifterIR.Edge(exerciseUnreachableBlock)
	)
)
builder:finalizeBlock(
	exerciseMatchedBlock,
	LifterIR.Terminator.returnValues({
		andResult,
		orResult,
		xorResult,
		leftShiftResult,
		rightShiftResult,
		notResults[1],
		negativeZeroResults[1],
		fractionResults[1],
		quotient,
		floored,
		remainder,
		powered,
		negatedResults[1],
		concatenated,
		lengthResults[1],
		either,
		different,
		ordered,
		summed,
		subtracted,
		multiplied,
		positiveInfinity,
		positiveInfinityCopy,
		negativeInfinity,
		notANumber,
		negatedPositiveInfinity,
		cancelledInfinity,
		equalInfinities,
		distinctInfinities,
		nanSelfInequality,
		dividedByNegativeZero,
		numberFloored,
		numberModulo,
		concatenatedOrdered,
		concatenationMatches,
		exactBitwiseMatches,
		zeroSaturatingLeftShiftResult,
		zeroSaturatingRightShiftResult,
	})
)
local _, unreachableResults = builder:addInstruction(
	exerciseUnreachableBlock,
	LifterIR.Operation.constant(LifterIR.Literal.string("wrong-negated-infinity-arm")),
	{ { type = LifterIR.Types.string(), name_hint = "unreachable_result" } },
	{ effects = pure, evidence = evidence }
)
builder:finalizeBlock(exerciseUnreachableBlock, LifterIR.Terminator.returnValues({ unreachableResults[1] }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(exercise)

local encoded = LifterIR.encodeJson(builder:finish(), true)
local decoded = serde.decode("json", encoded)
assert(decoded.schema_version == "lifter_ir_v1", "serialized schema version did not round-trip")
assert(decoded.program_id == "generic-luau-u32-numerics", "serialized program ID did not round-trip")
fs.writeFile(outputPath, encoded .. "\n")
