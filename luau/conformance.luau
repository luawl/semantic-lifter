--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")

local LifterIR = require("./lifter_ir")

local outputPath = process.args[1]
assert(outputPath ~= nil and outputPath ~= "", "expected an output JSON path")

local builder = LifterIR.Builder.new("generic-luau-choose-max-module")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-luau-choose-max-module")
local evidence = { proof }
local pure = LifterIR.Effects.pure()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local chooseMax = builder:reserveFunction({ name_hint = "choose_max", evidence = evidence })
local identityPackFunction = builder:reserveFunction({
	name_hint = "identity_pack",
	is_variadic = true,
	evidence = evidence,
})
local identityVarargs = builder:addVarargPack(identityPackFunction, evidence)
local firstVarargFunction = builder:reserveFunction({
	name_hint = "first_vararg",
	is_variadic = true,
	evidence = evidence,
})
local firstVarargs = builder:addVarargPack(firstVarargFunction, evidence)
local forwardOpenFunction = builder:reserveFunction({ name_hint = "forward_open", evidence = evidence })
local callWithVarargsFunction = builder:reserveFunction({
	name_hint = "call_with_varargs",
	is_variadic = true,
	evidence = evidence,
})
local callWithVarargsPack = builder:addVarargPack(callWithVarargsFunction, evidence)
local prefixVarargsFunction = builder:reserveFunction({
	name_hint = "prefix_varargs",
	is_variadic = true,
	evidence = evidence,
})
local prefixVarargsPack = builder:addVarargPack(prefixVarargsFunction, evidence)
local earlyReturnLoopFunction = builder:reserveFunction({ name_hint = "early_return_loop", evidence = evidence })
local left = builder:addParameter(chooseMax, LifterIR.Types.number(), "left")
local right = builder:addParameter(chooseMax, LifterIR.Types.number(), "right")
local forwardValue = builder:addParameter(forwardOpenFunction, LifterIR.Types.number(), "value")
local prefixValue = builder:addParameter(prefixVarargsFunction, LifterIR.Types.integer(), "prefix")

local chunkBlock = builder:reserveBlock(chunk, { evidence = evidence })
local chunkLive = builder:reserveBlock(chunk, { evidence = evidence })
local chunkDead = builder:reserveBlock(chunk, { evidence = evidence })
local identityBlock = builder:reserveBlock(identityPackFunction, { evidence = evidence })
local firstVarargBlock = builder:reserveBlock(firstVarargFunction, { evidence = evidence })
local forwardOpenBlock = builder:reserveBlock(forwardOpenFunction, { evidence = evidence })
local callWithVarargsBlock = builder:reserveBlock(callWithVarargsFunction, { evidence = evidence })
local prefixVarargsBlock = builder:reserveBlock(prefixVarargsFunction, { evidence = evidence })
local earlyEntry = builder:reserveBlock(earlyReturnLoopFunction, { evidence = evidence })
local earlyHeader = builder:reserveBlock(earlyReturnLoopFunction, { evidence = evidence })
local earlyBody = builder:reserveBlock(earlyReturnLoopFunction, { evidence = evidence })
local earlyReturn = builder:reserveBlock(earlyReturnLoopFunction, { evidence = evidence })
local earlyExit = builder:reserveBlock(earlyReturnLoopFunction, { evidence = evidence })
local chooseEntry = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseLeft = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseCompareRight = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseRight = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseTie = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseLeftPass = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseRightPass = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseTiePass = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseNestedJoin = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseJoin = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseLoopHeader = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseLoopBody = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseBreakPrep = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseBreakForward = builder:reserveBlock(chooseMax, { evidence = evidence })
local chooseReturn = builder:reserveBlock(chooseMax, { evidence = evidence })
local leftCandidate = builder:addBlockParameter(chooseLeft, LifterIR.Types.number(), "left_candidate")
local rightCandidate = builder:addBlockParameter(chooseRight, LifterIR.Types.number(), "right_candidate")
local tieCandidate = builder:addBlockParameter(chooseTie, LifterIR.Types.number(), "tie_candidate")
local forwardedLeft = builder:addBlockParameter(chooseLeftPass, LifterIR.Types.number(), "forwarded_left")
local forwardedRight = builder:addBlockParameter(chooseRightPass, LifterIR.Types.number(), "forwarded_right")
local forwardedTie = builder:addBlockParameter(chooseTiePass, LifterIR.Types.number(), "forwarded_tie")
local nestedChosen = builder:addBlockParameter(chooseNestedJoin, LifterIR.Types.number(), "nested_chosen")
local chosen = builder:addBlockParameter(chooseJoin, LifterIR.Types.number(), "chosen")
local loopChosen = builder:addBlockParameter(chooseLoopHeader, LifterIR.Types.number(), "loop_chosen")
local loopCounter = builder:addBlockParameter(chooseLoopHeader, LifterIR.Types.integer(), "loop_counter")
local breakCandidate = builder:addBlockParameter(chooseBreakPrep, LifterIR.Types.number(), "break_candidate")
local forwardedBreak = builder:addBlockParameter(chooseBreakForward, LifterIR.Types.number(), "forwarded_break")
local returned = builder:addBlockParameter(chooseReturn, LifterIR.Types.number(), "returned")
local earlyCounter = builder:addBlockParameter(earlyHeader, LifterIR.Types.integer(), "early_counter")
local earlyReturned = builder:addBlockParameter(earlyReturn, LifterIR.Types.integer(), "early_returned")
local earlyExhausted = builder:addBlockParameter(earlyExit, LifterIR.Types.integer(), "early_exhausted")

local bitVector64 = LifterIR.SolverSort.bitVector(64)
local maxWordLeft = builder:addSolverTerm(
	bitVector64,
	LifterIR.SolverTerm.bitVectorLiteral("18446744073709551615", 64)
)
local maxWordRight = builder:addSolverTerm(
	bitVector64,
	LifterIR.SolverTerm.bitVectorLiteral("18446744073709551615", 64)
)
local wordsEqual = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("equal", maxWordLeft, maxWordRight)
)
local selectThen = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.booleanLiteral(true)
)
local zeroWord = builder:addSolverTerm(
	bitVector64,
	LifterIR.SolverTerm.bitVectorLiteral("0", 64)
)
local selectedWord = builder:addSolverTerm(
	bitVector64,
	LifterIR.SolverTerm.ifThenElse(selectThen, maxWordLeft, zeroWord)
)
local selectionIsExact = builder:addSolverTerm(
	LifterIR.SolverSort.boolean(),
	LifterIR.SolverTerm.binary("equal", selectedWord, maxWordLeft)
)
local selectionQuery = builder:addQuery("prove_true", {}, selectionIsExact)
builder:addClaim(
	LifterIR.Entity.program(),
	selectionIsExact,
	"unproven",
	true,
	evidence,
	nil,
	nil,
	selectionQuery
)
do
	local function addBitVectorStructureProof()
		local bitVector8 = LifterIR.SolverSort.bitVector(8)
		local bitVector16 = LifterIR.SolverSort.bitVector(16)
		local highByte = builder:addSolverTerm(bitVector8, LifterIR.SolverTerm.bitVectorLiteral("10", 8))
		local lowByte = builder:addSolverTerm(bitVector8, LifterIR.SolverTerm.bitVectorLiteral("3", 8))
		local joinedBytes = builder:addSolverTerm(
			bitVector16,
			LifterIR.SolverTerm.bitVectorConcat(highByte, lowByte)
		)
		local recoveredHighByte = builder:addSolverTerm(
			bitVector8,
			LifterIR.SolverTerm.bitVectorExtract(joinedBytes, 15, 8)
		)
		local zeroByte = builder:addSolverTerm(bitVector8, LifterIR.SolverTerm.bitVectorLiteral("0", 8))
		local invertedZeroByte = builder:addSolverTerm(bitVector8, LifterIR.SolverTerm.bitVectorNot(zeroByte))
		local fullByte = builder:addSolverTerm(bitVector8, LifterIR.SolverTerm.bitVectorLiteral("255", 8))
		local signedByte = builder:addSolverTerm(bitVector8, LifterIR.SolverTerm.bitVectorLiteral("128", 8))
		local signExtendedByte = builder:addSolverTerm(
			bitVector16,
			LifterIR.SolverTerm.bitVectorExtend(signedByte, 8, "sign")
		)
		local signExtendedExpected = builder:addSolverTerm(
			bitVector16,
			LifterIR.SolverTerm.bitVectorLiteral("65408", 16)
		)
		local zeroExtendedByte = builder:addSolverTerm(
			bitVector16,
			LifterIR.SolverTerm.bitVectorExtend(signedByte, 8, "zero")
		)
		local zeroExtendedExpected = builder:addSolverTerm(
			bitVector16,
			LifterIR.SolverTerm.bitVectorLiteral("128", 16)
		)
		local concatExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", recoveredHighByte, highByte)
		)
		local notExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", invertedZeroByte, fullByte)
		)
		local signExtensionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", signExtendedByte, signExtendedExpected)
		)
		local zeroExtensionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", zeroExtendedByte, zeroExtendedExpected)
		)
		local structuralPair = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", concatExact, notExact)
		)
		local extensionPair = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", signExtensionExact, zeroExtensionExact)
		)
		local rotateSource = builder:addSolverTerm(bitVector8, LifterIR.SolverTerm.bitVectorLiteral("129", 8))
		local rotateAmount = builder:addSolverTerm(bitVector8, LifterIR.SolverTerm.bitVectorLiteral("1", 8))
		local rotatedByte = builder:addSolverTerm(
			bitVector8,
			LifterIR.SolverTerm.bitVectorRotate(rotateSource, rotateAmount, "left")
		)
		local rotatedExpected = builder:addSolverTerm(bitVector8, LifterIR.SolverTerm.bitVectorLiteral("3", 8))
		local rotationExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", rotatedByte, rotatedExpected)
		)
		local extensionAndRotation = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", extensionPair, rotationExact)
		)
		local integerSort = LifterIR.SolverSort.integer()
		local minusOne = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral("-1"))
		local minusOneByte = builder:addSolverTerm(bitVector8, LifterIR.SolverTerm.integerToBitVector(minusOne))
		local signedRoundTrip = builder:addSolverTerm(
			integerSort,
			LifterIR.SolverTerm.bitVectorToInteger(minusOneByte, true)
		)
		local unsignedRoundTrip = builder:addSolverTerm(
			integerSort,
			LifterIR.SolverTerm.bitVectorToInteger(minusOneByte, false)
		)
		local unsignedExpected = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral("255"))
		local wordConversionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", minusOneByte, fullByte)
		)
		local signedConversionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", signedRoundTrip, minusOne)
		)
		local unsignedConversionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", unsignedRoundTrip, unsignedExpected)
		)
		local integerConversionsExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", signedConversionExact, unsignedConversionExact)
		)
		local conversionsExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", wordConversionExact, integerConversionsExact)
		)
		local positiveSeven = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral("7"))
		local negativeSeven = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.arithmeticNegate(positiveSeven))
		local negativeSevenExpected = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral("-7"))
		local integerNegationExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", negativeSeven, negativeSevenExpected)
		)
		local negativeOneByte = builder:addSolverTerm(bitVector8, LifterIR.SolverTerm.arithmeticNegate(rotateAmount))
		local wordNegationExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", negativeOneByte, fullByte)
		)
		local negationExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", integerNegationExact, wordNegationExact)
		)
		local conversionsAndNegationExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", conversionsExact, negationExact)
		)
		local integerDivisor = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral("3"))
		local integerDivisionDefined = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.isNonzero(integerDivisor)
		)
		local integerQuotient = builder:addSolverTerm(
			integerSort,
			LifterIR.SolverTerm.division("integer_euclidean", positiveSeven, integerDivisor, integerDivisionDefined)
		)
		local integerQuotientExpected = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral("2"))
		local integerDivisionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", integerQuotient, integerQuotientExpected)
		)
		local integerDivisionConstraint = builder:addConstraint(integerDivisionDefined, evidence)

		local wordDivisor = builder:addSolverTerm(bitVector8, LifterIR.SolverTerm.bitVectorLiteral("2", 8))
		local unsignedDivisionDefined = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.isNonzero(wordDivisor)
		)
		local unsignedQuotient = builder:addSolverTerm(
			bitVector8,
			LifterIR.SolverTerm.division("bit_vector_unsigned", fullByte, wordDivisor, unsignedDivisionDefined)
		)
		local unsignedQuotientExpected = builder:addSolverTerm(
			bitVector8,
			LifterIR.SolverTerm.bitVectorLiteral("127", 8)
		)
		local unsignedDivisionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", unsignedQuotient, unsignedQuotientExpected)
		)
		local unsignedDivisionConstraint = builder:addConstraint(unsignedDivisionDefined, evidence)

		local signedBitVector8 = LifterIR.SolverSort.bitVector(8, true)
		local signedDividend = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.bitVectorLiteral("251", 8)
		)
		local signedDivisor = builder:addSolverTerm(signedBitVector8, LifterIR.SolverTerm.bitVectorLiteral("2", 8))
		local signedDivisionDefined = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.isNonzero(signedDivisor)
		)
		local signedQuotient = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.division("bit_vector_signed", signedDividend, signedDivisor, signedDivisionDefined)
		)
		local signedQuotientExpected = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.bitVectorLiteral("254", 8)
		)
		local signedDivisionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", signedQuotient, signedQuotientExpected)
		)
		local signedDivisionConstraint = builder:addConstraint(signedDivisionDefined, evidence)
		local unsignedShift = builder:addSolverTerm(
			bitVector8,
			LifterIR.SolverTerm.binary("shift_right", fullByte, rotateAmount)
		)
		local unsignedShiftExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", unsignedShift, unsignedQuotientExpected)
		)
		local signedShiftSource = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.bitVectorLiteral("128", 8)
		)
		local signedShiftAmount = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.bitVectorLiteral("1", 8)
		)
		local signedShift = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.binary("shift_right", signedShiftSource, signedShiftAmount)
		)
		local signedShiftExpected = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.bitVectorLiteral("192", 8)
		)
		local signedShiftExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", signedShift, signedShiftExpected)
		)
		local oversizedShiftAmount = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.bitVectorLiteral("8", 8)
		)
		local oversizedSignedShift = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.binary("shift_right", signedShiftSource, oversizedShiftAmount)
		)
		local oversizedSignedShiftExpected = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.bitVectorLiteral("255", 8)
		)
		local oversizedSignedShiftExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", oversizedSignedShift, oversizedSignedShiftExpected)
		)
		local signedShiftsExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", signedShiftExact, oversizedSignedShiftExact)
		)
		local wordShiftsExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", unsignedShiftExact, signedShiftsExact)
		)

		local integerAndUnsignedDivisionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", integerDivisionExact, unsignedDivisionExact)
		)
		local divisionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", integerAndUnsignedDivisionExact, signedDivisionExact)
		)

		local negativeIntegerDivisor = builder:addSolverTerm(
			integerSort,
			LifterIR.SolverTerm.arithmeticNegate(integerDivisor)
		)
		local integerRemainderDefined = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.isNonzero(negativeIntegerDivisor)
		)
		local integerEuclideanRemainder = builder:addSolverTerm(
			integerSort,
			LifterIR.SolverTerm.remainder(
				"integer_euclidean",
				positiveSeven,
				negativeIntegerDivisor,
				integerRemainderDefined
			)
		)
		local integerFloorRemainder = builder:addSolverTerm(
			integerSort,
			LifterIR.SolverTerm.remainder(
				"integer_floor",
				positiveSeven,
				negativeIntegerDivisor,
				integerRemainderDefined
			)
		)
		local integerEuclideanRemainderExpected = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral("1"))
		local integerFloorRemainderExpected = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral("-2"))
		local integerEuclideanRemainderExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", integerEuclideanRemainder, integerEuclideanRemainderExpected)
		)
		local integerFloorRemainderExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", integerFloorRemainder, integerFloorRemainderExpected)
		)
		local integerRemaindersExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", integerEuclideanRemainderExact, integerFloorRemainderExact)
		)
		local integerRemainderConstraint = builder:addConstraint(integerRemainderDefined, evidence)
		local negativeEuclideanQuotient = builder:addSolverTerm(
			integerSort,
			LifterIR.SolverTerm.division(
				"integer_euclidean",
				positiveSeven,
				negativeIntegerDivisor,
				integerRemainderDefined
			)
		)
		local negativeFloorQuotient = builder:addSolverTerm(
			integerSort,
			LifterIR.SolverTerm.division(
				"integer_floor",
				positiveSeven,
				negativeIntegerDivisor,
				integerRemainderDefined
			)
		)
		local negativeEuclideanQuotientExpected = builder:addSolverTerm(
			integerSort,
			LifterIR.SolverTerm.integerLiteral("-2")
		)
		local negativeFloorQuotientExpected = builder:addSolverTerm(
			integerSort,
			LifterIR.SolverTerm.integerLiteral("-3")
		)
		local negativeEuclideanDivisionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", negativeEuclideanQuotient, negativeEuclideanQuotientExpected)
		)
		local negativeFloorDivisionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", negativeFloorQuotient, negativeFloorQuotientExpected)
		)
		local integerDivisionConventionsExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", negativeEuclideanDivisionExact, negativeFloorDivisionExact)
		)
		local allDivisionModesExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", divisionExact, integerDivisionConventionsExact)
		)
		local divisionAndShiftModesExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", allDivisionModesExact, wordShiftsExact)
		)

		local unsignedRemainder = builder:addSolverTerm(
			bitVector8,
			LifterIR.SolverTerm.remainder(
				"bit_vector_unsigned",
				fullByte,
				wordDivisor,
				unsignedDivisionDefined
			)
		)
		local unsignedRemainderExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", unsignedRemainder, rotateAmount)
		)

		local signedDividendRemainder = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.remainder(
				"bit_vector_signed_dividend",
				signedDividend,
				signedDivisor,
				signedDivisionDefined
			)
		)
		local signedDivisorRemainder = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.remainder(
				"bit_vector_signed_divisor",
				signedDividend,
				signedDivisor,
				signedDivisionDefined
			)
		)
		local signedDividendRemainderExpected = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.bitVectorLiteral("255", 8)
		)
		local signedDivisorRemainderExpected = builder:addSolverTerm(
			signedBitVector8,
			LifterIR.SolverTerm.bitVectorLiteral("1", 8)
		)
		local signedDividendRemainderExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", signedDividendRemainder, signedDividendRemainderExpected)
		)
		local signedDivisorRemainderExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", signedDivisorRemainder, signedDivisorRemainderExpected)
		)
		local signedRemaindersExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", signedDividendRemainderExact, signedDivisorRemainderExact)
		)
		local wordRemaindersExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", unsignedRemainderExact, signedRemaindersExact)
		)
		local remainderExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", integerRemaindersExact, wordRemaindersExact)
		)
		local divisionAndRemainderExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", divisionAndShiftModesExact, remainderExact)
		)
		local arithmeticFactsExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", conversionsAndNegationExact, divisionAndRemainderExact)
		)

		local realSort = LifterIR.SolverSort.real()
		local realDividend = builder:addSolverTerm(realSort, LifterIR.SolverTerm.realLiteral("3", "2"))
		local realDivisor = builder:addSolverTerm(realSort, LifterIR.SolverTerm.realLiteral("3", "4"))
		local realDivisionDefined = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.isNonzero(realDivisor)
		)
		local realQuotient = builder:addSolverTerm(
			realSort,
			LifterIR.SolverTerm.division("real", realDividend, realDivisor, realDivisionDefined)
		)
		local realQuotientExpected = builder:addSolverTerm(realSort, LifterIR.SolverTerm.realLiteral("2", "1"))
		local realDivisionExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("equal", realQuotient, realQuotientExpected)
		)
		local realDivisionConstraint = builder:addConstraint(realDivisionDefined, evidence)
		local realDivisionQuery = builder:addQuery("prove_true", { realDivisionConstraint }, realDivisionExact)
		builder:addClaim(
			LifterIR.Entity.program(),
			realDivisionExact,
			"unproven",
			false,
			evidence,
			nil,
			nil,
			realDivisionQuery
		)

		local arithmeticStructureExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", extensionAndRotation, arithmeticFactsExact)
		)
		local bitVectorStructureExact = builder:addSolverTerm(
			LifterIR.SolverSort.boolean(),
			LifterIR.SolverTerm.binary("logical_and", structuralPair, arithmeticStructureExact)
		)
		local divisionAssumptions = {
			integerDivisionConstraint,
			integerRemainderConstraint,
			unsignedDivisionConstraint,
			signedDivisionConstraint,
		}
		local bitVectorStructureQuery = builder:addQuery("prove_true", divisionAssumptions, bitVectorStructureExact)
		builder:addClaim(
			LifterIR.Entity.program(),
			bitVectorStructureExact,
			"unproven",
			true,
			evidence,
			nil,
			nil,
			bitVectorStructureQuery
		)
	end

	addBitVectorStructureProof()
end
builder:addConstraint(wordsEqual, evidence, LifterIR.ConstraintScope.program())
local equalityQuery = builder:addQuery("prove_true", {}, wordsEqual)
builder:addUnsatCore(equalityQuery, {}, evidence)
builder:addClaim(
	LifterIR.Entity.program(),
	wordsEqual,
	"unproven",
	true,
	evidence,
	nil,
	nil,
	equalityQuery
)
local equalityObligation = builder:addObligation(
	"numeric_domain",
	LifterIR.Entity.program(),
	"open",
	"readable_luau",
	"the solver must establish the exact word identity",
	equalityQuery
)
local equalityRequirement = builder.program.obligations[equalityObligation + 1].requirement
assert(
	equalityRequirement.kind == "prove_true" and equalityRequirement.predicate == wordsEqual,
	"obligation requirement did not bind its solver-neutral query goal"
)
local modelQuery = builder:addQuery("find_model", {}, wordsEqual)
local model = builder:addSolverModel(modelQuery, {
	LifterIR.SolverModelBinding(
		maxWordLeft,
		LifterIR.SolverModelValue.bitVector("18446744073709551615", 64)
	),
}, evidence)
builder:addCertificate(modelQuery, "imported", "proved", evidence, "fixture:generic-model", model)
builder:addSolverTerm(LifterIR.SolverSort.real(), LifterIR.SolverTerm.realLiteral("-3", "2"))
builder:addSolverTerm(
	LifterIR.SolverSort.integer(),
	LifterIR.SolverTerm.integerLiteral("9223372036854775808")
)

builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(chooseMax, chooseEntry)
builder:setFunctionEntry(identityPackFunction, identityBlock)
builder:setFunctionEntry(firstVarargFunction, firstVarargBlock)
builder:setFunctionEntry(forwardOpenFunction, forwardOpenBlock)
builder:setFunctionEntry(callWithVarargsFunction, callWithVarargsBlock)
builder:setFunctionEntry(prefixVarargsFunction, prefixVarargsBlock)
builder:setFunctionEntry(earlyReturnLoopFunction, earlyEntry)

local _, exportResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(chooseMax),
	{ { type = LifterIR.Types.functionValue(), name_hint = "exported" } },
	{ effects = pure, evidence = evidence }
)
local exported = exportResults[1]
local _, opaqueLeftResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("9")),
	{ { type = LifterIR.Types.integer(), name_hint = "opaque_left" } },
	{ effects = pure, evidence = evidence }
)
local _, opaqueRightResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("4")),
	{ { type = LifterIR.Types.integer(), name_hint = "opaque_right" } },
	{ effects = pure, evidence = evidence }
)
local _, opaqueDifferenceResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.binary("subtract", opaqueLeftResults[1], opaqueRightResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "opaque_difference" } },
	{ effects = pure, evidence = evidence }
)
local _, opaqueExpectedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.constant(LifterIR.Literal.integer("5")),
	{ { type = LifterIR.Types.integer(), name_hint = "opaque_expected" } },
	{ effects = pure, evidence = evidence }
)
local _, chunkConditionResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.binary("equal", opaqueDifferenceResults[1], opaqueExpectedResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "live_control_path" } },
	{ effects = pure, evidence = evidence }
)
local chunkCondition = chunkConditionResults[1]
local _, deadMarkerResults = builder:addInstruction(
	chunkDead,
	LifterIR.Operation.constant(LifterIR.Literal.string("dead_control_path")),
	{ { type = LifterIR.Types.string(), name_hint = "dead_control_path" } },
	{ effects = pure, evidence = evidence }
)
local deadMarker = deadMarkerResults[1]
local _, deadLeftResults = builder:addInstruction(
	chunkDead,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = LifterIR.Types.integer(), name_hint = "dead_left" } },
	{ effects = pure, evidence = evidence }
)
local _, deadRightResults = builder:addInstruction(
	chunkDead,
	LifterIR.Operation.constant(LifterIR.Literal.integer("2")),
	{ { type = LifterIR.Types.integer(), name_hint = "dead_right" } },
	{ effects = pure, evidence = evidence }
)
local deadBitInstruction = builder:addInstruction(
	chunkDead,
	LifterIR.Operation.binary("bit_and", deadLeftResults[1], deadRightResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "dead_bit_result" } },
	{ effects = pure, evidence = evidence }
)
builder:addObligation(
	"target_support",
	LifterIR.Entity.instruction(deadBitInstruction),
	"open",
	"readable_luau",
	"unsupported operation is confined to the proved dead path"
)

builder:addInstruction(
	chooseEntry,
	LifterIR.Operation.constant(LifterIR.Literal.nilValue()),
	{ { type = LifterIR.Types.nilValue(), name_hint = "unused_nil" } },
	{ effects = pure, evidence = evidence }
)
builder:addInstruction(
	chooseEntry,
	LifterIR.Operation.makeTable(),
	{ { type = LifterIR.Types.table(), name_hint = "unused_table" } },
	{ effects = LifterIR.Effects.tableConstructor(), evidence = evidence }
)

local _, comparisonResults = builder:addInstruction(
	chooseEntry,
	LifterIR.Operation.binary("greater", left, right),
	{ { type = LifterIR.Types.boolean(), name_hint = "left_is_greater" } },
	{ effects = pure, evidence = evidence }
)
local leftIsGreater = comparisonResults[1]

local _, reverseComparisonResults = builder:addInstruction(
	chooseCompareRight,
	LifterIR.Operation.binary("greater", right, left),
	{ { type = LifterIR.Types.boolean(), name_hint = "right_is_greater" } },
	{ effects = pure, evidence = evidence }
)
local rightIsGreater = reverseComparisonResults[1]

local _, identityReferenceResults = builder:addInstruction(
	chooseJoin,
	LifterIR.Operation.functionRef(identityPackFunction),
	{ { type = LifterIR.Types.functionValue(), name_hint = "identity_pack" } },
	{ effects = pure, evidence = evidence }
)
local identityReference = identityReferenceResults[1]
local _, identityResults = builder:addOpenCall(
	chooseJoin,
	identityReference,
	{ chosen },
	{
		effects = LifterIR.Effects.dynamicCall(),
		evidence = evidence,
		result_pack_shape = LifterIR.PackShape.closed({ LifterIR.Types.number() }),
	}
)
local _, normalizedChosenResults = builder:addInstruction(
	chooseJoin,
	LifterIR.Operation.adjustPack(identityResults),
	{ { type = LifterIR.Types.number(), name_hint = "normalized_chosen" } },
	{ effects = pure, evidence = evidence }
)
local normalizedChosen = normalizedChosenResults[1]

local _, firstVarargReferenceResults = builder:addInstruction(
	chooseJoin,
	LifterIR.Operation.functionRef(firstVarargFunction),
	{ { type = LifterIR.Types.functionValue(), name_hint = "first_vararg" } },
	{ effects = pure, evidence = evidence }
)
local firstVarargReference = firstVarargReferenceResults[1]
local _, confirmedChosenResults = builder:addInstruction(
	chooseJoin,
	LifterIR.Operation.call(firstVarargReference, { normalizedChosen }, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.number(), name_hint = "confirmed_chosen" } },
	{
		effects = LifterIR.Effects.dynamicCall(),
		evidence = evidence,
	}
)
local confirmedChosen = confirmedChosenResults[1]

local _, forwardReferenceResults = builder:addInstruction(
	chooseJoin,
	LifterIR.Operation.functionRef(forwardOpenFunction),
	{ { type = LifterIR.Types.functionValue(), name_hint = "forward_open" } },
	{ effects = pure, evidence = evidence }
)
local forwardReference = forwardReferenceResults[1]
local _, forwardedChosenResults = builder:addInstruction(
	chooseJoin,
	LifterIR.Operation.call(forwardReference, { confirmedChosen }, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.number(), name_hint = "forwarded_chosen" } },
	{
		effects = LifterIR.Effects.dynamicCall(),
		evidence = evidence,
	}
)
local forwardedChosen = forwardedChosenResults[1]

local _, callWithVarargsReferenceResults = builder:addInstruction(
	chooseJoin,
	LifterIR.Operation.functionRef(callWithVarargsFunction),
	{ { type = LifterIR.Types.functionValue(), name_hint = "call_with_varargs" } },
	{ effects = pure, evidence = evidence }
)
local callWithVarargsReference = callWithVarargsReferenceResults[1]
local _, expandedChosenResults = builder:addInstruction(
	chooseJoin,
	LifterIR.Operation.call(callWithVarargsReference, { forwardedChosen }, LifterIR.ResultArity.fixed(1)),
	{ { type = LifterIR.Types.number(), name_hint = "expanded_chosen" } },
	{
		effects = LifterIR.Effects.dynamicCall(),
		evidence = evidence,
	}
)
local expandedChosen = expandedChosenResults[1]

local _, prefixZeroResults = builder:addInstruction(
	chooseJoin,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = LifterIR.Types.integer(), name_hint = "prefix_zero" } },
	{ effects = pure, evidence = evidence }
)
local prefixZero = prefixZeroResults[1]
local _, prefixVarargsReferenceResults = builder:addInstruction(
	chooseJoin,
	LifterIR.Operation.functionRef(prefixVarargsFunction),
	{ { type = LifterIR.Types.functionValue(), name_hint = "prefix_varargs" } },
	{ effects = pure, evidence = evidence }
)
local prefixVarargsReference = prefixVarargsReferenceResults[1]
local _, prefixedResults = builder:addInstruction(
	chooseJoin,
	LifterIR.Operation.call(
		prefixVarargsReference,
		{ prefixZero, expandedChosen },
		LifterIR.ResultArity.fixed(2)
	),
	{
		{ type = LifterIR.Types.integer(), name_hint = "returned_prefix" },
		{ type = LifterIR.Types.number(), name_hint = "prefixed_chosen" },
	},
	{
		effects = LifterIR.Effects.dynamicCall(),
		evidence = evidence,
	}
)
local prefixedChosen = prefixedResults[2]

local _, firstValueResults = builder:addInstruction(
	firstVarargBlock,
	LifterIR.Operation.adjustPack(firstVarargs),
	{ { type = LifterIR.Types.number(), name_hint = "first" } },
	{ effects = pure, evidence = evidence }
)
local firstValue = firstValueResults[1]

local _, forwardIdentityReferenceResults = builder:addInstruction(
	forwardOpenBlock,
	LifterIR.Operation.functionRef(identityPackFunction),
	{ { type = LifterIR.Types.functionValue(), name_hint = "identity_pack" } },
	{ effects = pure, evidence = evidence }
)
local forwardIdentityReference = forwardIdentityReferenceResults[1]
local _, forwardedResults = builder:addOpenCall(
	forwardOpenBlock,
	forwardIdentityReference,
	{ forwardValue },
	{
		effects = LifterIR.Effects.dynamicCall(),
		evidence = evidence,
	}
)

local _, callWithVarargsTargetResults = builder:addInstruction(
	callWithVarargsBlock,
	LifterIR.Operation.functionRef(firstVarargFunction),
	{ { type = LifterIR.Types.functionValue(), name_hint = "first_vararg" } },
	{ effects = pure, evidence = evidence }
)
local callWithVarargsTarget = callWithVarargsTargetResults[1]
local _, expandedFirstResults = builder:addInstruction(
	callWithVarargsBlock,
	LifterIR.Operation.call(callWithVarargsTarget, {}, LifterIR.ResultArity.fixed(1), callWithVarargsPack),
	{ { type = LifterIR.Types.number(), name_hint = "expanded_first" } },
	{
		effects = LifterIR.Effects.dynamicCall(),
		evidence = evidence,
	}
)
local expandedFirst = expandedFirstResults[1]

local _, loopStartResults = builder:addInstruction(
	chooseJoin,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = LifterIR.Types.integer(), name_hint = "loop_start" } },
	{ effects = pure, evidence = evidence }
)
local loopStart = loopStartResults[1]

local _, loopLimitResults = builder:addInstruction(
	chooseLoopHeader,
	LifterIR.Operation.constant(LifterIR.Literal.integer("2")),
	{ { type = LifterIR.Types.integer(), name_hint = "loop_limit" } },
	{ effects = pure, evidence = evidence }
)
local loopLimit = loopLimitResults[1]
local _, loopConditionResults = builder:addInstruction(
	chooseLoopHeader,
	LifterIR.Operation.binary("greater_equal", loopCounter, loopLimit),
	{ { type = LifterIR.Types.boolean(), name_hint = "loop_finished" } },
	{ effects = pure, evidence = evidence }
)
local loopFinished = loopConditionResults[1]

local _, loopStepResults = builder:addInstruction(
	chooseLoopBody,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = LifterIR.Types.integer(), name_hint = "loop_step" } },
	{ effects = pure, evidence = evidence }
)
local loopStep = loopStepResults[1]
local _, nextCounterResults = builder:addInstruction(
	chooseLoopBody,
	LifterIR.Operation.binary("add", loopCounter, loopStep),
	{ { type = LifterIR.Types.integer(), name_hint = "next_counter" } },
	{ effects = pure, evidence = evidence }
)
local nextCounter = nextCounterResults[1]
local _, bodyLoopLimitResults = builder:addInstruction(
	chooseLoopBody,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = LifterIR.Types.integer(), name_hint = "body_loop_limit" } },
	{ effects = pure, evidence = evidence }
)
local _, bodyLoopFinishedResults = builder:addInstruction(
	chooseLoopBody,
	LifterIR.Operation.binary("greater_equal", nextCounter, bodyLoopLimitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "body_loop_finished" } },
	{ effects = pure, evidence = evidence }
)
local bodyLoopFinished = bodyLoopFinishedResults[1]
local _, breakZeroResults = builder:addInstruction(
	chooseBreakPrep,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = LifterIR.Types.integer(), name_hint = "break_zero" } },
	{ effects = pure, evidence = evidence }
)
local _, adjustedBreakResults = builder:addInstruction(
	chooseBreakPrep,
	LifterIR.Operation.binary("add", breakCandidate, breakZeroResults[1]),
	{ { type = LifterIR.Types.number(), name_hint = "adjusted_break" } },
	{ effects = pure, evidence = evidence }
)

local _, earlyZeroResults = builder:addInstruction(
	earlyEntry,
	LifterIR.Operation.constant(LifterIR.Literal.integer("0")),
	{ { type = LifterIR.Types.integer(), name_hint = "early_zero" } },
	{ effects = pure, evidence = evidence }
)
local _, earlyLimitResults = builder:addInstruction(
	earlyHeader,
	LifterIR.Operation.constant(LifterIR.Literal.integer("3")),
	{ { type = LifterIR.Types.integer(), name_hint = "early_limit" } },
	{ effects = pure, evidence = evidence }
)
local _, earlyDoneResults = builder:addInstruction(
	earlyHeader,
	LifterIR.Operation.binary("greater_equal", earlyCounter, earlyLimitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "early_done" } },
	{ effects = pure, evidence = evidence }
)
local _, earlyStepResults = builder:addInstruction(
	earlyBody,
	LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
	{ { type = LifterIR.Types.integer(), name_hint = "early_step" } },
	{ effects = pure, evidence = evidence }
)
local _, earlyNextResults = builder:addInstruction(
	earlyBody,
	LifterIR.Operation.binary("add", earlyCounter, earlyStepResults[1]),
	{ { type = LifterIR.Types.integer(), name_hint = "early_next" } },
	{ effects = pure, evidence = evidence }
)
local _, earlyReturnLimitResults = builder:addInstruction(
	earlyBody,
	LifterIR.Operation.constant(LifterIR.Literal.integer("2")),
	{ { type = LifterIR.Types.integer(), name_hint = "early_return_limit" } },
	{ effects = pure, evidence = evidence }
)
local _, earlyShouldReturnResults = builder:addInstruction(
	earlyBody,
	LifterIR.Operation.binary("greater_equal", earlyNextResults[1], earlyReturnLimitResults[1]),
	{ { type = LifterIR.Types.boolean(), name_hint = "early_should_return" } },
	{ effects = pure, evidence = evidence }
)

builder:finalizeBlock(
	chunkBlock,
	LifterIR.Terminator.branch(
		chunkCondition,
		LifterIR.Edge(chunkLive, {}),
		LifterIR.Edge(chunkDead, {})
	)
)
builder:finalizeBlock(chunkLive, LifterIR.Terminator.returnValues({ exported }))
builder:finalizeBlock(chunkDead, LifterIR.Terminator.returnValues({ deadMarker }))
builder:finalizeBlock(identityBlock, LifterIR.Terminator.returnPack(identityVarargs))
builder:finalizeBlock(firstVarargBlock, LifterIR.Terminator.returnValues({ firstValue }))
builder:finalizeBlock(forwardOpenBlock, LifterIR.Terminator.returnPack(forwardedResults))
builder:finalizeBlock(callWithVarargsBlock, LifterIR.Terminator.returnValues({ expandedFirst }))
builder:finalizeBlock(prefixVarargsBlock, LifterIR.Terminator.returnExpanded({ prefixValue }, prefixVarargsPack))
builder:finalizeBlock(
	chooseEntry,
	LifterIR.Terminator.branch(
		leftIsGreater,
		LifterIR.Edge(chooseLeft, { left }),
		LifterIR.Edge(chooseCompareRight, {})
	)
)
builder:finalizeBlock(chooseLeft, LifterIR.Terminator.jump(LifterIR.Edge(chooseLeftPass, { leftCandidate })))
builder:finalizeBlock(
	chooseCompareRight,
	LifterIR.Terminator.branch(
		rightIsGreater,
		LifterIR.Edge(chooseRight, { right }),
		LifterIR.Edge(chooseTie, { left })
	)
)
builder:finalizeBlock(chooseRight, LifterIR.Terminator.jump(LifterIR.Edge(chooseRightPass, { rightCandidate })))
builder:finalizeBlock(chooseTie, LifterIR.Terminator.jump(LifterIR.Edge(chooseTiePass, { tieCandidate })))
builder:finalizeBlock(chooseLeftPass, LifterIR.Terminator.jump(LifterIR.Edge(chooseJoin, { forwardedLeft })))
builder:finalizeBlock(chooseRightPass, LifterIR.Terminator.jump(LifterIR.Edge(chooseNestedJoin, { forwardedRight })))
builder:finalizeBlock(chooseTiePass, LifterIR.Terminator.jump(LifterIR.Edge(chooseNestedJoin, { forwardedTie })))
builder:finalizeBlock(chooseNestedJoin, LifterIR.Terminator.jump(LifterIR.Edge(chooseJoin, { nestedChosen })))
builder:finalizeBlock(
	chooseJoin,
	LifterIR.Terminator.jump(LifterIR.Edge(chooseLoopHeader, { prefixedChosen, loopStart }))
)
builder:finalizeBlock(
	chooseLoopHeader,
	LifterIR.Terminator.branch(
		loopFinished,
		LifterIR.Edge(chooseReturn, { loopChosen }),
		LifterIR.Edge(chooseLoopBody, {})
	)
)
builder:finalizeBlock(
	chooseLoopBody,
	LifterIR.Terminator.branch(
		bodyLoopFinished,
		LifterIR.Edge(chooseBreakPrep, { loopChosen }),
		LifterIR.Edge(chooseLoopHeader, { loopChosen, nextCounter })
	)
)
builder:finalizeBlock(
	chooseBreakPrep,
	LifterIR.Terminator.jump(LifterIR.Edge(chooseBreakForward, { adjustedBreakResults[1] }))
)
builder:finalizeBlock(
	chooseBreakForward,
	LifterIR.Terminator.jump(LifterIR.Edge(chooseReturn, { forwardedBreak }))
)
builder:finalizeBlock(chooseReturn, LifterIR.Terminator.returnValues({ returned }))
builder:finalizeBlock(earlyEntry, LifterIR.Terminator.jump(LifterIR.Edge(earlyHeader, { earlyZeroResults[1] })))
builder:finalizeBlock(
	earlyHeader,
	LifterIR.Terminator.branch(
		earlyDoneResults[1],
		LifterIR.Edge(earlyExit, { earlyCounter }),
		LifterIR.Edge(earlyBody, {})
	)
)
builder:finalizeBlock(
	earlyBody,
	LifterIR.Terminator.branch(
		earlyShouldReturnResults[1],
		LifterIR.Edge(earlyReturn, { earlyNextResults[1] }),
		LifterIR.Edge(earlyHeader, { earlyNextResults[1] })
	)
)
builder:finalizeBlock(earlyReturn, LifterIR.Terminator.returnValues({ earlyReturned }))
builder:finalizeBlock(earlyExit, LifterIR.Terminator.returnValues({ earlyExhausted }))

builder:finalizeFunction(chunk)
builder:finalizeFunction(chooseMax)
builder:finalizeFunction(identityPackFunction)
builder:finalizeFunction(firstVarargFunction)
builder:finalizeFunction(forwardOpenFunction)
builder:finalizeFunction(callWithVarargsFunction)
builder:finalizeFunction(prefixVarargsFunction)
builder:finalizeFunction(earlyReturnLoopFunction)

local encoded = LifterIR.encodeJson(builder:finish(), true)
local decoded = serde.decode("json", encoded)
assert(decoded.schema_version == "lifter_ir_v1", "serialized schema version did not round-trip")
assert(decoded.program_id == "generic-luau-choose-max-module", "serialized program ID did not round-trip")
fs.writeFile(outputPath, encoded .. "\n")
