--!strict

local AstFrontend = require("./ast_frontend")
local LifterIR = require("./lifter_ir")

for _, special in { "nan", "positive_infinity", "negative_infinity" } do
	local literal = LifterIR.Literal.specialNumber(special)
	assert(literal.special_number == special, "special numeric literal lost its domain tag")
	assert(
		string.find(LifterIR.encodeJson(literal), `"special_number":"{special}"`, 1, true) ~= nil,
		"special numeric literal did not use the shared JSON tag"
	)
end
local invalidSpecialNumberAccepted = pcall(function()
	LifterIR.Literal.specialNumber("infinity")
end)
assert(not invalidSpecialNumberAccepted, "Luau builder accepted an ambiguous special numeric literal")

local explicitShift = LifterIR.Operation.binary(
	"shift_left",
	0,
	1,
	"primitive",
	LifterIR.ShiftBehavior.zeroSaturating
)
assert(explicitShift.binary.shift_behavior == "zero_saturating", "Luau builder dropped explicit shift behavior")
local missingShiftBehaviorAccepted = pcall(function()
	LifterIR.Operation.binary("shift_left", 0, 1, "primitive")
end)
assert(not missingShiftBehaviorAccepted, "Luau builder accepted a shift without explicit behavior")
local nonshiftBehaviorAccepted = pcall(function()
	LifterIR.Operation.binary("bit_and", 0, 1, "primitive", LifterIR.ShiftBehavior.luauBit32)
end)
assert(not nonshiftBehaviorAccepted, "Luau builder accepted shift behavior on a nonshift operation")
local unknownShiftBehaviorAccepted = pcall(function()
	LifterIR.Operation.binary("shift_right", 0, 1, "primitive", "masked_count")
end)
assert(not unknownShiftBehaviorAccepted, "Luau builder accepted an unknown shift behavior")

local dynamicIdentity = LifterIR.SolverModelValue.dynamicIdentity(7)
assert(dynamicIdentity.dynamic_identity == 7, "solver dynamic model identity lost its class ID")
assert(
	string.find(LifterIR.encodeJson(dynamicIdentity), '"dynamic_identity":7', 1, true) ~= nil,
	"solver dynamic model identity did not use the shared JSON tag"
)
local oversizedDynamicIdentityAccepted = pcall(function()
	LifterIR.SolverModelValue.dynamicIdentity(4294967296)
end)
assert(not oversizedDynamicIdentityAccepted, "Luau builder accepted a dynamic identity outside the Zig u32 contract")

local conditionalTerm = LifterIR.SolverTerm.ifThenElse(0, 1, 2)
assert(conditionalTerm.if_then_else.condition == 0, "solver conditional lost its condition")
assert(conditionalTerm.if_then_else.then_term == 1, "solver conditional lost its then term")
assert(conditionalTerm.if_then_else.else_term == 2, "solver conditional lost its else term")
assert(
	string.find(LifterIR.encodeJson(conditionalTerm), '"if_then_else"', 1, true) ~= nil,
	"solver conditional did not use the shared JSON tag"
)

local dynamicTruthiness = LifterIR.SolverTerm.dynamicTruthiness(3)
assert(dynamicTruthiness.dynamic_truthiness == 3, "solver dynamic truthiness lost its operand")
assert(
	string.find(LifterIR.encodeJson(dynamicTruthiness), '"dynamic_truthiness":3', 1, true) ~= nil,
	"solver dynamic truthiness did not use the shared JSON tag"
)

local dynamicNumberIsNaN = LifterIR.SolverTerm.dynamicNumberIsNaN(4)
assert(dynamicNumberIsNaN.dynamic_number_is_nan == 4, "solver dynamic numeric predicate lost its operand")
assert(
	string.find(LifterIR.encodeJson(dynamicNumberIsNaN), '"dynamic_number_is_nan":4', 1, true) ~= nil,
	"solver dynamic numeric predicate did not use the shared JSON tag"
)

local invertedTerm = LifterIR.SolverTerm.bitVectorNot(3)
assert(invertedTerm.bit_vector_not == 3, "solver bit-vector NOT lost its operand")
local extractedTerm = LifterIR.SolverTerm.bitVectorExtract(4, 11, 7)
assert(extractedTerm.bit_vector_extract.operand == 4, "solver bit-vector extraction lost its operand")
assert(extractedTerm.bit_vector_extract.high == 11, "solver bit-vector extraction lost its high index")
assert(extractedTerm.bit_vector_extract.low == 7, "solver bit-vector extraction lost its low index")
local concatenatedTerm = LifterIR.SolverTerm.bitVectorConcat(5, 6)
assert(concatenatedTerm.bit_vector_concat.high == 5, "solver bit-vector concatenation lost its high operand")
assert(concatenatedTerm.bit_vector_concat.low == 6, "solver bit-vector concatenation lost its low operand")
local extendedTerm = LifterIR.SolverTerm.bitVectorExtend(7, 8, "sign")
assert(extendedTerm.bit_vector_extend.extra_bits == 8, "solver bit-vector extension lost its width")
assert(extendedTerm.bit_vector_extend.mode == "sign", "solver bit-vector extension lost its mode")
local rotatedTerm = LifterIR.SolverTerm.bitVectorRotate(8, 9, "left")
assert(rotatedTerm.bit_vector_rotate.operand == 8, "solver bit-vector rotation lost its operand")
assert(rotatedTerm.bit_vector_rotate.amount == 9, "solver bit-vector rotation lost its amount")
assert(rotatedTerm.bit_vector_rotate.direction == "left", "solver bit-vector rotation lost its direction")
local wordConversion = LifterIR.SolverTerm.integerToBitVector(10)
assert(wordConversion.integer_to_bit_vector == 10, "solver integer-to-word conversion lost its operand")
local signedConversion = LifterIR.SolverTerm.bitVectorToInteger(11, true)
assert(signedConversion.bit_vector_to_integer.operand == 11, "solver word-to-integer conversion lost its operand")
assert(signedConversion.bit_vector_to_integer.signed == true, "solver word-to-integer conversion lost its signed mode")
local negatedTerm = LifterIR.SolverTerm.arithmeticNegate(12)
assert(negatedTerm.arithmetic_negate == 12, "solver arithmetic negation lost its operand")
local nonzeroTerm = LifterIR.SolverTerm.isNonzero(13)
assert(nonzeroTerm.is_nonzero == 13, "solver nonzero predicate lost its operand")
local valueDefinitionTerm = LifterIR.SolverTerm.valueDefinition(9, 13)
assert(valueDefinitionTerm.value_definition.value == 9, "solver value definition lost its IR identity")
assert(valueDefinitionTerm.value_definition.expression == 13, "solver value definition lost its expression")
assert(valueDefinitionTerm.value_definition.valid_when == nil, "unconditional solver value definition gained a guard")
local guardedValueDefinitionTerm = LifterIR.SolverTerm.valueDefinition(9, 13, 17)
assert(guardedValueDefinitionTerm.value_definition.valid_when == 17, "solver value definition lost its semantic guard")
local divisionTerm = LifterIR.SolverTerm.division("integer_euclidean", 14, 15, 16)
assert(divisionTerm.division.left == 14, "solver division lost its left operand")
assert(divisionTerm.division.right == 15, "solver division lost its right operand")
assert(divisionTerm.division.defined_by == 16, "solver division lost its definedness predicate")
assert(divisionTerm.division.mode == "integer_euclidean", "solver division lost its quotient mode")
local floorDivisionTerm = LifterIR.SolverTerm.division("integer_floor", 14, 15, 16)
assert(floorDivisionTerm.division.mode == "integer_floor", "solver division lost its floor convention")
local remainderTerm = LifterIR.SolverTerm.remainder("bit_vector_signed_divisor", 17, 18, 19)
assert(remainderTerm.remainder.left == 17, "solver remainder lost its left operand")
assert(remainderTerm.remainder.right == 18, "solver remainder lost its right operand")
assert(remainderTerm.remainder.defined_by == 19, "solver remainder lost its definedness predicate")
assert(remainderTerm.remainder.mode == "bit_vector_signed_divisor", "solver remainder lost its convention")
local invalidExtractAccepted = pcall(function()
	LifterIR.SolverTerm.bitVectorExtract(0, 2, 3)
end)
assert(not invalidExtractAccepted, "Luau builder accepted reversed bit-vector extraction bounds")
local invalidRotationAccepted = pcall(function()
	LifterIR.SolverTerm.bitVectorRotate(0, 1, "around")
end)
assert(not invalidRotationAccepted, "Luau builder accepted an unknown bit-vector rotation direction")
local invalidDivisionAccepted = pcall(function()
	LifterIR.SolverTerm.division("source_divide", 0, 1, 2)
end)
assert(not invalidDivisionAccepted, "Luau builder accepted an ambiguous division mode")
local invalidRemainderAccepted = pcall(function()
	LifterIR.SolverTerm.remainder("source_modulo", 0, 1, 2)
end)
assert(not invalidRemainderAccepted, "Luau builder accepted an ambiguous remainder mode")
local legacyModuloAccepted = pcall(function()
	LifterIR.SolverTerm.binary("modulo", 0, 1)
end)
assert(not legacyModuloAccepted, "Luau builder accepted unguarded legacy solver modulo")

local unknown = AstFrontend.tryLift({
	root = {
		type = "AstStatBlock",
		location = "0,0 - 0,1",
		body = {
			{ type = "AstStatUnknown", location = "0,0 - 0,1" },
		},
	},
}, {
	program_id = "frontend-unknown-statement-test",
	source_name = "frontend-unknown-statement-test",
})
assert(unknown.program == nil and #unknown.diagnostics == 1, "unknown statement did not produce one typed diagnostic")
assert(unknown.diagnostics[1].code == "unsupported_statement", "unknown statement diagnostic changed code")
assert(unknown.diagnostics[1].location == "0,0 - 0,1", "unknown statement diagnostic lost its source location")

local function expectProtocolRejection(statementType: string, code: string)
	local result = AstFrontend.tryLift({
		root = {
			type = "AstStatBlock",
			location = "0,0 - 0,1",
			body = {
				{ type = statementType, location = "0,0 - 0,1" },
			},
		},
	}, {
		program_id = `frontend-{statementType}-test`,
		source_name = `frontend-{statementType}-test`,
	})
	assert(result.program == nil and #result.diagnostics == 1, `{statementType} did not produce one typed diagnostic`)
	assert(result.diagnostics[1].code == code, `{statementType} diagnostic changed code`)
	assert(result.diagnostics[1].location == "0,0 - 0,1", `{statementType} diagnostic lost its source location`)
end

expectProtocolRejection("AstStatFor", "malformed_numeric_for")
expectProtocolRejection("AstStatForIn", "malformed_generic_for")

local instantiated = AstFrontend.tryLift({
	root = {
		type = "AstStatBlock",
		location = "0,0 - 0,12",
		body = {
			{
				type = "AstStatReturn",
				location = "0,0 - 0,12",
				list = {
					{
						type = "AstExprInstantiate",
						location = "0,7 - 0,12",
						expr = { type = "AstExprConstantNumber", location = "0,7 - 0,8", value = 7 },
						typeArguments = {},
					},
				},
			},
		},
	},
}, {
	program_id = "frontend-runtime-transparent-instantiation",
	source_name = "frontend-runtime-transparent-instantiation",
})
assert(instantiated.program ~= nil and #instantiated.diagnostics == 0, "generic instantiation was not runtime-transparent")

local exactInteger = AstFrontend.tryLift({
	root = {
		type = "AstStatBlock",
		location = "0,0 - 0,28",
		body = {
			{
				type = "AstStatReturn",
				location = "0,0 - 0,28",
				list = {
					{ type = "AstExprConstantInteger", location = "0,7 - 0,27", value = "18446744073709551615" },
				},
			},
		},
	},
}, {
	program_id = "frontend-exact-integer",
	source_name = "frontend-exact-integer",
})
assert(exactInteger.program ~= nil and #exactInteger.diagnostics == 0, "exact integer node was not admitted")
local exactOperation = (exactInteger.program :: any).instructions[1].operation
assert(exactOperation.constant.integer == "18446744073709551615", "exact integer transport lost precision")
assert((exactInteger.program :: any).values[1].type.bit_width == 65535, "exact integer transport made a false i64 claim")

local declaredClass = AstFrontend.tryLift({
	root = {
		type = "AstStatBlock",
		location = "0,0 - 1,8",
		body = {
			{ type = "AstStatDeclareClass", location = "0,0 - 0,20", name = "DeclaredOnly", props = {} },
			{ type = "AstStatReturn", location = "1,0 - 1,8", list = {} },
		},
	},
}, {
	program_id = "frontend-declared-class",
	source_name = "frontend-declared-class",
})
assert(declaredClass.program ~= nil and #declaredClass.diagnostics == 0, "type-only class declaration changed runtime admission")

expectProtocolRejection("AstStatError", "malformed_source_statement")

local expressionError = AstFrontend.tryLift({
	root = {
		type = "AstStatBlock",
		location = "0,0 - 0,12",
		body = {
			{
				type = "AstStatReturn",
				location = "0,0 - 0,12",
				list = {
					{ type = "AstExprError", location = "0,7 - 0,12" },
				},
			},
		},
	},
}, {
	program_id = "frontend-parser-expression-error",
	source_name = "frontend-parser-expression-error",
})
assert(expressionError.program == nil and expressionError.diagnostics[1].code == "malformed_source_expression", "parser expression error was not rejected")

local unreachableRecovery = AstFrontend.tryLift({
	root = {
		type = "AstStatBlock",
		location = "0,0 - 1,12",
		body = {
			{ type = "AstStatReturn", location = "0,0 - 0,8", list = {} },
			{
				type = "AstStatExpr",
				location = "1,0 - 1,12",
				expr = { type = "AstExprError", location = "1,0 - 1,12" },
			},
		},
	},
}, {
	program_id = "frontend-unreachable-parser-error",
	source_name = "frontend-unreachable-parser-error",
})
assert(
	unreachableRecovery.program == nil and unreachableRecovery.diagnostics[1].code == "malformed_source_expression",
	"dead-tail omission hid a parser recovery expression"
)

local nextIntrinsicLocation = 0
local function intrinsicNode(fields: any): any
	nextIntrinsicLocation += 1
	fields.location = `intrinsic:{nextIntrinsicLocation}`
	return fields
end

local function intrinsicGlobal(name: string): any
	return intrinsicNode({ type = "AstExprGlobal", global = name })
end

local function intrinsicMember(receiver: string, member: string): any
	return intrinsicNode({
		type = "AstExprIndexName",
		expr = intrinsicGlobal(receiver),
		index = member,
	})
end

local function intrinsicCall(callee: any, arguments: { any }): any
	return intrinsicNode({
		type = "AstExprCall",
		func = callee,
		args = arguments,
		self = false,
	})
end

local function intrinsicGroup(expression: any): any
	return intrinsicNode({ type = "AstExprGroup", expr = expression })
end

local function intrinsicVarargs(): any
	return intrinsicNode({ type = "AstExprVarargs" })
end

local function intrinsicNumber(value: number): any
	return intrinsicNode({ type = "AstExprConstantNumber", value = value })
end

local function intrinsicString(value: string): any
	return intrinsicNode({ type = "AstExprConstantString", value = value })
end

local function intrinsicNil(): any
	return intrinsicNode({ type = "AstExprConstantNil" })
end

local function intrinsicBool(value: boolean): any
	return intrinsicNode({ type = "AstExprConstantBool", value = value })
end

local function intrinsicLocal(name: string): any
	return intrinsicNode({ type = "AstLocal", name = name })
end

local function intrinsicLocalExpression(localNode: any): any
	return intrinsicNode({ type = "AstExprLocal", ["local"] = localNode })
end

local function intrinsicDocument(body: { any }): any
	return {
		root = intrinsicNode({
			type = "AstStatBlock",
			body = body,
		}),
	}
end

local intrinsicBindings = {}
for _, path in { "pcall", "xpcall", "coroutine.create", "coroutine.resume", "coroutine.yield", "error" } do
	table.insert(intrinsicBindings, {
		path = path,
		evidence = {
			kind = "frontend_proof",
			locator = `fixture:stable-{path}`,
		},
	})
end

local intrinsicLift = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatExpr",
		expr = intrinsicCall(intrinsicGlobal("pcall"), { intrinsicGlobal("target") }),
	}),
	intrinsicNode({
		type = "AstStatReturn",
		list = {
			intrinsicGroup(intrinsicCall(intrinsicGlobal("xpcall"), {
				intrinsicGlobal("target"),
				intrinsicGlobal("handler"),
			})),
			intrinsicGroup(intrinsicCall(intrinsicMember("coroutine", "create"), {
				intrinsicGlobal("target"),
			})),
			intrinsicGroup(intrinsicCall(intrinsicMember("coroutine", "resume"), {
				intrinsicGlobal("thread"),
				intrinsicVarargs(),
			})),
			intrinsicGroup(intrinsicCall(intrinsicMember("coroutine", "yield"), {
				intrinsicVarargs(),
			})),
			intrinsicCall(intrinsicGlobal("pcall"), {
				intrinsicGlobal("target"),
				intrinsicVarargs(),
			}),
		},
	}),
}), {
	program_id = "frontend-intrinsic-bindings",
	source_name = "frontend-intrinsic-bindings",
	intrinsic_bindings = intrinsicBindings,
})
assert(intrinsicLift.program ~= nil and #intrinsicLift.diagnostics == 0, "proven intrinsic calls were not lowered")
local intrinsicProgram = intrinsicLift.program :: any

local operationCounts: { [string]: number } = {}
local intrinsicInstructions = {}
for _, instruction in intrinsicProgram.instructions do
	for _, tag in { "protected_call", "coroutine_create", "coroutine_resume", "coroutine_yield" } do
		if instruction.operation[tag] ~= nil then
			operationCounts[tag] = (operationCounts[tag] or 0) + 1
			table.insert(intrinsicInstructions, instruction)
		end
	end
	local environmentGet = instruction.operation.environment_get
	if environmentGet ~= nil then
		assert(
			environmentGet.name ~= "pcall" and environmentGet.name ~= "xpcall" and environmentGet.name ~= "coroutine",
			"proven intrinsic lowering retained a mutable builtin lookup"
		)
	end
end
assert(operationCounts.protected_call == 3, "protected intrinsic calls changed operation count")
assert(operationCounts.coroutine_create == 1, "coroutine.create did not become one native operation")
assert(operationCounts.coroutine_resume == 1, "coroutine.resume did not become one native operation")
assert(operationCounts.coroutine_yield == 1, "coroutine.yield did not become one native operation")

local evidenceByLocator = {}
for _, evidence in intrinsicProgram.evidence do
	evidenceByLocator[evidence.locator] = evidence.id
end
for _, instruction in intrinsicInstructions do
	local path
	if instruction.operation.protected_call ~= nil then
		path = if instruction.operation.protected_call.error_handler == nil then "pcall" else "xpcall"
	elseif instruction.operation.coroutine_create ~= nil then
		path = "coroutine.create"
	elseif instruction.operation.coroutine_resume ~= nil then
		path = "coroutine.resume"
	else
		path = "coroutine.yield"
	end
	local intrinsicEvidence = evidenceByLocator[`fixture:stable-{path}`]
	assert(intrinsicEvidence ~= nil and table.find(instruction.evidence, intrinsicEvidence) ~= nil, `intrinsic {path} lost its proof evidence`)
	for index = 2, #instruction.evidence do
		assert(instruction.evidence[index - 1] < instruction.evidence[index], `intrinsic {path} evidence is not canonical`)
	end
end

local fixedStatusInstruction
local createInstruction
for _, instruction in intrinsicInstructions do
	if instruction.operation.protected_call ~= nil
		and instruction.operation.protected_call.error_handler == nil
		and instruction.pack_result == nil
	then
		fixedStatusInstruction = instruction
	elseif instruction.operation.coroutine_create ~= nil then
		createInstruction = instruction
	end
end
assert(fixedStatusInstruction ~= nil and #fixedStatusInstruction.results == 1, "discarded pcall did not retain its Boolean status result")
assert(intrinsicProgram.values[fixedStatusInstruction.results[1] + 1].type.kind == "boolean", "pcall status lost its Boolean domain")
assert(createInstruction ~= nil and #createInstruction.results == 1, "coroutine.create did not retain exactly one thread result")
assert(intrinsicProgram.values[createInstruction.results[1] + 1].type.kind == "thread", "coroutine.create result lost its thread domain")

local genericPcall = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatExpr",
		expr = intrinsicCall(intrinsicGlobal("pcall"), { intrinsicGlobal("target") }),
	}),
}), {
	program_id = "frontend-unproven-pcall",
	source_name = "frontend-unproven-pcall",
})
assert(genericPcall.program ~= nil, "unproven pcall did not retain generic call semantics")
local genericPcallKinds = { call = 0, protected_call = 0, pcall_lookup = 0 }
for _, instruction in (genericPcall.program :: any).instructions do
	if instruction.operation.call ~= nil then
		genericPcallKinds.call += 1
	elseif instruction.operation.protected_call ~= nil then
		genericPcallKinds.protected_call += 1
	elseif instruction.operation.environment_get ~= nil and instruction.operation.environment_get.name == "pcall" then
		genericPcallKinds.pcall_lookup += 1
	end
end
assert(genericPcallKinds.call == 1 and genericPcallKinds.protected_call == 0 and genericPcallKinds.pcall_lookup == 1, "syntax alone specialized pcall")

local errorBinding = intrinsicBindings[#intrinsicBindings]
local terminatingError = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatExpr",
		expr = intrinsicCall(intrinsicGlobal("error"), {
			intrinsicGlobal("message"),
			intrinsicNumber(0),
			intrinsicCall(intrinsicGlobal("extra"), {}),
		}),
	}),
}), {
	program_id = "frontend-terminating-error",
	source_name = "frontend-terminating-error",
	intrinsic_bindings = { errorBinding },
})
assert(terminatingError.program ~= nil and #terminatingError.diagnostics == 0, "proven error call did not become a terminator")
local terminatingProgram = terminatingError.program :: any
local terminatingBlock = terminatingProgram.blocks[1]
local thrown = terminatingBlock.terminator.throw_error
assert(thrown ~= nil and thrown.level == 0, "proven error call lost its exact level")
assert(#terminatingProgram.instructions == 4, "terminating error did not evaluate every argument")
assert(terminatingProgram.instructions[1].operation.environment_get.name == "message", "error message was not evaluated first")
assert(terminatingProgram.instructions[2].operation.constant.integer == "0", "error level was not evaluated second")
assert(terminatingProgram.instructions[3].operation.environment_get.name == "extra", "ignored open error argument was not evaluated")
assert(
	terminatingProgram.instructions[4].operation.call.result_arity.fixed == 0,
	"ignored open error argument did not use explicit discarded arity"
)
assert(thrown.value == terminatingProgram.instructions[1].results[1], "throw terminator lost message identity")
for index, instruction in terminatingProgram.instructions do
	assert(index == 4 or instruction.operation.call == nil, "proven terminating error retained a dynamic builtin call")
	local environmentGet = instruction.operation.environment_get
	assert(environmentGet == nil or environmentGet.name ~= "error", "proven terminating error retained a mutable builtin lookup")
end
local terminatingEvidence
for _, evidence in terminatingProgram.evidence do
	if evidence.locator == "fixture:stable-error" then
		terminatingEvidence = evidence.id
	end
end
assert(
	terminatingEvidence ~= nil and table.find(terminatingBlock.evidence, terminatingEvidence) ~= nil,
	"terminating error block lost manifest provenance"
)

for _, arguments in { {}, { intrinsicNil() }, { intrinsicNil(), intrinsicNil() } } do
	local omittedMessage = AstFrontend.tryLift(intrinsicDocument({
		intrinsicNode({
			type = "AstStatExpr",
			expr = intrinsicCall(intrinsicGlobal("error"), arguments),
		}),
	}), {
		program_id = "frontend-omitted-error-message",
		source_name = "frontend-omitted-error-message",
		intrinsic_bindings = { errorBinding },
	})
	assert(omittedMessage.program ~= nil, "omitted or nil error message was not represented")
	local omittedProgram = omittedMessage.program :: any
	local omittedThrow = omittedProgram.blocks[1].terminator.throw_error
	assert(omittedThrow ~= nil and omittedThrow.level == 1, "omitted error level lost its runtime default")
	assert(omittedProgram.values[omittedThrow.value + 1].type.kind == "nil_value", "omitted error message did not become nil")
end

local unprovenError = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatExpr",
		expr = intrinsicCall(intrinsicGlobal("error"), { intrinsicString("unproven"), intrinsicNumber(0) }),
	}),
}), {
	program_id = "frontend-unproven-error",
	source_name = "frontend-unproven-error",
})
assert(unprovenError.program ~= nil, "unproven error call was rejected")
local unprovenProgram = unprovenError.program :: any
local unprovenCalls = 0
local unprovenLookups = 0
for _, instruction in unprovenProgram.instructions do
	if instruction.operation.call ~= nil then
		unprovenCalls += 1
	elseif instruction.operation.environment_get ~= nil and instruction.operation.environment_get.name == "error" then
		unprovenLookups += 1
	end
end
assert(unprovenProgram.blocks[1].terminator.throw_error == nil, "syntax alone specialized error")
assert(unprovenCalls == 1 and unprovenLookups == 1, "unproven error did not retain mutable call semantics")

local fallbackLevels = {
	intrinsicGlobal("dynamic_level"),
	intrinsicNumber(0.5),
	intrinsicString("0"),
	intrinsicNode({ type = "AstExprUnary", op = "Minus", expr = intrinsicNumber(1) }),
	intrinsicGroup(intrinsicCall(intrinsicGlobal("level_factory"), {})),
}
local fallbackLevelKinds = { "dynamic", "number", "string", "number", "dynamic" }
for index, level in fallbackLevels do
	local fallback = AstFrontend.tryLift(intrinsicDocument({
		intrinsicNode({
			type = "AstStatExpr",
			expr = intrinsicCall(intrinsicGlobal("error"), { intrinsicString(`fallback-{index}`), level }),
		}),
	}), {
		program_id = `frontend-error-fallback-{index}`,
		source_name = `frontend-error-fallback-{index}`,
		intrinsic_bindings = { errorBinding },
	})
	assert(fallback.program ~= nil, `dynamic error level {index} was rejected instead of represented`)
	local fallbackProgram = fallback.program :: any
	local calls = 0
	local errorLookups = 0
	for _, instruction in fallbackProgram.instructions do
		if instruction.operation.call ~= nil then
			calls += 1
		elseif instruction.operation.environment_get ~= nil and instruction.operation.environment_get.name == "error" then
			errorLookups += 1
		end
	end
	local fallbackThrow = fallbackProgram.blocks[1].terminator.throw_error
	assert(
		fallbackThrow ~= nil and fallbackThrow.level == 0 and type(fallbackThrow.dynamic_level) == "number",
		`dynamic error level {index} did not become explicit nonreturning control`
	)
	assert(
		fallbackProgram.values[fallbackThrow.dynamic_level + 1].type.kind == fallbackLevelKinds[index],
		`dynamic error level {index} lost its value domain`
	)
	assert(calls == (if index == #fallbackLevels then 1 else 0), `dynamic error level {index} changed its producer calls`)
	assert(errorLookups == 0, `dynamic error level {index} retained a mutable error lookup`)
	assert(
		string.find(LifterIR.encodeJson(fallbackProgram), '"dynamic_level"', 1, true) ~= nil,
		`dynamic error level {index} did not serialize through the Luau contract`
	)
end

local expressionError = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatReturn",
		list = { intrinsicCall(intrinsicGlobal("error"), { intrinsicString("expression"), intrinsicNumber(0) }) },
	}),
}), {
	program_id = "frontend-expression-error",
	source_name = "frontend-expression-error",
	intrinsic_bindings = { errorBinding },
})
assert(expressionError.program ~= nil, "expression-context error call was rejected")
local expressionProgram = expressionError.program :: any
assert(expressionProgram.blocks[1].terminator.throw_error ~= nil, "return-context error did not become explicit nonreturning control")
assert(expressionProgram.blocks[1].terminator.return_pack == nil, "terminated return retained an unreachable result pack")

local exactOpenError = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatExpr",
		expr = intrinsicCall(intrinsicGlobal("error"), {
			intrinsicCall(intrinsicMember("coroutine", "create"), { intrinsicGlobal("target") }),
		}),
	}),
}), {
	program_id = "frontend-exact-open-error",
	source_name = "frontend-exact-open-error",
	intrinsic_bindings = { errorBinding, intrinsicBindings[3] },
})
assert(exactOpenError.program ~= nil, "authenticated exact-one error tail was rejected")
local exactOpenProgram = exactOpenError.program :: any
local exactOpenThrow = exactOpenProgram.blocks[1].terminator.throw_error
local exactOpenKinds = { coroutine_create = 0, pack_values = 0, adjust_pack = 0, call = 0, error_lookup = 0 }
for _, instruction in exactOpenProgram.instructions do
	for _, kind in { "coroutine_create", "pack_values", "adjust_pack", "call" } do
		if instruction.operation[kind] ~= nil then
			exactOpenKinds[kind] += 1
		end
	end
	if instruction.operation.environment_get ~= nil and instruction.operation.environment_get.name == "error" then
		exactOpenKinds.error_lookup += 1
	end
end
assert(exactOpenThrow ~= nil and exactOpenThrow.level == 1, "exact-one open tail lost omitted-level termination")
assert(exactOpenProgram.values[exactOpenThrow.value + 1].type.kind == "thread", "exact-one open tail lost its authenticated result type")
assert(
	exactOpenKinds.coroutine_create == 1
		and exactOpenKinds.pack_values == 1
		and exactOpenKinds.adjust_pack == 1
		and exactOpenKinds.call == 0
		and exactOpenKinds.error_lookup == 0,
	"exact-one open tail did not consume its pack directly into termination"
)

local exactThreadLocal = intrinsicNode({ type = "AstLocal", name = "thread" })
local exactPaddingLocal = intrinsicNode({ type = "AstLocal", name = "padding" })
local exactOpenAdjustment = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatLocal",
		vars = { exactThreadLocal, exactPaddingLocal },
		values = {
			intrinsicCall(intrinsicMember("coroutine", "create"), { intrinsicGlobal("target") }),
		},
	}),
	intrinsicNode({
		type = "AstStatReturn",
		list = {
			intrinsicNode({ type = "AstExprLocal", ["local"] = exactThreadLocal }),
			intrinsicNode({ type = "AstExprLocal", ["local"] = exactPaddingLocal }),
		},
	}),
}), {
	program_id = "frontend-exact-open-adjustment",
	source_name = "frontend-exact-open-adjustment",
	intrinsic_bindings = { intrinsicBindings[3] },
})
assert(exactOpenAdjustment.program ~= nil, "exact open value-list adjustment was rejected")
local exactAdjustmentProgram = exactOpenAdjustment.program :: any
local exactAdjustment
for _, instruction in exactAdjustmentProgram.instructions do
	if instruction.operation.adjust_pack ~= nil then
		exactAdjustment = instruction
	end
end
assert(exactAdjustment ~= nil and #exactAdjustment.results == 2, "exact open value list lost its requested adjustment")
assert(
	exactAdjustmentProgram.values[exactAdjustment.results[1] + 1].type.kind == "thread"
		and exactAdjustmentProgram.values[exactAdjustment.results[2] + 1].type.kind == "nil_value",
	"exact open value list lost its result type or nil padding"
)

local unresolvedOpenError = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatExpr",
		expr = intrinsicCall(intrinsicGlobal("error"), {
			intrinsicCall(intrinsicGlobal("pcall"), { intrinsicGlobal("target") }),
		}),
	}),
}), {
	program_id = "frontend-unresolved-open-error",
	source_name = "frontend-unresolved-open-error",
	intrinsic_bindings = { errorBinding, intrinsicBindings[1] },
})
assert(unresolvedOpenError.program ~= nil, "variable-result error tail was rejected instead of retained")
local unresolvedOpenProgram = unresolvedOpenError.program :: any
local unresolvedKinds = { protected_call = 0, call = 0, error_lookup = 0 }
for _, instruction in unresolvedOpenProgram.instructions do
	if instruction.operation.protected_call ~= nil then
		unresolvedKinds.protected_call += 1
	elseif instruction.operation.call ~= nil then
		unresolvedKinds.call += 1
	elseif instruction.operation.environment_get ~= nil and instruction.operation.environment_get.name == "error" then
		unresolvedKinds.error_lookup += 1
	end
end
assert(unresolvedOpenProgram.blocks[1].terminator.throw_error == nil, "variable-result open tail became a false termination claim")
assert(
	unresolvedKinds.protected_call == 1 and unresolvedKinds.call == 1 and unresolvedKinds.error_lookup == 1,
	"variable-result open tail did not retain its protected producer and ordinary error call"
)

local pcallAliasLocal = intrinsicLocal("invoke")
local createAliasLocal = intrinsicLocal("create")
local errorAliasLocal = intrinsicLocal("fail")
local aliasThreadLocal = intrinsicLocal("thread")
local aliasPaddingLocal = intrinsicLocal("padding")
local capturedAliasLocal = intrinsicLocal("captured")
local capturedAliasFunction = intrinsicNode({
	type = "AstExprFunction",
	args = {},
	vararg = false,
	body = intrinsicNode({
		type = "AstStatBlock",
		body = {
			intrinsicNode({
				type = "AstStatExpr",
				expr = intrinsicCall(intrinsicLocalExpression(errorAliasLocal), {
					intrinsicCall(intrinsicLocalExpression(createAliasLocal), { intrinsicGlobal("target") }),
				}),
			}),
		},
	}),
})
local immutableAliases = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({ type = "AstStatLocal", vars = { pcallAliasLocal }, values = { intrinsicGlobal("pcall") } }),
	intrinsicNode({ type = "AstStatLocal", vars = { createAliasLocal }, values = { intrinsicMember("coroutine", "create") } }),
	intrinsicNode({ type = "AstStatLocal", vars = { errorAliasLocal }, values = { intrinsicGlobal("error") } }),
	intrinsicNode({
		type = "AstStatExpr",
		expr = intrinsicCall(intrinsicLocalExpression(pcallAliasLocal), { intrinsicGlobal("target") }),
	}),
	intrinsicNode({
		type = "AstStatLocal",
		vars = { aliasThreadLocal, aliasPaddingLocal },
		values = { intrinsicCall(intrinsicLocalExpression(createAliasLocal), { intrinsicGlobal("target") }) },
	}),
	intrinsicNode({ type = "AstStatLocal", vars = { capturedAliasLocal }, values = { capturedAliasFunction } }),
	intrinsicNode({
		type = "AstStatReturn",
		list = {
			intrinsicLocalExpression(aliasThreadLocal),
			intrinsicLocalExpression(aliasPaddingLocal),
			intrinsicLocalExpression(capturedAliasLocal),
		},
	}),
}), {
	program_id = "frontend-immutable-intrinsic-aliases",
	source_name = "frontend-immutable-intrinsic-aliases",
	intrinsic_bindings = { intrinsicBindings[1], intrinsicBindings[3], errorBinding },
})
assert(immutableAliases.program ~= nil, "immutable intrinsic aliases were rejected")
local immutableAliasProgram = immutableAliases.program :: any
local aliasKinds = { protected_call = 0, coroutine_create = 0, call = 0, throw_error = 0 }
local aliasAdjustment
for _, instruction in immutableAliasProgram.instructions do
	for _, kind in { "protected_call", "coroutine_create", "call" } do
		if instruction.operation[kind] ~= nil then
			aliasKinds[kind] += 1
		end
	end
	if instruction.operation.adjust_pack ~= nil and #instruction.results == 2 then
		aliasAdjustment = instruction
	end
end
local capturedAliasFunctionRecord
local capturedAliasThrow
for _, functionRecord in immutableAliasProgram.functions do
	if functionRecord.name_hint == "captured" then
		capturedAliasFunctionRecord = functionRecord
	end
end
for _, block in immutableAliasProgram.blocks do
	if block.terminator.throw_error ~= nil then
		aliasKinds.throw_error += 1
		capturedAliasThrow = block.terminator.throw_error
	end
end
assert(
	aliasKinds.protected_call == 1 and aliasKinds.coroutine_create == 2 and aliasKinds.call == 0 and aliasKinds.throw_error == 1,
	"immutable aliases did not reuse intrinsic operation or termination owners"
)
assert(aliasAdjustment ~= nil, "exact-one intrinsic alias lost open-pack adjustment")
assert(
	immutableAliasProgram.values[aliasAdjustment.results[1] + 1].type.kind == "thread"
		and immutableAliasProgram.values[aliasAdjustment.results[2] + 1].type.kind == "nil_value",
	"exact-one intrinsic alias lost result shape"
)
assert(
	capturedAliasFunctionRecord ~= nil and #capturedAliasFunctionRecord.captures == 2,
	"captured immutable intrinsic alias lost lexical ownership"
)
assert(
	capturedAliasThrow ~= nil
		and capturedAliasThrow.level == 1
		and immutableAliasProgram.values[capturedAliasThrow.value + 1].type.kind == "thread",
	"captured consumer/producer aliases lost exact open-tail termination"
)

local mutableErrorAlias = intrinsicLocal("mutable_fail")
local mutableAliasFallback = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({ type = "AstStatLocal", vars = { mutableErrorAlias }, values = { intrinsicGlobal("error") } }),
	intrinsicNode({
		type = "AstStatAssign",
		vars = { intrinsicLocalExpression(mutableErrorAlias) },
		values = { intrinsicGlobal("replacement") },
	}),
	intrinsicNode({
		type = "AstStatExpr",
		expr = intrinsicCall(intrinsicLocalExpression(mutableErrorAlias), { intrinsicString("ordinary"), intrinsicNumber(0) }),
	}),
}), {
	program_id = "frontend-mutable-intrinsic-alias",
	source_name = "frontend-mutable-intrinsic-alias",
	intrinsic_bindings = { errorBinding },
})
assert(mutableAliasFallback.program ~= nil, "mutable intrinsic alias fallback was rejected")
local mutableAliasProgram = mutableAliasFallback.program :: any
local mutableCalls = 0
local mutableThrows = 0
for _, instruction in mutableAliasProgram.instructions do
	mutableCalls += if instruction.operation.call ~= nil then 1 else 0
end
for _, block in mutableAliasProgram.blocks do
	mutableThrows += if block.terminator.throw_error ~= nil then 1 else 0
end
assert(mutableCalls == 1 and mutableThrows == 0, "mutable intrinsic alias retained stale authenticated identity")

local function liftJoinedAlias(name: string, expression: any, bindings: { any }): any
	local aliasLocal = intrinsicLocal(name)
	return AstFrontend.tryLift(intrinsicDocument({
		intrinsicNode({ type = "AstStatLocal", vars = { aliasLocal }, values = { expression } }),
		intrinsicNode({
			type = "AstStatExpr",
			expr = intrinsicCall(intrinsicLocalExpression(aliasLocal), {
				intrinsicGlobal("target"),
				intrinsicGlobal("handler"),
			}),
		}),
	}), {
		program_id = `frontend-{name}`,
		source_name = `frontend-{name}`,
		intrinsic_bindings = bindings,
	})
end

local function joinedAliasKinds(result: any): { [string]: number }
	assert(result.program ~= nil, "joined intrinsic alias was rejected")
	local kinds = { protected_call = 0, call = 0, throw_error = 0 }
	for _, instruction in (result.program :: any).instructions do
		kinds.protected_call += if instruction.operation.protected_call ~= nil then 1 else 0
		kinds.call += if instruction.operation.call ~= nil then 1 else 0
	end
	for _, block in (result.program :: any).blocks do
		kinds.throw_error += if block.terminator.throw_error ~= nil then 1 else 0
	end
	return kinds
end

local matchedIfJoin = joinedAliasKinds(liftJoinedAlias("matched-if-intrinsic-join", intrinsicNode({
	type = "AstExprIfElse",
	condition = intrinsicGlobal("condition"),
	trueExpr = intrinsicGlobal("pcall"),
	falseExpr = intrinsicGlobal("pcall"),
}), { intrinsicBindings[1] }))
assert(matchedIfJoin.protected_call == 1 and matchedIfJoin.call == 0, "matching if-expression identities did not survive their join")

local matchedShortJoin = joinedAliasKinds(liftJoinedAlias("matched-short-intrinsic-join", intrinsicNode({
	type = "AstExprBinary",
	op = "And",
	left = intrinsicGlobal("pcall"),
	right = intrinsicGlobal("pcall"),
}), { intrinsicBindings[1] }))
assert(matchedShortJoin.protected_call == 1 and matchedShortJoin.call == 0, "matching short-circuit identities did not survive their join")

local survivingIfJoin = joinedAliasKinds(liftJoinedAlias("surviving-intrinsic-join", intrinsicNode({
	type = "AstExprIfElse",
	condition = intrinsicGlobal("condition"),
	trueExpr = intrinsicCall(intrinsicGlobal("error"), { intrinsicString("stop"), intrinsicNumber(0) }),
	falseExpr = intrinsicGlobal("pcall"),
}), { intrinsicBindings[1], errorBinding }))
assert(
	survivingIfJoin.protected_call == 1 and survivingIfJoin.call == 0 and survivingIfJoin.throw_error == 1,
	"sole surviving identity did not cross a partially terminating join"
)

local mismatchedIfJoin = joinedAliasKinds(liftJoinedAlias("mismatched-intrinsic-join", intrinsicNode({
	type = "AstExprIfElse",
	condition = intrinsicGlobal("condition"),
	trueExpr = intrinsicGlobal("pcall"),
	falseExpr = intrinsicGlobal("xpcall"),
}), { intrinsicBindings[1], intrinsicBindings[2] }))
assert(mismatchedIfJoin.protected_call == 0 and mismatchedIfJoin.call == 1, "mismatched identities produced a false joined intrinsic")

local function joinedExpressionType(name: string, expression: any, bindings: { any }?): any
	local result = AstFrontend.tryLift(intrinsicDocument({
		intrinsicNode({ type = "AstStatReturn", list = { expression } }),
	}), {
		program_id = `frontend-{name}`,
		source_name = `frontend-{name}`,
		intrinsic_bindings = bindings or {},
	})
	assert(result.program ~= nil, `joined expression {name} was rejected`)
	local program = result.program :: any
	for _, block in program.blocks do
		if (block.name_hint == "if_value_join" or block.name_hint == "logical_join") and #block.parameters == 1 then
			return program.values[block.parameters[1] + 1].type
		end
	end
	error(`joined expression {name} has no result parameter`)
end

local wideIntegerType = joinedExpressionType("matching-wide-integer-join", intrinsicNode({
	type = "AstExprIfElse",
	condition = intrinsicGlobal("condition"),
	trueExpr = intrinsicNode({ type = "AstExprConstantInteger", value = "1" }),
	falseExpr = intrinsicNode({ type = "AstExprConstantInteger", value = "2" }),
}), nil)
assert(
	wideIntegerType.kind == "integer" and wideIntegerType.bit_width == 65535 and wideIntegerType.signed == false,
	"matching exact integer domains collapsed at an if-expression join"
)

local mismatchedIntegerType = joinedExpressionType("mismatched-integer-width-join", intrinsicNode({
	type = "AstExprIfElse",
	condition = intrinsicGlobal("condition"),
	trueExpr = intrinsicNode({ type = "AstExprConstantInteger", value = "1" }),
	falseExpr = intrinsicNumber(2),
}), nil)
assert(mismatchedIntegerType.kind == "dynamic", "same-kind integer width mismatch produced a false joined domain")

local survivingStringType = joinedExpressionType("surviving-string-join", intrinsicNode({
	type = "AstExprIfElse",
	condition = intrinsicGlobal("condition"),
	trueExpr = intrinsicCall(intrinsicGlobal("error"), { intrinsicString("stop"), intrinsicNumber(0) }),
	falseExpr = intrinsicString("survived"),
}), { errorBinding })
assert(survivingStringType.kind == "string", "sole surviving if-expression type was lost")

local matchingAndType = joinedExpressionType("matching-and-type-join", intrinsicNode({
	type = "AstExprBinary",
	op = "And",
	left = intrinsicString("left"),
	right = intrinsicString("right"),
}), nil)
assert(matchingAndType.kind == "string", "matching and-expression types collapsed at their join")

local matchingOrType = joinedExpressionType("matching-or-type-join", intrinsicNode({
	type = "AstExprBinary",
	op = "Or",
	left = intrinsicBool(false),
	right = intrinsicBool(true),
}), nil)
assert(matchingOrType.kind == "boolean", "matching or-expression types collapsed at their join")

local survivingShortType = joinedExpressionType("surviving-short-type-join", intrinsicNode({
	type = "AstExprBinary",
	op = "And",
	left = intrinsicBool(false),
	right = intrinsicCall(intrinsicGlobal("error"), { intrinsicString("stop"), intrinsicNumber(0) }),
}), { errorBinding })
assert(survivingShortType.kind == "boolean", "sole surviving short-circuit type was lost")

local mismatchedShortType = joinedExpressionType("mismatched-short-type-join", intrinsicNode({
	type = "AstExprBinary",
	op = "Or",
	left = intrinsicString("left"),
	right = intrinsicBool(true),
}), nil)
assert(mismatchedShortType.kind == "dynamic", "mismatched short-circuit types produced a false joined domain")

local function returnedOperatorSemantics(name: string, expression: any): (any, any, any)
	local result = AstFrontend.tryLift(intrinsicDocument({
		intrinsicNode({ type = "AstStatReturn", list = { expression } }),
	}), {
		program_id = `frontend-{name}`,
		source_name = `frontend-{name}`,
	})
	assert(result.program ~= nil and #result.diagnostics == 0, `operator expression {name} was rejected`)
	local program = result.program :: any
	local returnedValue
	for _, block in program.blocks do
		if block.terminator.return_values ~= nil then
			assert(#block.terminator.return_values == 1, `operator expression {name} changed result arity`)
			returnedValue = block.terminator.return_values[1]
		end
	end
	assert(returnedValue ~= nil, `operator expression {name} has no scalar return`)
	local value = program.values[returnedValue + 1]
	local origin = value.origin.instruction_result
	assert(origin ~= nil, `operator expression {name} result is not instruction-owned`)
	local instruction = program.instructions[origin.instruction + 1]
	return value.type, instruction.effects, instruction.operation
end

local function hasExactPureEffects(effects: any): boolean
	return effects.precision == "exact"
		and not effects.reads_memory
		and not effects.writes_memory
		and not effects.may_throw
		and not effects.may_yield
		and not effects.invokes_unknown_code
end

local function hasDynamicOperatorEffects(effects: any): boolean
	return effects.precision == "conservative"
		and effects.reads_memory
		and effects.writes_memory
		and effects.may_throw
		and effects.may_yield
		and effects.invokes_unknown_code
end

local primitiveBinaryRows = {
	{ name = "add", source = "Add", lowered = "add", left = intrinsicNumber(0.5), right = intrinsicNumber(2), result = "number" },
	{ name = "subtract", source = "Sub", lowered = "subtract", left = intrinsicNumber(5), right = intrinsicNumber(2), result = "number" },
	{ name = "multiply", source = "Mul", lowered = "multiply", left = intrinsicNumber(3), right = intrinsicNumber(4), result = "number" },
	{ name = "divide", source = "Div", lowered = "divide", left = intrinsicNumber(5), right = intrinsicNumber(2), result = "number" },
	{ name = "floor-divide", source = "FloorDiv", lowered = "floor_divide", left = intrinsicNumber(5), right = intrinsicNumber(2), result = "number" },
	{ name = "modulo", source = "Mod", lowered = "modulo", left = intrinsicNumber(5), right = intrinsicNumber(2), result = "number" },
	{ name = "power", source = "Pow", lowered = "power", left = intrinsicNumber(2), right = intrinsicNumber(3), result = "number" },
	{ name = "concat", source = "Concat", lowered = "concat", left = intrinsicString("value="), right = intrinsicNumber(2), result = "string" },
	{ name = "equal", source = "CompareEq", lowered = "equal", left = intrinsicString("a"), right = intrinsicString("b"), result = "boolean" },
	{ name = "not-equal", source = "CompareNe", lowered = "not_equal", left = intrinsicString("a"), right = intrinsicString("b"), result = "boolean" },
	{ name = "less", source = "CompareLt", lowered = "less", left = intrinsicString("a"), right = intrinsicString("b"), result = "boolean" },
	{ name = "less-equal", source = "CompareLe", lowered = "less_equal", left = intrinsicString("a"), right = intrinsicString("b"), result = "boolean" },
	{ name = "greater", source = "CompareGt", lowered = "greater", left = intrinsicString("a"), right = intrinsicString("b"), result = "boolean" },
	{ name = "greater-equal", source = "CompareGe", lowered = "greater_equal", left = intrinsicString("a"), right = intrinsicString("b"), result = "boolean" },
	{ name = "numeric-less", source = "CompareLt", lowered = "less", left = intrinsicNumber(0.5), right = intrinsicNumber(2), result = "boolean" },
}
for _, row in primitiveBinaryRows do
	local resultType, effects, operation = returnedOperatorSemantics(`primitive-{row.name}`, intrinsicNode({
		type = "AstExprBinary",
		op = row.source,
		left = row.left,
		right = row.right,
	}))
	assert(resultType.kind == row.result, `primitive {row.name} lost its result domain`)
	assert(hasExactPureEffects(effects), `primitive {row.name} retained dynamic effects`)
	assert(operation.binary ~= nil and operation.binary.operator == row.lowered, `primitive {row.name} changed operator mapping`)
end

local primitiveUnaryRows = {
	{ name = "not", source = "Not", lowered = "logical_not", operand = intrinsicGlobal("dynamic_value"), result = "boolean" },
	{ name = "minus", source = "Minus", lowered = "negate", operand = intrinsicNumber(0.5), result = "number" },
	{ name = "length", source = "Len", lowered = "length", operand = intrinsicString("value"), result = "integer" },
}
for _, row in primitiveUnaryRows do
	local resultType, effects, operation = returnedOperatorSemantics(`primitive-{row.name}`, intrinsicNode({
		type = "AstExprUnary",
		op = row.source,
		expr = row.operand,
	}))
	assert(resultType.kind == row.result, `primitive {row.name} lost its result domain`)
	assert(hasExactPureEffects(effects), `primitive {row.name} retained dynamic effects`)
	assert(operation.unary ~= nil and operation.unary.operator == row.lowered, `primitive {row.name} changed operator mapping`)
end

local unresolvedOperatorRows = {
	{
		name = "dynamic-add",
		expression = intrinsicNode({ type = "AstExprBinary", op = "Add", left = intrinsicGlobal("dynamic_left"), right = intrinsicNumber(1) }),
		result = "dynamic",
	},
	{
		name = "table-concat",
		expression = intrinsicNode({ type = "AstExprBinary", op = "Concat", left = intrinsicNode({ type = "AstExprTable", items = {} }), right = intrinsicString("value") }),
		result = "dynamic",
	},
	{
		name = "mixed-less",
		expression = intrinsicNode({ type = "AstExprBinary", op = "CompareLt", left = intrinsicString("value"), right = intrinsicNumber(1) }),
		result = "boolean",
	},
	{
		name = "table-equality",
		expression = intrinsicNode({ type = "AstExprBinary", op = "CompareEq", left = intrinsicNode({ type = "AstExprTable", items = {} }), right = intrinsicNode({ type = "AstExprTable", items = {} }) }),
		result = "boolean",
	},
	{
		name = "string-minus",
		expression = intrinsicNode({ type = "AstExprUnary", op = "Minus", expr = intrinsicString("value") }),
		result = "dynamic",
	},
	{
		name = "table-length",
		expression = intrinsicNode({ type = "AstExprUnary", op = "Len", expr = intrinsicNode({ type = "AstExprTable", items = {} }) }),
		result = "dynamic",
	},
}
for _, row in unresolvedOperatorRows do
	local resultType, effects = returnedOperatorSemantics(`unresolved-{row.name}`, row.expression)
	assert(resultType.kind == row.result, `unresolved {row.name} made a false result claim`)
	assert(hasDynamicOperatorEffects(effects), `unresolved {row.name} understated dynamic dispatch`)
end

local uniformPlaceLocal = intrinsicLocal("uniform_place")
local uniformPlace = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({ type = "AstStatLocal", vars = { uniformPlaceLocal }, values = { intrinsicNumber(1) } }),
	intrinsicNode({
		type = "AstStatAssign",
		vars = { intrinsicLocalExpression(uniformPlaceLocal) },
		values = { intrinsicNumber(2) },
	}),
	intrinsicNode({
		type = "AstStatReturn",
		list = {
			intrinsicNode({
				type = "AstExprBinary",
				op = "Add",
				left = intrinsicLocalExpression(uniformPlaceLocal),
				right = intrinsicNumber(0.5),
			}),
		},
	}),
}), { program_id = "frontend-uniform-place-domain", source_name = "frontend-uniform-place-domain" })
assert(uniformPlace.program ~= nil and #uniformPlace.diagnostics == 0, "uniform local place was rejected")
local uniformPlaceProgram = uniformPlace.program :: any
local uniformRead
local uniformAdd
for _, instruction in uniformPlaceProgram.instructions do
	if instruction.operation.place_read ~= nil then
		uniformRead = instruction
	elseif instruction.operation.binary ~= nil and instruction.operation.binary.operator == "add" then
		uniformAdd = instruction
	end
end
assert(uniformPlaceProgram.places[1].type.kind == "integer", "uniform local place lost its concrete domain")
assert(
	uniformRead ~= nil and uniformPlaceProgram.values[uniformRead.results[1] + 1].type.kind == "integer",
	"uniform local place read lost its concrete domain"
)
assert(
	uniformAdd ~= nil
		and uniformPlaceProgram.values[uniformAdd.results[1] + 1].type.kind == "number"
		and hasExactPureEffects(uniformAdd.effects),
	"refined local place did not update its downstream operator domain"
)

local mixedPlaceLocal = intrinsicLocal("mixed_place")
local mixedPlace = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({ type = "AstStatLocal", vars = { mixedPlaceLocal }, values = { intrinsicNumber(1) } }),
	intrinsicNode({
		type = "AstStatAssign",
		vars = { intrinsicLocalExpression(mixedPlaceLocal) },
		values = { intrinsicString("changed") },
	}),
	intrinsicNode({
		type = "AstStatReturn",
		list = {
			intrinsicNode({
				type = "AstExprBinary",
				op = "Add",
				left = intrinsicLocalExpression(mixedPlaceLocal),
				right = intrinsicNumber(1),
			}),
		},
	}),
}), { program_id = "frontend-mixed-place-domain", source_name = "frontend-mixed-place-domain" })
assert(mixedPlace.program ~= nil and #mixedPlace.diagnostics == 0, "mixed local place was rejected")
local mixedPlaceProgram = mixedPlace.program :: any
local mixedAdd
for _, instruction in mixedPlaceProgram.instructions do
	if instruction.operation.binary ~= nil and instruction.operation.binary.operator == "add" then
		mixedAdd = instruction
	end
end
assert(mixedPlaceProgram.places[1].type.kind == "dynamic", "mixed local place gained a false concrete domain")
assert(
	mixedAdd ~= nil
		and mixedPlaceProgram.values[mixedAdd.results[1] + 1].type.kind == "dynamic"
		and hasDynamicOperatorEffects(mixedAdd.effects),
	"mixed local place understated downstream dynamic dispatch"
)

assert(require("./source_domain_fixed_point_test"), "source domain fixed-point tests failed")

local truthyPlaceLocal = intrinsicLocal("truthy_place")
local truthyPlace = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({ type = "AstStatLocal", vars = { truthyPlaceLocal }, values = { intrinsicNumber(1) } }),
	intrinsicNode({
		type = "AstStatAssign",
		vars = { intrinsicLocalExpression(truthyPlaceLocal) },
		values = { intrinsicNumber(2) },
	}),
	intrinsicNode({
		type = "AstStatIf",
		condition = intrinsicLocalExpression(truthyPlaceLocal),
		thenbody = intrinsicNode({
			type = "AstStatBlock",
			body = { intrinsicNode({ type = "AstStatReturn", list = { intrinsicBool(true) } }) },
		}),
	}),
	intrinsicNode({ type = "AstStatReturn", list = { intrinsicBool(false) } }),
}), { program_id = "frontend-truthy-place-domain", source_name = "frontend-truthy-place-domain" })
assert(truthyPlace.program ~= nil and #truthyPlace.diagnostics == 0, "truthiness-used local place was rejected")
local truthyPlaceProgram = truthyPlace.program :: any
local truthyCondition
for _, block in truthyPlaceProgram.blocks do
	if block.terminator.branch ~= nil then
		truthyCondition = block.terminator.branch.condition
	end
end
assert(
	truthyPlaceProgram.places[1].type.kind == "integer"
		and truthyCondition ~= nil
		and truthyPlaceProgram.values[truthyCondition + 1].type.kind == "integer",
	"closed non-Boolean place did not preserve its branch truthiness domain"
)

local function repeatError(message: string): any
	return intrinsicCall(intrinsicGlobal("error"), { intrinsicString(message), intrinsicNumber(0) })
end

local function countEnvironmentGets(program: any, name: string): number
	local count = 0
	for _, instruction in program.instructions do
		count += if instruction.operation.environment_get ~= nil and instruction.operation.environment_get.name == name then 1 else 0
	end
	return count
end

local function countTerminators(program: any, kind: string): number
	local count = 0
	for _, block in program.blocks do
		count += if block.terminator[kind] ~= nil then 1 else 0
	end
	return count
end

local noBreakRepeat = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatRepeat",
		body = intrinsicNode({ type = "AstStatBlock", body = {} }),
		condition = repeatError("repeat-no-break"),
	}),
	intrinsicNode({ type = "AstStatExpr", expr = intrinsicCall(intrinsicGlobal("after"), {}) }),
}), {
	program_id = "frontend-terminating-repeat-no-break",
	source_name = "frontend-terminating-repeat-no-break",
	intrinsic_bindings = { errorBinding },
})
assert(noBreakRepeat.program ~= nil, "terminating repeat without break was rejected")
local noBreakProgram = noBreakRepeat.program :: any
assert(
	countTerminators(noBreakProgram, "throw_error") == 1
		and countTerminators(noBreakProgram, "unreachable_block") == 1
		and countEnvironmentGets(noBreakProgram, "after") == 0,
	"no-break repeat retained a synthetic continuation"
)

local breakOnlyRepeat = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatRepeat",
		body = intrinsicNode({ type = "AstStatBlock", body = { intrinsicNode({ type = "AstStatBreak" }) } }),
		condition = repeatError("dead-break-latch"),
	}),
	intrinsicNode({ type = "AstStatExpr", expr = intrinsicCall(intrinsicGlobal("after"), {}) }),
}), {
	program_id = "frontend-repeat-break-only",
	source_name = "frontend-repeat-break-only",
	intrinsic_bindings = { errorBinding },
})
assert(breakOnlyRepeat.program ~= nil, "break-only repeat was rejected")
local breakOnlyProgram = breakOnlyRepeat.program :: any
assert(
	countTerminators(breakOnlyProgram, "throw_error") == 0
		and countTerminators(breakOnlyProgram, "unreachable_block") == 1
		and countEnvironmentGets(breakOnlyProgram, "after") == 1,
	"break-only repeat lowered its unreachable latch or lost its exit"
)

local terminatingBodyRepeat = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatRepeat",
		body = intrinsicNode({
			type = "AstStatBlock",
			body = {
				intrinsicNode({ type = "AstStatExpr", expr = repeatError("repeat-body") }),
				intrinsicNode({ type = "AstStatContinue" }),
			},
		}),
		condition = repeatError("dead-body-latch"),
	}),
	intrinsicNode({ type = "AstStatExpr", expr = intrinsicCall(intrinsicGlobal("after"), {}) }),
}), {
	program_id = "frontend-repeat-terminating-body",
	source_name = "frontend-repeat-terminating-body",
	intrinsic_bindings = { errorBinding },
})
assert(terminatingBodyRepeat.program ~= nil, "terminating repeat body was rejected")
local terminatingBodyProgram = terminatingBodyRepeat.program :: any
assert(
	countTerminators(terminatingBodyProgram, "throw_error") == 1
		and countTerminators(terminatingBodyProgram, "unreachable_block") == 2
		and countEnvironmentGets(terminatingBodyProgram, "after") == 0,
	"terminating repeat body retained a dead-tail continue, latch, or continuation"
)

local conditionalContinueRepeat = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatRepeat",
		body = intrinsicNode({
			type = "AstStatBlock",
			body = {
				intrinsicNode({
					type = "AstStatIf",
					condition = intrinsicGlobal("again"),
					thenbody = intrinsicNode({ type = "AstStatBlock", body = { intrinsicNode({ type = "AstStatContinue" }) } }),
				}),
				intrinsicNode({ type = "AstStatExpr", expr = repeatError("repeat-non-continue") }),
			},
		}),
		condition = intrinsicGlobal("done"),
	}),
	intrinsicNode({ type = "AstStatExpr", expr = intrinsicCall(intrinsicGlobal("after"), {}) }),
}), {
	program_id = "frontend-repeat-conditional-continue",
	source_name = "frontend-repeat-conditional-continue",
	intrinsic_bindings = { errorBinding },
})
assert(conditionalContinueRepeat.program ~= nil, "conditional repeat continue was rejected")
local conditionalContinueProgram = conditionalContinueRepeat.program :: any
assert(
	countTerminators(conditionalContinueProgram, "throw_error") == 1
		and countEnvironmentGets(conditionalContinueProgram, "done") == 1
		and countEnvironmentGets(conditionalContinueProgram, "after") == 1,
	"actual continue edge did not preserve the repeat latch and exit"
)

local nestedContinueRepeat = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatRepeat",
		body = intrinsicNode({
			type = "AstStatBlock",
			body = {
				intrinsicNode({
					type = "AstStatRepeat",
					body = intrinsicNode({ type = "AstStatBlock", body = { intrinsicNode({ type = "AstStatContinue" }) } }),
					condition = intrinsicBool(true),
				}),
				intrinsicNode({ type = "AstStatExpr", expr = repeatError("nested-continue-body") }),
			},
		}),
		condition = repeatError("dead-outer-latch"),
	}),
	intrinsicNode({ type = "AstStatExpr", expr = intrinsicCall(intrinsicGlobal("after"), {}) }),
}), {
	program_id = "frontend-repeat-nested-continue",
	source_name = "frontend-repeat-nested-continue",
	intrinsic_bindings = { errorBinding },
})
assert(nestedContinueRepeat.program ~= nil, "nested repeat continue was rejected")
local nestedContinueProgram = nestedContinueRepeat.program :: any
assert(
	countTerminators(nestedContinueProgram, "throw_error") == 1
		and countTerminators(nestedContinueProgram, "unreachable_block") == 2
		and countEnvironmentGets(nestedContinueProgram, "after") == 0,
	"nested-loop continue incorrectly preserved the outer repeat latch or exit"
)

local conditionalBreakRepeat = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatRepeat",
		body = intrinsicNode({
			type = "AstStatBlock",
			body = {
				intrinsicNode({
					type = "AstStatIf",
					condition = intrinsicGlobal("leave"),
					thenbody = intrinsicNode({ type = "AstStatBlock", body = { intrinsicNode({ type = "AstStatBreak" }) } }),
				}),
			},
		}),
		condition = repeatError("repeat-with-break"),
	}),
	intrinsicNode({ type = "AstStatExpr", expr = intrinsicCall(intrinsicGlobal("after"), {}) }),
}), {
	program_id = "frontend-terminating-repeat-with-break",
	source_name = "frontend-terminating-repeat-with-break",
	intrinsic_bindings = { errorBinding },
})
assert(conditionalBreakRepeat.program ~= nil, "terminating repeat with break was rejected")
local conditionalBreakProgram = conditionalBreakRepeat.program :: any
assert(countEnvironmentGets(conditionalBreakProgram, "after") == 1, "actual break edge did not preserve the repeat exit")

local nestedBreakRepeat = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatRepeat",
		body = intrinsicNode({
			type = "AstStatBlock",
			body = {
				intrinsicNode({
					type = "AstStatRepeat",
					body = intrinsicNode({ type = "AstStatBlock", body = { intrinsicNode({ type = "AstStatBreak" }) } }),
					condition = intrinsicBool(true),
				}),
			},
		}),
		condition = repeatError("outer-repeat"),
	}),
	intrinsicNode({ type = "AstStatExpr", expr = intrinsicCall(intrinsicGlobal("after"), {}) }),
}), {
	program_id = "frontend-nested-break-repeat",
	source_name = "frontend-nested-break-repeat",
	intrinsic_bindings = { errorBinding },
})
assert(nestedBreakRepeat.program ~= nil, "nested repeat break case was rejected")
local nestedBreakProgram = nestedBreakRepeat.program :: any
assert(countEnvironmentGets(nestedBreakProgram, "after") == 0, "nested-loop break incorrectly preserved the outer repeat exit")

local nestedArgumentError = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatReturn",
		list = {
			intrinsicCall(intrinsicGlobal("sink"), {
				intrinsicCall(intrinsicGlobal("before"), {}),
				intrinsicCall(intrinsicGlobal("error"), { intrinsicString("argument"), intrinsicNumber(0) }),
				intrinsicCall(intrinsicGlobal("after"), {}),
			}),
		},
	}),
}), {
	program_id = "frontend-nested-argument-error",
	source_name = "frontend-nested-argument-error",
	intrinsic_bindings = { errorBinding },
})
assert(nestedArgumentError.program ~= nil, "nested argument error was rejected")
local nestedArgumentProgram = nestedArgumentError.program :: any
local nestedLookups = {}
local nestedCalls = 0
for _, instruction in nestedArgumentProgram.instructions do
	local lookup = instruction.operation.environment_get
	if lookup ~= nil then
		nestedLookups[lookup.name] = (nestedLookups[lookup.name] or 0) + 1
	elseif instruction.operation.call ~= nil then
		nestedCalls += 1
	end
end
assert(nestedArgumentProgram.blocks[1].terminator.throw_error ~= nil, "nested argument error did not terminate its owner")
assert(nestedLookups.sink == 1 and nestedLookups.before == 1, "call callee or earlier argument was not evaluated")
assert(nestedLookups.after == nil and nestedLookups.error == nil, "nested argument error evaluated a later argument or mutable builtin")
assert(nestedCalls == 1, "nested argument error emitted the unreachable outer call")

local nestedTerminator = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatReturn",
		list = {
			intrinsicCall(intrinsicGlobal("error"), {
				intrinsicCall(intrinsicGlobal("error"), { intrinsicString("inner"), intrinsicNumber(0) }),
				intrinsicNumber(0),
			}),
		},
	}),
}), {
	program_id = "frontend-nested-terminator",
	source_name = "frontend-nested-terminator",
	intrinsic_bindings = { errorBinding },
})
assert(nestedTerminator.program ~= nil, "nested terminating error was rejected")
local nestedTerminatorProgram = nestedTerminator.program :: any
assert(#nestedTerminatorProgram.instructions == 2, "outer error evaluated after its message terminated")
assert(nestedTerminatorProgram.blocks[1].terminator.throw_error ~= nil, "nested error did not finalize exactly one throw")

local shortCircuitError = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatReturn",
		list = {
			intrinsicNode({
				type = "AstExprBinary",
				op = "And",
				left = intrinsicGlobal("condition"),
				right = intrinsicCall(intrinsicGlobal("error"), { intrinsicString("right"), intrinsicNumber(0) }),
			}),
		},
	}),
}), {
	program_id = "frontend-short-circuit-error",
	source_name = "frontend-short-circuit-error",
	intrinsic_bindings = { errorBinding },
})
assert(shortCircuitError.program ~= nil, "short-circuit error branch was rejected")
local shortCircuitProgram = shortCircuitError.program :: any
local shortThrows = 0
local shortReturns = 0
for _, block in shortCircuitProgram.blocks do
	shortThrows += if block.terminator.throw_error ~= nil then 1 else 0
	shortReturns += if block.terminator.return_values ~= nil then 1 else 0
end
assert(#shortCircuitProgram.blocks == 4 and shortThrows == 1 and shortReturns == 1, "short-circuit termination lost its surviving join")

local bothBranchError = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatReturn",
		list = {
			intrinsicNode({
				type = "AstExprIfElse",
				condition = intrinsicGlobal("condition"),
				trueExpr = intrinsicCall(intrinsicGlobal("error"), { intrinsicString("true"), intrinsicNumber(0) }),
				falseExpr = intrinsicCall(intrinsicGlobal("error"), { intrinsicString("false"), intrinsicNumber(0) }),
			}),
		},
	}),
}), {
	program_id = "frontend-both-branch-error",
	source_name = "frontend-both-branch-error",
	intrinsic_bindings = { errorBinding },
})
assert(bothBranchError.program ~= nil, "fully terminating if expression was rejected")
local bothBranchProgram = bothBranchError.program :: any
local branchThrows = 0
local deadJoins = 0
for _, block in bothBranchProgram.blocks do
	branchThrows += if block.terminator.throw_error ~= nil then 1 else 0
	deadJoins += if block.terminator.unreachable_block ~= nil then 1 else 0
	assert(block.terminator.return_values == nil, "fully terminating if expression retained an unreachable return")
end
assert(#bothBranchProgram.blocks == 4 and branchThrows == 2 and deadJoins == 1, "fully terminating if expression did not seal its reserved join")

local openCreate = AstFrontend.tryLift(intrinsicDocument({
	intrinsicNode({
		type = "AstStatReturn",
		list = {
			intrinsicCall(intrinsicMember("coroutine", "create"), { intrinsicGlobal("target") }),
		},
	}),
}), {
	program_id = "frontend-open-create",
	source_name = "frontend-open-create",
	intrinsic_bindings = { intrinsicBindings[3] },
})
assert(openCreate.program ~= nil, "open-result coroutine.create was rejected")
local openCreateKinds = { call = 0, coroutine_create = 0, pack_values = 0, coroutine_lookup = 0 }
local openCreatePack
for _, instruction in (openCreate.program :: any).instructions do
	if instruction.operation.call ~= nil then
		openCreateKinds.call += 1
	elseif instruction.operation.coroutine_create ~= nil then
		openCreateKinds.coroutine_create += 1
	elseif instruction.operation.pack_values ~= nil then
		openCreateKinds.pack_values += 1
		openCreatePack = instruction.pack_result
	elseif instruction.operation.environment_get ~= nil and instruction.operation.environment_get.name == "coroutine" then
		openCreateKinds.coroutine_lookup += 1
	end
end
assert(
	openCreateKinds.call == 0
		and openCreateKinds.coroutine_create == 1
		and openCreateKinds.pack_values == 1
		and openCreateKinds.coroutine_lookup == 0,
	"open coroutine.create did not use native creation and closed pack construction"
)
assert(openCreatePack ~= nil, "open coroutine.create did not produce a pack")
local openPack = (openCreate.program :: any).value_packs[openCreatePack + 1]
assert(openPack.shape.tail == "closed" and #openPack.shape.prefix == 1, "open coroutine.create pack did not stay one fixed result")
assert(openPack.shape.prefix[1].kind == "thread", "open coroutine.create pack lost its thread domain")

local duplicateIntrinsicOptions = AstFrontend.tryLift(intrinsicDocument({}), {
	program_id = "frontend-duplicate-intrinsic-options",
	source_name = "frontend-duplicate-intrinsic-options",
	intrinsic_bindings = { intrinsicBindings[1], intrinsicBindings[1] },
})
assert(
	duplicateIntrinsicOptions.program == nil and duplicateIntrinsicOptions.diagnostics[1].code == "invalid_options",
	"direct frontend options accepted duplicate intrinsic authority"
)

local malformedIntrinsicOptions = AstFrontend.tryLift(intrinsicDocument({}), {
	program_id = "frontend-malformed-intrinsic-options",
	source_name = "frontend-malformed-intrinsic-options",
	intrinsic_bindings = {
		{
			path = "pcall",
			evidence = { kind = "frontend_proof", locator = "" },
		},
	},
})
assert(
	malformedIntrinsicOptions.program == nil and malformedIntrinsicOptions.diagnostics[1].code == "invalid_options",
	"direct frontend options accepted malformed intrinsic evidence"
)
