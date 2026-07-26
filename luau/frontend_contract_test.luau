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
