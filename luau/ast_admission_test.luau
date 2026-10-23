--!strict

local AstAdmission = require("./ast_admission")
local AstFrontend = require("./ast_frontend")

local function limits(tables: number, entries: number, depth: number): AstAdmission.Limits
	return {
		max_tables = tables,
		max_entries = entries,
		max_depth = depth,
	}
end

local function chain(length: number): any
	local root: any = {}
	local current: any = root
	for _ = 2, length do
		local child = {}
		current.child = child
		current = child
	end
	return root
end

local function inspectOk(value: any, requestedLimits: AstAdmission.Limits): AstAdmission.Inspection
	local inspection, problem = AstAdmission.inspect(value, requestedLimits)
	assert(problem == nil, if problem == nil then "unexpected AST admission failure" else problem.detail)
	return inspection :: AstAdmission.Inspection
end

local function inspectProblem(value: any, requestedLimits: AstAdmission.Limits, detail: string): AstAdmission.Problem
	local inspection, problem = AstAdmission.inspect(value, requestedLimits)
	assert(inspection == nil and problem ~= nil, `expected AST admission failure containing {detail}`)
	assert(string.find((problem :: AstAdmission.Problem).detail, detail, 1, true) ~= nil, (problem :: AstAdmission.Problem).detail)
	return problem :: AstAdmission.Problem
end

assert(AstAdmission.expectBytes("abcd", "fixture bytes", 4) == "abcd", "exact byte limit was rejected")
local oversizedBytesAccepted = pcall(AstAdmission.expectBytes, "abcde", "fixture bytes", 4)
assert(not oversizedBytesAccepted, "oversized byte input was accepted")
local decodeCount = 0
local decoded = AstAdmission.decodeBytes("abcd", "fixture decoder bytes", 4, function(bytes: string): any
	decodeCount += 1
	return { length = #bytes }
end)
assert(decoded.length == 4 and decodeCount == 1, "exact-limit parser bytes did not reach the decoder once")
local oversizedDecodeAccepted = pcall(AstAdmission.decodeBytes, "abcde", "fixture decoder bytes", 4, function(_bytes: string): any
	decodeCount += 1
	return {}
end)
assert(not oversizedDecodeAccepted and decodeCount == 1, "oversized parser bytes reached the decoder")

local signedBytePrefix = string.char(0xef, 0xbf, 0xbf) .. "ff"
local parserDecoded = AstAdmission.decodeParserBytes("parser-json", "parser byte recovery", function(_bytes: string): any
	return {
		literal = signedBytePrefix .. "ff",
		segments = { signedBytePrefix .. "fe" .. "prefix", signedBytePrefix .. "7f" },
		multibyte = signedBytePrefix .. "c3" .. signedBytePrefix .. "a9",
		literalPrefix = signedBytePrefix .. "ef" .. signedBytePrefix .. "bf" .. signedBytePrefix .. "bf" .. "ffff",
	}
end)
assert(
	parserDecoded.literal == string.char(0xff),
	`signed parser byte was not recovered (length {#parserDecoded.literal}, first byte {string.byte(parserDecoded.literal, 1)})`
)
assert(parserDecoded.segments[1] == string.char(0xfe) .. "prefix", "nested signed parser byte was not recovered")
assert(parserDecoded.segments[2] == signedBytePrefix .. "7f", "nonnegative parser artifact was rewritten")
assert(parserDecoded.multibyte == utf8.char(0xe9), "valid multibyte parser string was not recovered")
assert(parserDecoded.literalPrefix == signedBytePrefix .. "ff", "parser repair rescanned reconstructed bytes")

local exactTables = inspectOk(chain(4), limits(4, 8, 8))
assert(exactTables.table_count == 4, "exact AST table limit changed")
inspectProblem(chain(5), limits(4, 8, 8), "table limit")

local exactDepth = inspectOk(chain(4), limits(8, 8, 4))
assert(exactDepth.max_depth == 4, "exact AST depth limit changed")
inspectProblem(chain(5), limits(8, 8, 4), "depth limit")

local exactEntries = inspectOk({ a = 1, b = 2, c = 3, d = 4 }, limits(8, 4, 8))
assert(exactEntries.entry_count == 4, "exact AST entry limit changed")
inspectProblem({ a = 1, b = 2, c = 3, d = 4, e = 5 }, limits(8, 4, 8), "entry limit")

local cyclic = {}
cyclic.self = cyclic
local cycleProblem = inspectProblem(cyclic, limits(8, 8, 8), "contains a cycle")
assert(cycleProblem.code == "malformed_ast_graph", "AST cycle diagnostic changed code")

local malformedKey = {}
malformedKey[false] = "value"
local keyProblem = inspectProblem(malformedKey, limits(8, 8, 8), "positive integer indexes")
assert(keyProblem.code == "malformed_ast_graph", "AST key diagnostic changed code")

local sparseProblem = inspectProblem({ [1] = {}, [3] = {} }, limits(8, 8, 8), "arrays must be dense")
assert(sparseProblem.code == "malformed_ast_graph", "sparse AST array diagnostic changed code")
local nullableTypeArgumentNames = {
	type = "AstStatBlock",
	body = {
		{
			type = "AstStatTypeAlias",
			value = {
				type = "AstTypeFunction",
				argTypes = {
					type = "AstTypeList",
					types = {
						{ type = "AstTypeReference", name = "Cursor" },
						{ type = "AstTypeReference", name = "string" },
						{ type = "AstTypeReference", name = "string" },
					},
				},
				argNames = {
					[2] = { type = "AstArgumentName", name = "typ" },
					[3] = { type = "AstArgumentName", name = "value" },
				},
			},
		},
	},
}
inspectOk(nullableTypeArgumentNames, limits(32, 64, 16))

local outOfRangeTypeArgumentName = nullableTypeArgumentNames.body[1].value.argNames[3]
nullableTypeArgumentNames.body[1].value.argNames[4] = outOfRangeTypeArgumentName
nullableTypeArgumentNames.body[1].value.argNames[3] = nil
local nullableRangeProblem = inspectProblem(nullableTypeArgumentNames, limits(32, 64, 16), "arrays must be dense")
assert(nullableRangeProblem.code == "malformed_ast_graph", "nullable AST array range diagnostic changed code")
local mixedProblem = inspectProblem({ type = "AstStatBlock", [1] = {} }, limits(8, 8, 8), "must not mix")
assert(mixedProblem.code == "malformed_ast_graph", "mixed AST table diagnostic changed code")
local metatableProblem = inspectProblem(setmetatable({}, {}), limits(8, 8, 8), "must not have metatables")
assert(metatableProblem.code == "malformed_ast_graph", "AST metatable diagnostic changed code")

local parserError = {
	type = "AstStatBlock",
	body = {
		{ type = "AstExprError", location = "1,0 - 1,1" },
	},
}
local _, parserProblem = AstAdmission.inspect(parserError, limits(8, 16, 8))
assert(parserProblem ~= nil and parserProblem.code == "malformed_source_expression", "parser recovery diagnostic changed")
assert((parserProblem :: AstAdmission.Problem).node == parserError.body[1], "parser recovery diagnostic lost its AST node")

local function functionWithBody(isVariadic: boolean, body: { any }): any
	return {
		type = "AstExprFunction",
		args = {},
		vararg = isVariadic,
		body = { type = "AstStatBlock", body = body },
	}
end

local declaration: any = { type = "AstLocal", name = "target", location = "2,0 - 2,6" }
local localTarget: any = { type = "AstExprLocal", ["local"] = declaration }
local mutationAst = {
	type = "AstStatBlock",
	body = ({
		{ type = "AstStatLocalFunction", name = declaration, func = functionWithBody(false, {}) },
		{ type = "AstStatAssign", vars = { localTarget }, values = { { type = "AstExprConstantNil" } } },
		{ type = "AstStatCompoundAssign", op = "Add", var = localTarget, value = { type = "AstExprConstantNil" } },
		{ type = "AstStatFunction", name = localTarget, func = functionWithBody(false, {}) },
	} :: { any }),
}
local mutationInspection = inspectOk(mutationAst, limits(64, 128, 16))
assert(#mutationInspection.mutable_local_nodes == 4, "mutable-local preflight lost a mutation form")
for _, node in mutationInspection.mutable_local_nodes do
	assert(node == declaration, "mutable-local preflight changed declaration identity")
end
assert(#mutationInspection.reassigned_local_nodes == 3, "reassignment preflight conflated recursive initialization with a source write")
for _, node in mutationInspection.reassigned_local_nodes do
	assert(node == declaration, "reassignment preflight changed declaration identity")
end

local function mutationDocument(prefix: string, typeOnly: boolean): any
	local target = { type = "AstLocal", name = "target", location = prefix .. "-target" }
	local function targetExpression(): any
		return { type = "AstExprLocal", ["local"] = target }
	end
	local assignment = {
		type = "AstStatAssign",
		location = prefix .. "-assignment",
		vars = { targetExpression() },
		values = { { type = "AstExprGlobal", global = "warn" } },
	}
	local middle: any = if typeOnly
		then {
			type = "AstStatTypeAlias",
			location = prefix .. "-type-alias",
			value = {
				type = "AstTypeTypeof",
				expr = functionWithBody(false, { assignment }),
			},
		}
		else assignment
	return { root = {
		type = "AstStatBlock",
		body = ({
			{
				type = "AstStatLocal",
				location = prefix .. "-declaration",
				vars = { target },
				values = { { type = "AstExprGlobal", global = "print" } },
			},
			middle,
			{ type = "AstStatReturn", list = { targetExpression() } },
		} :: { any }),
	} }
end

local typeOnlyMutation = mutationDocument("type-only-mutation", true)
local typeOnlyInspection = inspectOk(typeOnlyMutation, limits(64, 128, 20))
assert(#typeOnlyInspection.mutable_local_nodes == 0, "type-only assignment created a runtime mutable local")
assert(#typeOnlyInspection.reassigned_local_nodes == 0, "type-only assignment created a runtime reassignment")
local typeOnlyResult = AstFrontend.tryLift(typeOnlyMutation, {
	program_id = "type-only-mutation",
	source_name = "type-only-mutation",
})
assert(typeOnlyResult.program ~= nil and #typeOnlyResult.diagnostics == 0, "type-only mutation fixture did not lift")
assert(#(typeOnlyResult.program :: any).places == 0, "type-only assignment created a runtime place")

local runtimeMutation = mutationDocument("runtime-mutation", false)
local runtimeResult = AstFrontend.tryLift(runtimeMutation, {
	program_id = "runtime-mutation",
	source_name = "runtime-mutation",
})
assert(runtimeResult.program ~= nil and #runtimeResult.diagnostics == 0, "runtime mutation fixture did not lift")
assert(#(runtimeResult.program :: any).places == 1, "runtime assignment lost its place identity")

assert(require("./ast_local_identity_test") == true, "runtime-local identity suite failed")
assert(require("./ast_expression_scalar_test") == true, "expression scalar admission suite failed")

local function expectFrontendProblem(document: any, code: string, label: string)
	local result = AstFrontend.tryLift(document, { program_id = label, source_name = label })
	assert(result.program == nil and #result.diagnostics == 1, `{label} did not reject at the frontend boundary`)
	assert(result.diagnostics[1].code == code, `{label} changed frontend diagnostic code`)
end

local function deadTransfer(transferType: string): any
	return {
		root = {
			type = "AstStatBlock",
			body = ({
				{ type = "AstStatReturn", list = {} },
				{ type = transferType },
			} :: { any }),
		},
	}
end

local deadBreak = deadTransfer("AstStatBreak")
local deadBreakProblem = inspectProblem(deadBreak, limits(16, 32, 12), "break has no enclosing loop")
assert(deadBreakProblem.code == "break_outside_loop", "dead break changed admission diagnostic code")
expectFrontendProblem(deadBreak, "break_outside_loop", "dead-break-context-admission")

local deadContinue = deadTransfer("AstStatContinue")
local deadContinueProblem = inspectProblem(deadContinue, limits(16, 32, 12), "continue has no enclosing loop")
assert(deadContinueProblem.code == "continue_outside_loop", "dead continue changed admission diagnostic code")
expectFrontendProblem(deadContinue, "continue_outside_loop", "dead-continue-context-admission")

local deadVarargs: any = {
	root = {
		type = "AstStatBlock",
		body = { {
			type = "AstStatReturn",
			list = { {
				type = "AstExprFunction",
				args = {},
				vararg = false,
				body = {
					type = "AstStatBlock",
					body = {
						{ type = "AstStatReturn", list = {} },
						{ type = "AstStatReturn", list = { { type = "AstExprVarargs" } } },
					},
				},
			} },
		} },
	},
}
local deadVarargProblem = inspectProblem(deadVarargs, limits(32, 64, 20), "varargs have no owning function pack")
assert(deadVarargProblem.code == "varargs_outside_variadic_function", "dead varargs changed admission diagnostic code")
expectFrontendProblem(deadVarargs, "varargs_outside_variadic_function", "dead-varargs-context-admission")

inspectOk({
	root = {
		type = "AstStatBlock",
		body = { { type = "AstStatReturn", list = { { type = "AstExprVarargs" } } } },
	},
}, limits(16, 32, 12))
inspectOk({
	root = {
		type = "AstStatBlock",
		body = { { type = "AstStatReturn", list = { functionWithBody(true, {
			{ type = "AstStatReturn", list = { { type = "AstExprVarargs" } } },
		}) } } },
	},
}, limits(24, 48, 16))

for _, loopType in { "AstStatWhile", "AstStatRepeat", "AstStatFor", "AstStatForIn" } do
	local loop: any = {
		type = loopType,
		body = {
			type = "AstStatBlock",
			body = { { type = "AstStatBreak" }, { type = "AstStatContinue" } },
		},
	}
	if loopType == "AstStatWhile" or loopType == "AstStatRepeat" then
		loop.condition = { type = "AstExprConstantBool", value = true }
	elseif loopType == "AstStatFor" then
		loop.var = { type = "AstLocal", name = "item", location = "runtime-context-numeric-item" }
		loop.from = { type = "AstExprConstantNumber", value = 1 }
		loop.to = { type = "AstExprConstantNumber", value = 2 }
	else
		loop.vars = { { type = "AstLocal", name = "item", location = "runtime-context-generic-item" } }
		loop.values = { { type = "AstExprConstantNil" } }
	end
	inspectOk({
		root = {
			type = "AstStatBlock",
			body = { loop },
		},
	}, limits(24, 48, 16))
end

local nestedBreak = {
	root = {
		type = "AstStatBlock",
		body = { {
			type = "AstStatWhile",
			condition = { type = "AstExprConstantBool", value = true },
			body = {
				type = "AstStatBlock",
				body = { { type = "AstStatReturn", list = { functionWithBody(false, {
					{ type = "AstStatReturn", list = {} },
					{ type = "AstStatBreak" },
				}) } } },
			},
		} },
	},
}
local nestedBreakProblem = inspectProblem(nestedBreak, limits(32, 64, 20), "break has no enclosing loop")
assert(nestedBreakProblem.code == "break_outside_loop", "nested function inherited an outer loop")

local nestedVarargs = {
	root = {
		type = "AstStatBlock",
		body = { { type = "AstStatReturn", list = { functionWithBody(true, {
			{ type = "AstStatReturn", list = { functionWithBody(false, {
				{ type = "AstStatReturn", list = {} },
				{ type = "AstStatReturn", list = { { type = "AstExprVarargs" } } },
			}) } },
		}) } } },
	},
}
local nestedVarargProblem = inspectProblem(nestedVarargs, limits(40, 80, 24), "varargs have no owning function pack")
assert(nestedVarargProblem.code == "varargs_outside_variadic_function", "nested function captured an outer vararg pack")

local function deadMember(member: any): any
	return {
		root = {
			type = "AstStatBlock",
			body = ({ { type = "AstStatReturn", list = {} }, member } :: { any }),
		},
	}
end

local scalarMember = deadMember("not-a-statement")
local scalarMemberProblem = inspectProblem(scalarMember, limits(16, 32, 12), "block member is not an AST node")
assert(scalarMemberProblem.code == "malformed_statement", "scalar block member changed admission diagnostic code")
expectFrontendProblem(scalarMember, "malformed_statement", "dead-scalar-statement-admission")

local untaggedMember = deadMember({ location = "dead-untagged-statement" })
local untaggedMemberProblem = inspectProblem(untaggedMember, limits(16, 32, 12), "AST node is missing its type tag")
assert(untaggedMemberProblem.code == "malformed_ast", "untagged block member changed admission diagnostic code")
expectFrontendProblem(untaggedMember, "malformed_ast", "dead-untagged-statement-admission")

local unsupportedMember = deadMember({ type = "AstStatUnsupported", location = "dead-unsupported-statement" })
local unsupportedMemberProblem = inspectProblem(unsupportedMember, limits(16, 32, 12), "is not supported")
assert(unsupportedMemberProblem.code == "unsupported_statement", "unsupported block member changed admission diagnostic code")
expectFrontendProblem(unsupportedMember, "unsupported_statement", "dead-unsupported-statement-admission")

local deadTypeStatement = deadMember({ type = "AstStatTypeAlias", location = "dead-type-statement" })
inspectOk(deadTypeStatement, limits(16, 32, 12))
local deadTypeResult = AstFrontend.tryLift(deadTypeStatement, {
	program_id = "dead-type-statement-admission",
	source_name = "dead-type-statement-admission",
})
assert(deadTypeResult.program ~= nil and #deadTypeResult.diagnostics == 0, "valid dead type statement was rejected")

local function deadReturnMember(member: any): any
	return deadMember({ type = "AstStatReturn", list = ({ member } :: { any }) })
end

local scalarReturnMember = deadReturnMember("not-an-expression")
expectFrontendProblem(scalarReturnMember, "malformed_return", "dead-scalar-return-expression-admission")

local missingReturnList = deadMember({ type = "AstStatReturn" })
expectFrontendProblem(missingReturnList, "malformed_ast", "dead-missing-return-list-admission")

local untaggedReturnMember = deadReturnMember({ location = "dead-untagged-return-expression" })
expectFrontendProblem(untaggedReturnMember, "malformed_ast", "dead-untagged-return-expression-admission")

local unsupportedReturnMember = deadReturnMember({
	type = "AstExprUnsupported",
	location = "dead-unsupported-return-expression",
})
expectFrontendProblem(unsupportedReturnMember, "unsupported_expression", "dead-unsupported-return-expression-admission")

local nestedUnsupportedReturnMember = deadReturnMember({
	type = "AstExprGroup",
	expr = { type = "AstExprUnsupported", location = "dead-nested-unsupported-expression" },
})
expectFrontendProblem(nestedUnsupportedReturnMember, "unsupported_expression", "dead-nested-expression-admission")

local missingGroupExpression = deadReturnMember({ type = "AstExprGroup" })
expectFrontendProblem(missingGroupExpression, "malformed_group", "dead-missing-group-expression-admission")

local unsupportedTableItem = deadReturnMember({
	type = "AstExprTable",
	items = { { type = "AstExprTableItem", kind = "unsupported", value = { type = "AstExprConstantNil" } } },
})
expectFrontendProblem(unsupportedTableItem, "unsupported_table_item_kind", "dead-table-item-kind-admission")

local scalarTableItem = deadReturnMember({ type = "AstExprTable", items = { "not-a-table-item" } })
expectFrontendProblem(scalarTableItem, "malformed_table_item", "dead-scalar-table-item-admission")

local missingTableItemValue = deadReturnMember({
	type = "AstExprTable",
	items = { { type = "AstExprTableItem", kind = "list" } },
})
expectFrontendProblem(missingTableItemValue, "malformed_table_item", "dead-missing-table-item-value-admission")

local orderedTableTailPack = {
	root = {
		type = "AstStatBlock",
		body = { {
			type = "AstStatReturn",
			list = { {
				type = "AstExprTable",
				location = "ordered-table-tail-pack",
				items = ({
					{
						type = "AstExprTableItem",
						kind = "general",
						key = { type = "AstExprGlobal", global = "dynamic_key" },
						value = { type = "AstExprConstantNumber", value = 1 },
					},
					{
						type = "AstExprTableItem",
						kind = "list",
						value = {
							type = "AstExprCall",
							func = { type = "AstExprGlobal", global = "produce" },
							args = {},
						},
					},
				} :: { any }),
			} },
		} },
	},
}
local orderedTableTailResult = AstFrontend.tryLift(orderedTableTailPack, {
	program_id = "ordered-table-tail-pack",
	source_name = "ordered-table-tail-pack",
})
assert(orderedTableTailResult.program ~= nil and #orderedTableTailResult.diagnostics == 0, "ordered table tail pack was rejected")
local orderedTablePackWrites = 0
for _, instruction in (orderedTableTailResult.program :: any).instructions do
	if instruction.operation.table_set_pack ~= nil then
		orderedTablePackWrites += 1
		assert(instruction.operation.table_set_pack.first_index == 1, "ordered table tail pack changed its first list index")
	end
end
assert(orderedTablePackWrites == 1, "ordered table tail pack did not lower exactly one pack write")

local deadNonCallStatement = deadMember({
	type = "AstStatExpr",
	expr = { type = "AstExprConstantNil", location = "dead-non-call-statement-expression" },
})
expectFrontendProblem(deadNonCallStatement, "unsupported_expression_statement", "dead-non-call-statement-admission")

local deadInvalidAssignmentTarget = deadMember({
	type = "AstStatAssign",
	vars = { { type = "AstExprConstantNil", location = "dead-invalid-assignment-target" } },
	values = { { type = "AstExprConstantNil" } },
})
expectFrontendProblem(deadInvalidAssignmentTarget, "unsupported_assignment_target", "dead-assignment-target-admission")

local deadMissingWhileBody = deadMember({
	type = "AstStatWhile",
	condition = { type = "AstExprConstantBool", value = true },
})
expectFrontendProblem(deadMissingWhileBody, "malformed_while", "dead-missing-while-body-admission")

local deadMissingFunctionBody = deadReturnMember({ type = "AstExprFunction", args = {}, vararg = false })
expectFrontendProblem(deadMissingFunctionBody, "malformed_function", "dead-missing-function-body-admission")

local deadMissingBlockBody = deadMember({ type = "AstStatBlock" })
expectFrontendProblem(deadMissingBlockBody, "malformed_ast", "dead-missing-block-body-admission")

local deadUnsupportedElse = deadMember({
	type = "AstStatIf",
	condition = { type = "AstExprConstantBool", value = true },
	thenbody = { type = "AstStatBlock", body = {} },
	elsebody = { type = "AstStatReturn", list = {} },
})
expectFrontendProblem(deadUnsupportedElse, "unsupported_else_body", "dead-unsupported-else-admission")

local deadTypeAssertion = deadReturnMember({
	type = "AstExprTypeAssertion",
	expr = { type = "AstExprConstantNil" },
	annotation = { kind = "type-metadata", payload = { kind = "nested-type-metadata" } },
})
inspectOk(deadTypeAssertion, limits(32, 64, 16))
local deadTypeAssertionResult = AstFrontend.tryLift(deadTypeAssertion, {
	program_id = "dead-expression-type-metadata-admission",
	source_name = "dead-expression-type-metadata-admission",
})
assert(
	deadTypeAssertionResult.program ~= nil and #deadTypeAssertionResult.diagnostics == 0,
	"expression admission classified type metadata as runtime syntax"
)

local optionalChildCases: { {
	label: string,
	code: string,
	detail: string,
	statement: any,
} } = {
	{
		label = "numeric-for-step",
		code = "malformed_numeric_for",
		detail = "numeric for step is not an AST expression",
		statement = {
			type = "AstStatFor",
			location = "numeric-for-step-owner",
			var = { type = "AstLocal", name = "index", location = "numeric-for-step-local" },
			from = { type = "AstExprConstantNumber", value = 1 },
			to = { type = "AstExprConstantNumber", value = 2 },
			step = "not-an-expression",
			body = { type = "AstStatBlock", body = {} },
		},
	},
	{
		label = "if-else-body",
		code = "malformed_ast",
		detail = "else body is missing its type tag",
		statement = {
			type = "AstStatIf",
			location = "if-else-body-owner",
			condition = { type = "AstExprConstantBool", value = true },
			thenbody = { type = "AstStatBlock", body = {} },
			elsebody = false,
		},
	},
}
local optionalChildFailures = {}
for _, case in optionalChildCases do
	for _, mode in { "reachable", "dead" } do
		local caseDocument = if mode == "dead" then deadMember(case.statement) else { root = {
			type = "AstStatBlock",
			body = { case.statement },
		} }
		local label = `{mode}-{case.label}-presence-admission`
		local result = AstFrontend.tryLift(caseDocument, { program_id = label, source_name = label })
		local diagnostic = result.diagnostics[1]
		if result.program ~= nil
			or #result.diagnostics ~= 1
			or diagnostic.code ~= case.code
			or diagnostic.detail ~= case.detail
			or diagnostic.location ~= "unknown"
		then
			table.insert(optionalChildFailures, label)
		end
	end
end
assert(#optionalChildFailures == 0, `optional child admission mismatches: {table.concat(optionalChildFailures, ", ")}`)

local function functionShapeDocument(statement: any, dead: boolean): any
	return if dead then deadMember(statement) else { root = { type = "AstStatBlock", body = { statement } } }
end

local function tableItemStatement(item: any): any
	return {
		type = "AstStatReturn",
		list = { { type = "AstExprTable", items = { item } } },
	}
end

local functionShapeCases: { any } = {
	{
		label = "local-function-value",
		code = "malformed_local_function",
		detail = "local function value is not a function expression",
		statement = {
			type = "AstStatLocalFunction",
			name = { type = "AstLocal", name = "forged", location = "function-shape-local" },
			func = { type = "AstExprConstantNil", location = "function-shape-local-value" },
		},
	},
	{
		label = "function-statement-value",
		code = "malformed_function_statement",
		detail = "function statement value is not a function expression",
		statement = {
			type = "AstStatFunction",
			name = { type = "AstExprGlobal", global = "forged" },
			func = { type = "AstExprConstantNil", location = "function-shape-statement-value" },
		},
	},
	{
		label = "function-statement-target",
		code = "malformed_function_statement",
		detail = "function statement target must be a local, global, or named index",
		field = "name",
		statement = {
			type = "AstStatFunction",
			name = {
				type = "AstExprIndexExpr",
				location = "function-shape-statement-target",
				expr = { type = "AstExprTable", items = {} },
				index = { type = "AstExprConstantString", value = "dynamic" },
			},
			func = functionWithBody(false, {}),
		},
	},
}
local functionShapeFailures = {}
for _, case in functionShapeCases do
	for _, mode in { "reachable", "dead" } do
		local label = `{mode}-{case.label}-admission`
		local result = AstFrontend.tryLift(functionShapeDocument(case.statement, mode == "dead"), {
			program_id = label,
			source_name = label,
		})
		local diagnostic = result.diagnostics[1]
		local diagnosticNode = case.statement[case.field or "func"]
		if result.program ~= nil
			or #result.diagnostics ~= 1
			or diagnostic.code ~= case.code
			or diagnostic.detail ~= case.detail
			or diagnostic.location ~= diagnosticNode.location
		then
			table.insert(functionShapeFailures, label)
		end
	end
end
assert(#functionShapeFailures == 0, `function child admission mismatches: {table.concat(functionShapeFailures, ", ")}`)

local collectionShapeCases: { any } = {
	{
		label = "expression-list",
		code = "malformed_ast",
		detail = "expected array field list",
		location = "array-shape-expression-list",
		statement = {
			type = "AstStatReturn",
			location = "array-shape-expression-list",
			list = { forged = { type = "AstExprConstantNumber", value = 7 } },
		},
	},
	{
		label = "table-items",
		code = "malformed_ast",
		detail = "expected array field items",
		location = "array-shape-table-items",
		statement = {
			type = "AstStatReturn",
			list = { {
				type = "AstExprTable",
				location = "array-shape-table-items",
				items = { forged = {
					type = "AstExprTableItem",
					kind = "item",
					value = { type = "AstExprConstantNil" },
				} },
			} },
		},
	},
	{
		label = "missing-table-item-tag",
		code = "malformed_table_item",
		detail = "table item is not an AstExprTableItem",
		location = "collection-shape-missing-table-item-tag",
		statement = tableItemStatement({
			location = "collection-shape-missing-table-item-tag",
			kind = "item",
			value = { type = "AstExprConstantNumber", value = 1 },
		}),
	},
	{
		label = "wrong-table-item-tag",
		code = "malformed_table_item",
		detail = "table item is not an AstExprTableItem",
		location = "collection-shape-wrong-table-item-tag",
		statement = tableItemStatement({
			type = "AstExprConstantNil",
			location = "collection-shape-wrong-table-item-tag",
			kind = "item",
			value = { type = "AstExprConstantNumber", value = 1 },
		}),
	},
	{
		label = "statement-list",
		code = "malformed_ast",
		detail = "expected array field body",
		location = "array-shape-statement-list",
		statement = {
			type = "AstStatBlock",
			location = "array-shape-statement-list",
			body = { forged = { type = "AstStatReturn", list = {} } },
		},
	},
	{
		label = "local-declarations",
		code = "malformed_ast",
		detail = "expected array field vars",
		location = "array-shape-local-declarations",
		statement = {
			type = "AstStatLocal",
			location = "array-shape-local-declarations",
			vars = { forged = { type = "AstLocal", name = "forged" } },
			values = {},
		},
	},
	{
		label = "function-parameters",
		code = "malformed_ast",
		detail = "expected array field args",
		location = "array-shape-function-parameters",
		statement = {
			type = "AstStatReturn",
			list = { {
				type = "AstExprFunction",
				location = "array-shape-function-parameters",
				args = { forged = { type = "AstLocal", name = "forged" } },
				body = { type = "AstStatBlock", body = {} },
			} },
		},
	},
	{
		label = "record-item-key",
		code = "malformed_table_item",
		detail = "record table item key is not a string literal",
		location = "collection-shape-record-item-key",
		statement = tableItemStatement({
			type = "AstExprTableItem",
			kind = "record",
			key = {
				type = "AstExprCall",
				location = "collection-shape-record-item-key",
				func = { type = "AstExprGlobal", global = "key_effect" },
				args = {},
			},
			value = { type = "AstExprConstantNumber", value = 1 },
		}),
	},
	{
		label = "list-item-key",
		code = "malformed_table_item",
		detail = "list table item must not carry a key expression",
		location = "collection-shape-list-item-key",
		statement = tableItemStatement({
			type = "AstExprTableItem",
			kind = "item",
			location = "collection-shape-list-item-key",
			key = {
				type = "AstExprCall",
				func = { type = "AstExprGlobal", global = "key_effect" },
				args = {},
			},
			value = { type = "AstExprConstantNumber", value = 1 },
		}),
	},
}
local collectionShapeFailures = {}
for _, case in collectionShapeCases do
	for _, mode in { "reachable", "dead" } do
		local label = `{mode}-{case.label}-collection-shape-admission`
		local result = AstFrontend.tryLift(functionShapeDocument(case.statement, mode == "dead"), {
			program_id = label,
			source_name = label,
		})
		local diagnostic = result.diagnostics[1]
		if result.program ~= nil
			or #result.diagnostics ~= 1
			or diagnostic.code ~= case.code
			or diagnostic.detail ~= case.detail
			or diagnostic.location ~= case.location
		then
			table.insert(collectionShapeFailures, label)
		end
	end
end
assert(
	#collectionShapeFailures == 0,
	`collection-shape admission mismatches: {table.concat(collectionShapeFailures, ", ")}`
)

local validTableItemCases: { any } = {
	{
		label = "record-string-key",
		expected_calls = 0,
		item = {
			type = "AstExprTableItem",
			kind = "record",
			key = { type = "AstExprConstantString", value = "field" },
			value = { type = "AstExprConstantNumber", value = 1 },
		},
	},
	{
		label = "general-call-key",
		expected_calls = 1,
		item = {
			type = "AstExprTableItem",
			kind = "general",
			key = {
				type = "AstExprCall",
				func = { type = "AstExprGlobal", global = "key_effect" },
				args = {},
			},
			value = { type = "AstExprConstantNumber", value = 1 },
		},
	},
}
for _, case in validTableItemCases do
	local label = `valid-{case.label}-admission`
	local result = AstFrontend.tryLift(functionShapeDocument(tableItemStatement(case.item), false), {
		program_id = label,
		source_name = label,
	})
	assert(result.program ~= nil and #result.diagnostics == 0, `{case.label} table item was rejected`)
	local calls = 0
	for _, instruction in (result.program :: any).instructions do
		if instruction.operation.call ~= nil then
			calls += 1
		end
	end
	assert(calls == case.expected_calls, `{case.label} table item changed key effects`)
end

local recursiveDeclaration = { type = "AstLocal", name = "recursive", location = "function-shape-recursive" }
local validFunctionStatements: { any } = {
	{
		type = "AstStatLocalFunction",
		name = recursiveDeclaration,
		func = functionWithBody(false, { {
			type = "AstStatReturn",
			list = { { type = "AstExprLocal", ["local"] = recursiveDeclaration } },
		} }),
	},
	{
		type = "AstStatFunction",
		name = { type = "AstExprGlobal", global = "assigned" },
		func = functionWithBody(false, {}),
	},
}
for index, statement in validFunctionStatements do
	local label = `valid-function-child-{index}`
	local result = AstFrontend.tryLift(functionShapeDocument(statement, false), {
		program_id = label,
		source_name = label,
	})
	assert(result.program ~= nil and #result.diagnostics == 0, `{label} was rejected`)
end

local shared = {}
local sharedInspection = inspectOk({ shared, shared }, limits(4, 4, 4))
assert(sharedInspection.table_count == 3, "acyclic shared AST input was mistaken for a cycle")

local cyclicDocument: any = {
	root = {
		type = "AstStatBlock",
		location = "0,0 - 0,0",
		body = {},
	},
}
cyclicDocument.frontend_private_cycle = cyclicDocument
local cyclicLift = AstFrontend.tryLift(cyclicDocument, {
	program_id = "cyclic-ast-admission",
	source_name = "cyclic-ast-admission",
})
assert(cyclicLift.program == nil and #cyclicLift.diagnostics == 1, "cyclic direct AST did not return one diagnostic")
assert(cyclicLift.diagnostics[1].code == "malformed_ast_graph", "cyclic direct AST diagnostic changed code")

local deepDocument: any = {
	root = {
		type = "AstStatBlock",
		location = "0,0 - 0,0",
		body = {},
	},
	frontend_private_depth = chain(AstAdmission.defaultLimits.max_depth),
}
local deepLift = AstFrontend.tryLift(deepDocument, {
	program_id = "deep-ast-admission",
	source_name = "deep-ast-admission",
})
assert(deepLift.program == nil and #deepLift.diagnostics == 1, "over-depth direct AST did not return one diagnostic")
assert(deepLift.diagnostics[1].code == "ast_resource_limit", "over-depth direct AST diagnostic changed code")

return true
