--!strict

-- Bounded preflight for parser-produced and direct source AST graphs. Semantic
-- lowering remains in ast_frontend; this owner only admits traversal shape and
-- indexes runtime-local identity and extracts mutation/reassignment candidates
-- needed before lexical lowering.

local AstLocalIdentity = require("./ast_local_identity")
local AstLexicalScope = require("./ast_lexical_scope")
local AstRuntimeContext = require("./ast_runtime_context")
local AstExpressionSlots = require("./ast_expression_slots")
local AstStatementSlots = require("./ast_statement_slots")
local AstExpressionScalar = require("./ast_expression_scalar")

local AstAdmission = {}

type Record = { [string]: any }

export type Limits = {
	max_tables: number,
	max_entries: number,
	max_depth: number,
}

export type Problem = {
	code: string,
	node: Record?,
	detail: string,
}

export type Inspection = {
	mutable_local_nodes: { Record },
	reassigned_local_nodes: { Record },
	written_global_names: { string },
	table_count: number,
	entry_count: number,
	max_depth: number,
}

type Frame = {
	value: Record,
	depth: number,
	exiting: boolean,
	statement_role: AstStatementSlots.Role?,
	expression_role: AstExpressionSlots.Role?,
	expression_owner: Record?,
	array_problem: Problem?,
	nullable_array_length: number?,
	function_owner: number,
	lexical_context: AstLexicalScope.Context,
	runtime_context: AstRuntimeContext.Context,
}

type RuntimeFrame = {
	value: Record,
	statement_role: AstStatementSlots.Role?,
	expression_role: AstExpressionSlots.Role?,
}

AstAdmission.maxSourceBytes = 16 * 1024 * 1024
AstAdmission.maxParserBytes = 64 * 1024 * 1024
AstAdmission.defaultLimits = table.freeze({
	max_tables = 256 * 1024,
	max_entries = 1024 * 1024,
	max_depth = 256,
})

local function expectLimit(value: number, label: string)
	assert(value >= 1 and value % 1 == 0, `{label} must be a positive integer`)
end

function AstAdmission.expectBytes(value: any, label: string, limit: number): string
	expectLimit(limit, "byte limit")
	assert(type(value) == "string", `{label} must be a byte string`)
	assert(#value <= limit, `{label} exceeds the byte limit of {limit}`)
	return value
end

function AstAdmission.expectSourceBytes(value: any, label: string): string
	return AstAdmission.expectBytes(value, label, AstAdmission.maxSourceBytes)
end

function AstAdmission.expectParserBytes(value: any, label: string): string
	return AstAdmission.expectBytes(value, label, AstAdmission.maxParserBytes)
end

function AstAdmission.decodeBytes(value: any, label: string, limit: number, decode: (string) -> any): any
	local bytes = AstAdmission.expectBytes(value, label, limit)
	return decode(bytes)
end

local signedBytePrefix = string.char(0xef, 0xbf, 0xbf) .. "ff"

-- luau-ast writes a number literal as the "%.17g" text of the parser's double, which names that double exactly, and a
-- recovery manifest writes the number of a literal key as JSON text. Lune's serde.decode("json") can read such a text
-- one or two units in the last place away, so each one crosses the decoder as the JSON string "#<text>" and is read
-- back with tonumber, which rounds correctly.
local parserNumberLiteral = '("type":"AstExprConstantNumber","location":"[^"]*","value":)(%d[%d%.eE+%-]*)'
-- luau-ast writes a number literal that overflows a double, such as 1e999, which Luau reads as math.huge, as the bare
-- token Infinity, which is not JSON. Such a value crosses the decoder as the marked decimal text 1e999, which tonumber
-- reads back as math.huge; the pattern for the token runs only on a document that holds the token.
local parserInfiniteLiteral = '("type":"AstExprConstantNumber","location":"[^"]*","value":)Infinity}'
local manifestNumberField = '("number"%s*:%s*)(%-?%d[%d%.eE+%-]*)'

local function markedNumber(text: string, label: string): number
	local exact = tonumber(string.match(text, "^#(%-?%d[%d%.eE+%-]*)$") or "")
	assert(exact ~= nil, `{label} text is not a decimal number`)
	return exact
end

local function recoverParserString(value: string): string
	return string.gsub(value, signedBytePrefix .. "(%x%x)", function(hexByte: string): string
		local byte = tonumber(hexByte, 16)
		if byte == nil or byte < 0x80 then
			return signedBytePrefix .. hexByte
		end
		return string.char(byte)
	end)
end

local function recoverParserStrings(value: any): any
	if type(value) ~= "table" then
		return value
	end
	local stack: { Record } = { value :: Record }
	local visited: { [Record]: boolean } = {}
	local tableCount = 0
	local entryCount = 0
	while #stack > 0 do
		local record = table.remove(stack) :: Record
		if visited[record] then
			continue
		end
		visited[record] = true
		tableCount += 1
		assert(tableCount <= AstAdmission.defaultLimits.max_tables, "decoded parser AST exceeds the table limit")
		for key, child in record do
			entryCount += 1
			assert(entryCount <= AstAdmission.defaultLimits.max_entries, "decoded parser AST exceeds the entry limit")
			if type(child) == "string" then
				if key == "value" and record.type == "AstExprConstantNumber" and string.sub(child, 1, 1) == "#" then
					record[key] = markedNumber(child, "parser number literal")
				else
					record[key] = recoverParserString(child)
				end
			elseif type(child) == "number" and key == "value" and record.type == "AstExprConstantNumber" then
				error("parser number literal did not use exact text transport", 0)
			elseif type(child) == "table" then
				table.insert(stack, child :: Record)
			end
		end
	end
	return value
end

function AstAdmission.decodeParserBytes(value: any, label: string, decode: (string) -> any): any
	local bytes = AstAdmission.expectParserBytes(value, label)
	local marked = string.gsub(bytes, parserNumberLiteral, '%1"#%2"')
	if string.find(marked, '"value":Infinity}', 1, true) ~= nil then
		marked = string.gsub(marked, parserInfiniteLiteral, '%1"#1e999"}')
	end
	return recoverParserStrings(decode(marked))
end

-- A recovery manifest names the number of a literal key in a field named number, its only field of that name; the
-- manifest is decoded with each such number read from its text. Every text the transport marks is read back and
-- nothing else is, so a field named number that holds a string beginning with # is refused.
function AstAdmission.decodeManifestBytes(bytes: string, decode: (string) -> any): any
	local marked, markedCount = string.gsub(bytes, manifestNumberField, '%1"#%2"')
	local decoded = decode(marked)
	local readCount = 0
	local stack: { any } = { decoded }
	while #stack > 0 do
		local item = table.remove(stack)
		if type(item) == "table" then
			local record = item :: Record
			for key, child in record do
				if key == "number" and type(child) == "string" and string.sub(child, 1, 1) == "#" then
					record[key] = markedNumber(child, "recovery manifest number")
					readCount += 1
				elseif key == "number" and type(child) == "number" then
					error("recovery manifest number did not use exact text transport", 0)
				elseif type(child) == "table" then
					table.insert(stack, child)
				end
			end
		end
	end
	assert(readCount == markedCount, "recovery manifest holds a number text that the exact transport did not mark")
	return decoded
end

local function resourceProblem(node: Record, detail: string): Problem
	return { code = "ast_resource_limit", node = node, detail = detail }
end

local function nullableParserArrayLength(parent: Record, key: any): number?
	if parent.type ~= "AstTypeFunction" or key ~= "argNames" then
		return nil
	end
	local argumentTypes = parent.argTypes
	if type(argumentTypes) ~= "table" then
		return nil
	end
	local types = (argumentTypes :: Record).types
	if type(types) ~= "table" then
		return nil
	end
	return #(types :: { any })
end

function AstAdmission.visitRuntime(value: Record, visit: (Record) -> ())
	local runtimeRoot = if type(value.root) == "table" then value.root :: Record else value
	local stack: { RuntimeFrame } = { {
		value = runtimeRoot,
		statement_role = nil,
		expression_role = nil,
	} }
	while #stack > 0 do
		local frame = table.remove(stack) :: RuntimeFrame
		local record = frame.value
		visit(record)
		for key, child in record do
			if type(child) == "table" then
				local statementRole = AstStatementSlots.childRole(frame.statement_role, record, key, child)
				local expressionRole = AstExpressionSlots.childRole(frame.expression_role, record, key, child)
				if statementRole ~= nil or expressionRole ~= nil then
					table.insert(stack, {
						value = child :: Record,
						statement_role = statementRole,
						expression_role = expressionRole,
					})
				end
			end
		end
	end
end

local function appendMutableLocal(nodes: { Record }, value: any)
	if type(value) ~= "table" then
		return
	end
	local target = value :: Record
	if target.type == "AstExprLocal" and type(target["local"]) == "table" then
		table.insert(nodes, target["local"] :: Record)
	end
end

local function appendWrittenGlobal(names: { string }, value: any)
	if type(value) == "table" and value.type == "AstExprGlobal" and type(value.global) == "string" then
		table.insert(names, value.global)
	end
end

local function collectMutationCandidates(
	record: Record,
	mutableNodes: { Record },
	reassignedNodes: { Record },
	writtenGlobals: { string },
	limit: number
): Problem?
	if record.type == "AstStatAssign" and type(record.vars) == "table" then
		local scanned = 0
		for _, target in record.vars :: Record do
			scanned += 1
			if scanned > limit then
				return resourceProblem(record, `AST mutation target scan exceeds the entry limit of {limit}`)
			end
			appendMutableLocal(mutableNodes, target)
			appendMutableLocal(reassignedNodes, target)
			appendWrittenGlobal(writtenGlobals, target)
		end
	elseif record.type == "AstStatCompoundAssign" then
		appendMutableLocal(mutableNodes, record.var)
		appendMutableLocal(reassignedNodes, record.var)
		appendWrittenGlobal(writtenGlobals, record.var)
	elseif record.type == "AstStatLocalFunction" and type(record.name) == "table" then
		table.insert(mutableNodes, record.name :: Record)
	elseif record.type == "AstStatFunction" then
		appendMutableLocal(mutableNodes, record.name)
		appendMutableLocal(reassignedNodes, record.name)
		appendWrittenGlobal(writtenGlobals, record.name)
	end
	return nil
end

function AstAdmission.inspect(value: any, requestedLimits: Limits?): (Inspection?, Problem?)
	if type(value) ~= "table" then
		return nil, {
			code = "malformed_document",
			node = nil,
			detail = "source AST root must be a table",
		}
	end
	local limits = requestedLimits or AstAdmission.defaultLimits
	expectLimit(limits.max_tables, "AST table limit")
	expectLimit(limits.max_entries, "AST entry limit")
	expectLimit(limits.max_depth, "AST depth limit")

	local root = value :: Record
	local lexicalState, rootLexicalContext = AstLexicalScope.initialize(root)
	local stack: { Frame } = { {
		value = root,
		depth = 1,
		exiting = false,
		statement_role = nil,
		expression_role = nil,
		expression_owner = nil,
		array_problem = nil,
		nullable_array_length = nil,
		function_owner = 0,
		lexical_context = rootLexicalContext,
		runtime_context = AstRuntimeContext.root(),
	} }
	local active: { [any]: boolean } = {}
	local mutableLocalNodes: { Record } = {}
	local reassignedLocalNodes: { Record } = {}
	local writtenGlobalNames: { string } = {}
	local runtimeDeclarationRecords: { AstLocalIdentity.OwnedRecord } = {}
	local runtimeReferenceRecords: { AstLocalIdentity.OwnedRecord } = {}
	local functionParents: { [number]: number } = {}
	local nextFunctionOwner = 0
	local tableCount = 0
	local entryCount = 0
	local maximumDepth = 0

	while #stack > 0 do
		local frame = table.remove(stack) :: Frame
		local record = frame.value
		if frame.exiting then
			local scalarProblem = AstExpressionScalar.validatePostorder(record)
			if scalarProblem ~= nil then
				return nil, scalarProblem
			end
			active[record] = nil
			continue
		end
		if active[record] then
			return nil, {
				code = "malformed_ast_graph",
				node = record,
				detail = "source AST graph contains a cycle",
			}
		end
		if getmetatable(record :: any) ~= nil then
			return nil, {
				code = "malformed_ast_graph",
				node = record,
				detail = "source AST tables must not have metatables",
			}
		end
		if frame.depth > limits.max_depth then
			return nil, resourceProblem(record, `source AST exceeds the depth limit of {limits.max_depth}`)
		end
		tableCount += 1
		if tableCount > limits.max_tables then
			return nil, resourceProblem(record, `source AST exceeds the table limit of {limits.max_tables}`)
		end
		maximumDepth = math.max(maximumDepth, frame.depth)
		local childFunctionOwner = frame.function_owner
		if record.type == "AstExprFunction" then
			nextFunctionOwner += 1
			childFunctionOwner = nextFunctionOwner
			functionParents[childFunctionOwner] = frame.function_owner
		end
		local bodyLexicalScope = AstLexicalScope.reserveBody(lexicalState, record, frame.lexical_context)

		if record.type == "AstStatError" then
			return nil, {
				code = "malformed_source_statement",
				node = record,
				detail = "parser recovery statement cannot be admitted as runtime semantics",
			}
		elseif record.type == "AstExprError" then
			return nil, {
				code = "malformed_source_expression",
				node = record,
				detail = "parser recovery expression cannot be admitted as runtime semantics",
			}
		end
		local expressionProblem = AstExpressionSlots.validateRole(frame.expression_role, record, frame.expression_owner)
		if expressionProblem ~= nil then
			return nil, expressionProblem
		end
		local statementProblem = AstStatementSlots.validateRole(frame.statement_role, record)
		if statementProblem ~= nil then
			return nil, statementProblem
		end
		local contextProblem = AstRuntimeContext.validate(record, frame.runtime_context)
		if contextProblem ~= nil then
			return nil, contextProblem
		end
		if record.type == "AstStatLocal"
			or record.type == "AstStatLocalFunction"
			or record.type == "AstExprFunction"
			or record.type == "AstStatFor"
			or record.type == "AstStatForIn"
		then
			local declarationContext = AstLexicalScope.declarationContext(record, frame.lexical_context, bodyLexicalScope)
			table.insert(runtimeDeclarationRecords, {
				value = record,
				function_owner = if record.type == "AstExprFunction" then childFunctionOwner else frame.function_owner,
				lexical_scope = declarationContext.scope,
				lexical_position = declarationContext.position,
			})
		end
		if record.type == "AstExprLocal" then
			table.insert(runtimeReferenceRecords, {
				value = record,
				function_owner = frame.function_owner,
				lexical_scope = frame.lexical_context.scope,
				lexical_position = frame.lexical_context.position,
			})
		end

		active[record] = true
		table.insert(stack, {
			value = record,
			depth = frame.depth,
			exiting = true,
			statement_role = frame.statement_role,
			expression_role = frame.expression_role,
			expression_owner = frame.expression_owner,
			array_problem = frame.array_problem,
			nullable_array_length = frame.nullable_array_length,
			function_owner = frame.function_owner,
			lexical_context = frame.lexical_context,
			runtime_context = frame.runtime_context,
		})
		local hasStringKey = false
		local hasNumberKey = false
		local numericCount = 0
		local numericLength = frame.nullable_array_length or #(record :: any)
		for key, child in next, record do
			entryCount += 1
			if entryCount > limits.max_entries then
				return nil, resourceProblem(record, `source AST exceeds the entry limit of {limits.max_entries}`)
			end
			local positiveIntegerKey = type(key) == "number" and key % 1 == 0 and key >= 1
			if frame.array_problem ~= nil and not positiveIntegerKey then
				return nil, frame.array_problem
			elseif type(key) == "string" then
				hasStringKey = true
			elseif positiveIntegerKey then
				hasNumberKey = true
				numericCount += 1
				if key > numericLength then
					return nil, {
						code = "malformed_ast_graph",
						node = record,
						detail = "source AST arrays must be dense",
					}
				end
			else
				return nil, {
					code = "malformed_ast_graph",
					node = record,
					detail = "source AST tables may use only string fields or positive integer indexes",
				}
			end
			if hasStringKey and hasNumberKey then
				return nil, {
					code = "malformed_ast_graph",
					node = record,
					detail = "source AST tables must not mix record fields and array indexes",
				}
			end
			local statementRole = AstStatementSlots.childRole(frame.statement_role, record, key, child)
			local expressionRole = AstExpressionSlots.childRole(frame.expression_role, record, key, child)
			local expressionOwner = if expressionRole ~= nil and expressionRole.surface == "call_statement" then record else nil
			local arrayProblem: Problem? = nil
			local nullableArrayLength = nullableParserArrayLength(record, key)
			if expressionRole ~= nil and (expressionRole.kind == "expression_array" or expressionRole.kind == "table_item_array") then
				arrayProblem = AstExpressionSlots.scalarProblem(expressionRole, record)
			elseif statementRole ~= nil and statementRole.kind == "statement_array" then
				arrayProblem = AstStatementSlots.scalarProblem(statementRole, record)
			elseif nullableArrayLength ~= nil then
				arrayProblem = {
					code = "malformed_ast_graph",
					node = record,
					detail = "function type argument names must be a nullable array",
				}
			else
				arrayProblem = AstLocalIdentity.declarationArrayProblem(record, key)
			end
			if statementRole ~= nil and type(child) ~= "table" then
				return nil, AstStatementSlots.scalarProblem(statementRole, record)
			end
			if expressionRole ~= nil and type(child) ~= "table" then
				return nil, AstExpressionSlots.scalarProblem(expressionRole, record)
			end
			if type(child) == "table" then
				local childRecord = child :: Record
				local childRuntimeContext = AstRuntimeContext.child(record, key, childRecord, frame.runtime_context)
				local childLexicalContext = AstLexicalScope.childContext(
					lexicalState,
					record,
					key,
					childRecord,
					frame.lexical_context,
					bodyLexicalScope
				)
				table.insert(stack, {
					value = childRecord,
					depth = frame.depth + 1,
					exiting = false,
					statement_role = statementRole,
					expression_role = expressionRole,
					expression_owner = expressionOwner,
					array_problem = arrayProblem,
					nullable_array_length = nullableArrayLength,
					function_owner = childFunctionOwner,
					lexical_context = childLexicalContext,
					runtime_context = childRuntimeContext,
				})
			end
		end
		if hasNumberKey and frame.nullable_array_length == nil and numericCount ~= numericLength then
			return nil, {
				code = "malformed_ast_graph",
				node = record,
				detail = "source AST arrays must be dense",
			}
		end
		local earlyDeclarationProblem = AstLocalIdentity.validateEarlyDeclarationShape(record)
		if earlyDeclarationProblem ~= nil then
			return nil, earlyDeclarationProblem
		end
		local requiredExpressionProblem = AstExpressionSlots.validateRequired(frame.expression_role, record)
		if requiredExpressionProblem ~= nil then
			return nil, requiredExpressionProblem
		end
		local requiredStatementProblem = AstStatementSlots.validateRequired(frame.statement_role, record)
		if requiredStatementProblem ~= nil then
			return nil, requiredStatementProblem
		end
		local lateDeclarationProblem = AstLocalIdentity.validateLateDeclarationShape(record)
		if lateDeclarationProblem ~= nil then
			return nil, lateDeclarationProblem
		end
		local scalarProblem = AstExpressionScalar.validatePreorder(record)
		if scalarProblem ~= nil then
			return nil, scalarProblem
		end
	end

	local identityProblem = AstLocalIdentity.validate(
		runtimeDeclarationRecords,
		runtimeReferenceRecords,
		functionParents,
		lexicalState.scopes
	)
	if identityProblem ~= nil then
		return nil, identityProblem
	end

	local mutationRecords: { Record } = {}
	AstAdmission.visitRuntime(root, function(record: Record)
		if record.type == "AstStatAssign"
			or record.type == "AstStatCompoundAssign"
			or record.type == "AstStatLocalFunction"
			or record.type == "AstStatFunction"
		then
			table.insert(mutationRecords, record)
		end
	end)
	for _, record in mutationRecords do
		local mutationProblem = collectMutationCandidates(record, mutableLocalNodes, reassignedLocalNodes, writtenGlobalNames, limits.max_entries)
		if mutationProblem ~= nil then
			return nil, mutationProblem
		end
	end

	return {
		mutable_local_nodes = mutableLocalNodes,
		reassigned_local_nodes = reassignedLocalNodes,
		written_global_names = writtenGlobalNames,
		table_count = tableCount,
		entry_count = entryCount,
		max_depth = maximumDepth,
	}, nil
end

return table.freeze(AstAdmission)
