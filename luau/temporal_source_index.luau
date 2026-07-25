--!strict

-- Builds the runtime-only source index shared by temporal identity and
-- invocation-flow policy. Reaching-definition decisions remain with callers.

local AstExpressionSlots = require("./ast_expression_slots")
local AstStatementSlots = require("./ast_statement_slots")

local TemporalSourceIndex = {}

export type Record = { [string]: any }

export type Position = {
	node: Record,
	owner: Record,
	statement: Record?,
	block: Record?,
	statementIndex: number?,
}

type DeclarationKind = "local" | "local_function" | "parameter" | "loop_variable"

export type Declaration = {
	owner: Record,
	kind: DeclarationKind,
}

type DefinitionKind = "declaration" | "local_function" | "parameter" | "loop_variable" | "assignment" | "compound_assignment" | "function_statement"

export type Definition = {
	owner: Record,
	statement: Record?,
	block: Record?,
	statementIndex: number?,
	expression: Record?,
	resultOrdinal: number,
	kind: DefinitionKind,
	repeated: boolean,
}

export type Index = {
	positions: { [any]: Position },
	repeatDepths: { [any]: number },
	parents: { [any]: Record },
	localUses: { [string]: { Record } },
	blockParents: { [any]: Record },
	declarations: { [string]: Declaration },
	definitions: { [string]: { Definition } },
}

local function expectRecord(value: any, label: string): Record
	assert(type(value) == "table", `{label} must be an AST object`)
	return value :: Record
end

local function expectLocation(value: any, label: string): string
	assert(type(value) == "string" and value ~= "", `{label} must have a source location`)
	return value
end

function TemporalSourceIndex.declarationLocation(value: any, label: string): string
	local declaration = expectRecord(value, label)
	assert(declaration.type == "AstLocal", `{label} must be an AST local declaration`)
	return expectLocation(declaration.location, label)
end

local function addDeclaration(index: Index, value: any, owner: Record, kind: DeclarationKind): string
	local location = TemporalSourceIndex.declarationLocation(value, "temporal target declaration")
	local prior = index.declarations[location]
	if prior == nil then
		index.declarations[location] = { owner = owner, kind = kind }
	else
		assert(prior.owner == owner and prior.kind == kind, `temporal target declaration {location} is ambiguous`)
	end
	return location
end

local function addDefinition(
	index: Index,
	location: string,
	owner: Record,
	statement: Record?,
	block: Record?,
	statementIndex: number?,
	expression: Record?,
	kind: DefinitionKind,
	repeated: boolean,
	resultOrdinal: number?
)
	local definitions = index.definitions[location]
	if definitions == nil then
		definitions = {}
		index.definitions[location] = definitions
	end
	table.insert(definitions, {
		owner = owner,
		statement = statement,
		block = block,
		statementIndex = statementIndex,
		expression = expression,
		resultOrdinal = resultOrdinal or 1,
		kind = kind,
		repeated = repeated,
	})
end

local function selectedAssignmentExpression(values: any, targetOrdinal: any): (Record?, number)
	if type(values) ~= "table" or type(targetOrdinal) ~= "number" then
		return nil, 1
	end
	local valueCount = #values
	if targetOrdinal <= valueCount then
		return if type(values[targetOrdinal]) == "table" then values[targetOrdinal] :: Record else nil, 1
	elseif valueCount == 0 or type(values[valueCount]) ~= "table" then
		return nil, 1
	end
	local tail = values[valueCount] :: Record
	if tail.type ~= "AstExprCall" and tail.type ~= "AstExprVarargs" then
		return nil, 1
	end
	return tail, targetOrdinal - valueCount + 1
end

local function directLocalTarget(value: any): string?
	if type(value) ~= "table" then
		return nil
	end
	local target = value :: Record
	if target.type ~= "AstExprLocal" or type(target["local"]) ~= "table" then
		return nil
	end
	return TemporalSourceIndex.declarationLocation(target["local"], "temporal target write")
end

local function collectStatementDefinitions(
	index: Index,
	statement: Record,
	owner: Record,
	block: Record,
	statementIndex: number,
	repeatDepth: number
)
	local kind = statement.type
	if kind == "AstStatLocal" and type(statement.vars) == "table" then
		for indexInStatement, variable in statement.vars do
			local location = addDeclaration(index, variable, owner, "local")
			local expression, resultOrdinal = selectedAssignmentExpression(statement.values, indexInStatement)
			addDefinition(
				index,
				location,
				owner,
				statement,
				block,
				statementIndex,
				expression,
				"declaration",
				repeatDepth > 0,
				resultOrdinal
			)
		end
	elseif kind == "AstStatLocalFunction" then
		local location = addDeclaration(index, statement.name, owner, "local_function")
		addDefinition(
			index,
			location,
			owner,
			statement,
			block,
			statementIndex,
			if type(statement.func) == "table" then statement.func :: Record else nil,
			"local_function",
			repeatDepth > 0
		)
	elseif kind == "AstStatFor" then
		local location = addDeclaration(index, statement.var, owner, "loop_variable")
		addDefinition(index, location, owner, statement, block, statementIndex, nil, "loop_variable", true)
	elseif kind == "AstStatForIn" and type(statement.vars) == "table" then
		for _, variable in statement.vars do
			local location = addDeclaration(index, variable, owner, "loop_variable")
			addDefinition(index, location, owner, statement, block, statementIndex, nil, "loop_variable", true)
		end
	elseif kind == "AstStatAssign" and type(statement.vars) == "table" then
		for indexInStatement, target in statement.vars do
			local location = directLocalTarget(target)
			if location ~= nil then
				local expression, resultOrdinal = selectedAssignmentExpression(statement.values, indexInStatement)
				addDefinition(
					index,
					location,
					owner,
					statement,
					block,
					statementIndex,
					expression,
					"assignment",
					repeatDepth > 0,
					resultOrdinal
				)
			end
		end
	elseif kind == "AstStatCompoundAssign" then
		local location = directLocalTarget(statement.var)
		if location ~= nil then
			addDefinition(index, location, owner, statement, block, statementIndex, nil, "compound_assignment", repeatDepth > 0)
		end
	elseif kind == "AstStatFunction" then
		local location = directLocalTarget(statement.name)
		if location ~= nil then
			addDefinition(
				index,
				location,
				owner,
				statement,
				block,
				statementIndex,
				if type(statement.func) == "table" then statement.func :: Record else nil,
				"function_statement",
				repeatDepth > 0
			)
		end
	end
end

function TemporalSourceIndex.isRepeatedStatement(value: Record): boolean
	return value.type == "AstStatWhile"
		or value.type == "AstStatRepeat"
		or value.type == "AstStatFor"
		or value.type == "AstStatForIn"
end

function TemporalSourceIndex.analyze(document: Record): Index
	local index: Index = {
		positions = {},
		repeatDepths = {},
		parents = {},
		localUses = {},
		blockParents = {},
		declarations = {},
		definitions = {},
	}
	local root = expectRecord(document.root, "temporal target document root")
	local visitNode: (
		any,
		Record,
		Record?,
		Record?,
		number?,
		number,
		Record?,
		AstStatementSlots.Role?,
		AstExpressionSlots.Role?
	) -> ()
	local visitBlock: (Record, Record, Record?, number) -> ()

	visitBlock = function(block: Record, owner: Record, parentStatement: Record?, repeatDepth: number)
		if parentStatement ~= nil then
			index.blockParents[block] = parentStatement
		end
		local body = block.body
		assert(type(body) == "table", "temporal target statement block must have a body")
		for statementIndex, statementValue in body do
			local statement = expectRecord(statementValue, "temporal target statement")
			collectStatementDefinitions(index, statement, owner, block, statementIndex, repeatDepth)
			visitNode(statement, owner, statement, block, statementIndex, repeatDepth, block, nil, nil)
		end
	end

	visitNode = function(
		value: any,
		owner: Record,
		statement: Record?,
		block: Record?,
		statementIndex: number?,
		repeatDepth: number,
		parent: Record?,
		statementRole: AstStatementSlots.Role?,
		expressionRole: AstExpressionSlots.Role?
	)
		if type(value) ~= "table" then
			return
		end
		local node = value :: Record
		if parent ~= nil then
			index.parents[node] = parent :: Record
		end
		if node.type == nil then
			for key, child in node do
				if type(child) == "table" then
					local childStatementRole = AstStatementSlots.childRole(statementRole, node, key, child)
					local childExpressionRole = AstExpressionSlots.childRole(expressionRole, node, key, child)
					if childStatementRole ~= nil or childExpressionRole ~= nil then
						visitNode(
							child,
							owner,
							statement,
							block,
							statementIndex,
							repeatDepth,
							parent,
							childStatementRole,
							childExpressionRole
						)
					end
				end
			end
			return
		elseif node.type == "AstLocal" then
			return
		end
		index.positions[node] = {
			node = node,
			owner = owner,
			statement = statement,
			block = block,
			statementIndex = statementIndex,
		}
		index.repeatDepths[node] = repeatDepth
		if node.type == "AstExprLocal" and type(node["local"]) == "table" then
			local localNode = node["local"] :: Record
			local location = localNode.location
			assert(type(location) == "string" and location ~= "", "temporal local use has no declaration location")
			local uses = index.localUses[location]
			if uses == nil then
				uses = {}
				index.localUses[location] = uses
			end
			table.insert(uses, node)
		end
		if node.type == "AstStatBlock" then
			visitBlock(node, owner, statement, repeatDepth)
			return
		elseif node.type == "AstExprFunction" then
			if type(node.args) == "table" then
				for _, parameter in node.args do
					local location = addDeclaration(index, parameter, node, "parameter")
					addDefinition(index, location, node, nil, nil, nil, nil, "parameter", false)
				end
			end
			visitBlock(expectRecord(node.body, "temporal target function body"), node, nil, 0)
			return
		end

		local nestedRepeatDepth = repeatDepth
		if TemporalSourceIndex.isRepeatedStatement(node) then
			nestedRepeatDepth += 1
		end
		for key, child in node do
			if type(child) == "table" then
				local childStatementRole = AstStatementSlots.childRole(statementRole, node, key, child)
				local childExpressionRole = AstExpressionSlots.childRole(expressionRole, node, key, child)
				if childStatementRole == nil and childExpressionRole == nil then
					continue
				end
				visitNode(
					child,
					owner,
					statement,
					block,
					statementIndex,
					if key == "body" then nestedRepeatDepth else repeatDepth,
					node,
					childStatementRole,
					childExpressionRole
				)
			end
		end
	end

	index.positions[root] = { node = root, owner = root, statement = nil, block = nil, statementIndex = nil }
	index.repeatDepths[root] = 0
	visitBlock(root, root, nil, 0)
	return index
end

return table.freeze(TemporalSourceIndex)
