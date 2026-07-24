--!strict

-- Canonical runtime-local identity, function ownership, and lexical visibility
-- validation for the bounded AST records collected by ast_admission.

local AstLocalBinding = require("./ast_local_binding")

local AstLocalIdentity = {}

type Record = { [string]: any }

export type Problem = {
	code: string,
	node: Record?,
	detail: string,
}

export type OwnedRecord = {
	value: Record,
	function_owner: number,
	lexical_scope: number,
	lexical_position: number,
}

export type LexicalScope = {
	parent: number,
	entry_position: number,
}

type DeclarationRole = {
	code: string,
	missing_detail: string,
	name_detail: string,
	name_first: boolean,
}

local function declarationRole(code: string, missingDetail: string, nameDetail: string?, nameFirst: boolean?): DeclarationRole
	return {
		code = code,
		missing_detail = missingDetail,
		name_detail = nameDetail or "local declaration is missing its name",
		name_first = nameFirst == true,
	}
end

local localDeclarationRole = declarationRole(
	"malformed_local_declaration",
	"local declaration variable is not an AST local"
)
local localFunctionRole = declarationRole("malformed_local_function", "local function is missing its lexical identity")
local numericForRole = declarationRole(
	"malformed_numeric_for",
	"numeric for is missing its lexical variable",
	"numeric-for variable has no name",
	true
)
local genericForRole = declarationRole(
	"malformed_generic_for",
	"generic-for variable is not a lexical local",
	"generic-for variable has no name",
	true
)
local functionParameterRole = declarationRole(
	"malformed_function_parameter",
	"function parameter is not a local declaration"
)

function AstLocalIdentity.validateEarlyDeclarationShape(record: Record): Problem?
	if record.type == "AstStatLocal" and type(record.vars) ~= "table" then
		return {
			code = "malformed_ast",
			node = record,
			detail = "expected array field vars",
		}
	elseif record.type == "AstStatForIn" and (type(record.vars) ~= "table" or #record.vars == 0) then
		return {
			code = "malformed_generic_for",
			node = record,
			detail = "generic for must declare at least one lexical variable",
		}
	end
	return nil
end

function AstLocalIdentity.validateLateDeclarationShape(record: Record): Problem?
	if record.type == "AstExprFunction" and type(record.args) ~= "table" then
		return {
			code = "malformed_ast",
			node = record,
			detail = "expected array field args",
		}
	end
	return nil
end

function AstLocalIdentity.declarationArrayProblem(record: Record, key: any): Problem?
	if key == "vars" and record.type == "AstStatLocal" then
		return {
			code = "malformed_ast",
			node = record,
			detail = "expected array field vars",
		}
	elseif key == "vars" and record.type == "AstStatForIn" then
		return {
			code = "malformed_generic_for",
			node = record,
			detail = "generic for must declare at least one lexical variable",
		}
	elseif key == "args" and record.type == "AstExprFunction" then
		return {
			code = "malformed_ast",
			node = record,
			detail = "expected array field args",
		}
	end
	return nil
end

local function expectRuntimeLocalIdentity(value: any, owner: Record, role: string): (Record?, Problem?)
	if type(value) ~= "table" then
		return nil, {
			code = "malformed_local_identity",
			node = owner,
			detail = `{role} identity must be an AST local`,
		}
	end
	local localNode = value :: Record
	if localNode.type ~= "AstLocal"
		or type(localNode.location) ~= "string"
		or localNode.location == ""
		or type(localNode.name) ~= "string"
		or localNode.name == ""
	then
		return nil, {
			code = "malformed_local_identity",
			node = localNode,
			detail = `{role} must have a nonempty name and source location`,
		}
	end
	return localNode, nil
end

local function expectRuntimeDeclarationIdentity(value: any, role: DeclarationRole): (Record?, Problem?)
	if type(value) ~= "table" then
		return nil, {
			code = role.code,
			node = nil,
			detail = role.missing_detail,
		}
	end
	local localNode = value :: Record
	local nameIsMissing = type(localNode.name) ~= "string" or localNode.name == ""
	if role.name_first and nameIsMissing then
		return nil, {
			code = role.code,
			node = localNode,
			detail = role.name_detail,
		}
	elseif localNode.type ~= "AstLocal"
		or type(localNode.location) ~= "string"
		or localNode.location == ""
	then
		return nil, {
			code = role.code,
			node = localNode,
			detail = "local declaration is missing its source location",
		}
	elseif nameIsMissing then
		return nil, {
			code = role.code,
			node = localNode,
			detail = role.name_detail,
		}
	end
	return localNode, nil
end

local function indexRuntimeDeclaration(
	index: AstLocalBinding.Index,
	value: any,
	role: DeclarationRole,
	owned: OwnedRecord,
	lexicalRank: number
): Problem?
	local declarationValue, identityProblem = expectRuntimeDeclarationIdentity(value, role)
	if identityProblem ~= nil then
		return identityProblem
	elseif declarationValue == nil then
		return nil
	end
	local declaration = declarationValue :: Record
	return AstLocalBinding.add(index, {
		value = declaration,
		function_owner = owned.function_owner,
		lexical_scope = owned.lexical_scope,
		lexical_position = owned.lexical_position,
		lexical_rank = lexicalRank,
	})
end

local function indexRuntimeDeclarationArray(
	index: AstLocalBinding.Index,
	value: any,
	role: DeclarationRole,
	owned: OwnedRecord,
	rankOffset: number
): Problem?
	if type(value) ~= "table" then
		return nil
	end
	for rank, declaration in value :: { any } do
		local problem = indexRuntimeDeclaration(index, declaration, role, owned, rankOffset + rank)
		if problem ~= nil then
			return problem
		end
	end
	return nil
end

local function indexRuntimeDeclarations(
	index: AstLocalBinding.Index,
	owned: OwnedRecord
): Problem?
	local record = owned.value
	if record.type == "AstStatLocal" then
		return indexRuntimeDeclarationArray(index, record.vars, localDeclarationRole, owned, 0)
	elseif record.type == "AstStatForIn" then
		return indexRuntimeDeclarationArray(index, record.vars, genericForRole, owned, 0)
	elseif record.type == "AstStatLocalFunction" then
		return indexRuntimeDeclaration(index, record.name, localFunctionRole, owned, 1)
	elseif record.type == "AstStatFor" then
		return indexRuntimeDeclaration(index, record.var, numericForRole, owned, 1)
	elseif record.type == "AstExprFunction" then
		local rankOffset = 0
		if record.self ~= nil then
			local selfProblem = indexRuntimeDeclaration(index, record.self, functionParameterRole, owned, 1)
			if selfProblem ~= nil then
				return selfProblem
			end
			rankOffset = 1
		end
		return indexRuntimeDeclarationArray(index, record.args, functionParameterRole, owned, rankOffset)
	end
	return nil
end

local function scopeIsVisible(
	lexicalScopes: { [number]: LexicalScope },
	referenceScope: number,
	referencePosition: number,
	declarationScope: number,
	declarationPosition: number
): boolean
	local scope = referenceScope
	local position = referencePosition
	while scope ~= declarationScope do
		if scope == 0 then
			return false
		end
		local link = lexicalScopes[scope]
		if link == nil then
			return false
		end
		position = link.entry_position
		scope = link.parent
	end
	return position >= declarationPosition
end

local function ownerIsVisible(functionParents: { [number]: number }, referenceOwner: number, declarationOwner: number): boolean
	local owner = referenceOwner
	while true do
		if owner == declarationOwner then
			return true
		elseif owner == 0 then
			return false
		end
		local parent = functionParents[owner]
		if parent == nil then
			return false
		end
		owner = parent
	end
end

local function validateRuntimeLocalReference(
	index: AstLocalBinding.Index,
	functionParents: { [number]: number },
	lexicalScopes: { [number]: LexicalScope },
	owned: OwnedRecord
): Problem?
	local record = owned.value
	local referenceValue, identityProblem = expectRuntimeLocalIdentity(record["local"], record, "runtime local reference")
	if identityProblem ~= nil then
		return identityProblem
	end
	local reference = referenceValue :: Record
	local location = reference.location :: string
	local indexedDeclaration = index.by_location[location]
	if indexedDeclaration == nil then
		return {
			code = "unresolved_local_identity",
			node = reference,
			detail = `local source location {location} has no runtime declaration`,
		}
	end
	local declarationRecord = indexedDeclaration :: AstLocalBinding.Declaration
	local declaration = declarationRecord.value
	if declaration.name ~= reference.name then
		return {
			code = "inconsistent_local_identity",
			node = reference,
			detail = `local {reference.name} at {location} does not match its declaration {declaration.name}`,
		}
	end
	if not ownerIsVisible(functionParents, owned.function_owner, declarationRecord.function_owner) then
		return {
			code = "invalid_local_owner",
			node = reference,
			detail = `local source location {location} is not owned by this function or an ancestor`,
		}
	end
	if not scopeIsVisible(
			lexicalScopes,
			owned.lexical_scope,
			owned.lexical_position,
			declarationRecord.lexical_scope,
			declarationRecord.lexical_position
		)
	then
		return {
			code = "invalid_local_scope",
			node = reference,
			detail = `local source location {location} is not visible at this source position`,
		}
	end
	local resolvedDeclaration = AstLocalBinding.resolve(
		index,
		lexicalScopes,
		reference.name :: string,
		owned.lexical_scope,
		owned.lexical_position
	)
	if resolvedDeclaration == nil or resolvedDeclaration.value.location ~= location then
		return {
			code = "shadowed_local_identity",
			node = reference,
			detail = if resolvedDeclaration == nil
				then `local source location {location} is not the active lexical binding`
				else `local source location {location} is shadowed by {resolvedDeclaration.value.location}`,
		}
	end
	return nil
end

function AstLocalIdentity.validate(
	declarationRecords: { OwnedRecord },
	referenceRecords: { OwnedRecord },
	functionParents: { [number]: number },
	lexicalScopes: { [number]: LexicalScope }
): Problem?
	local index = AstLocalBinding.new()
	for _, owned in declarationRecords do
		local problem = indexRuntimeDeclarations(index, owned)
		if problem ~= nil then
			return problem
		end
	end
	local indexProblem = AstLocalBinding.normalize(index)
	if indexProblem ~= nil then
		return indexProblem
	end
	for _, owned in referenceRecords do
		local problem = validateRuntimeLocalReference(
			index,
			functionParents,
			lexicalScopes,
			owned
		)
		if problem ~= nil then
			return problem
		end
	end
	return nil
end

return table.freeze(AstLocalIdentity)
