--!strict

-- Deterministic nearest-binding index for validated runtime-local declarations.

local AstLocalBinding = {}

type Record = { [string]: any }

export type Problem = {
	code: string,
	node: Record?,
	detail: string,
}

export type Scope = {
	parent: number,
	entry_position: number,
}

export type Declaration = {
	value: Record,
	function_owner: number,
	lexical_scope: number,
	lexical_position: number,
	lexical_rank: number,
}

export type Index = {
	by_location: { [string]: Declaration },
	by_name: { [string]: { [number]: { Declaration } } },
}

function AstLocalBinding.new(): Index
	return { by_location = {}, by_name = {} }
end

function AstLocalBinding.add(index: Index, declaration: Declaration): Problem?
	local node = declaration.value
	local location = node.location :: string
	if index.by_location[location] ~= nil then
		return {
			code = "duplicate_local_identity",
			node = node,
			detail = `local source location {location} belongs to more than one runtime declaration`,
		}
	end
	index.by_location[location] = declaration
	local scopes = index.by_name[node.name]
	if scopes == nil then
		scopes = {}
		index.by_name[node.name] = scopes
	end
	local declarations = (scopes :: { [number]: { Declaration } })[declaration.lexical_scope]
	if declarations == nil then
		declarations = {}
		(scopes :: { [number]: { Declaration } })[declaration.lexical_scope] = declarations
	end
	table.insert(declarations :: { Declaration }, declaration)
	return nil
end

function AstLocalBinding.normalize(index: Index): Problem?
	for _, scopes in index.by_name do
		for _, declarations in scopes do
			table.sort(declarations, function(left: Declaration, right: Declaration): boolean
				if left.lexical_position ~= right.lexical_position then
					return left.lexical_position < right.lexical_position
				end
				return left.lexical_rank < right.lexical_rank
			end)
			for declarationIndex = 2, #declarations do
				local previous = declarations[declarationIndex - 1]
				local current = declarations[declarationIndex]
				if previous.lexical_position == current.lexical_position and previous.lexical_rank == current.lexical_rank then
					return {
						code = "ambiguous_local_binding",
						node = current.value,
						detail = `local {current.value.name} has more than one declaration at the same lexical position`,
					}
				end
			end
		end
	end
	return nil
end

local function latestActive(declarations: { Declaration }, position: number): Declaration?
	local low = 1
	local high = #declarations
	local result: Declaration? = nil
	while low <= high do
		local middle = math.floor((low + high) / 2)
		local candidate = declarations[middle]
		if candidate.lexical_position <= position then
			result = candidate
			low = middle + 1
		else
			high = middle - 1
		end
	end
	return result
end

function AstLocalBinding.resolve(
	index: Index,
	lexicalScopes: { [number]: Scope },
	name: string,
	referenceScope: number,
	referencePosition: number
): Declaration?
	local scopes = index.by_name[name]
	if scopes == nil then
		return nil
	end
	local scope = referenceScope
	local position = referencePosition
	while true do
		local declarations = scopes[scope]
		if declarations ~= nil then
			local active = latestActive(declarations, position)
			if active ~= nil then
				return active
			end
		end
		if scope == 0 then
			return nil
		end
		local link = lexicalScopes[scope]
		if link == nil then
			return nil
		end
		position = link.entry_position
		scope = link.parent
	end
end

return table.freeze(AstLocalBinding)
