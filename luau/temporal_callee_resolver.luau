--!strict

-- Resolves one direct local callee through bounded value snapshots. Temporal
-- definition selection stays with the host; this module owns only expression
-- wrappers, local identity, alias traversal, and cycle/depth rejection.

local TemporalCalleeResolver = {}
TemporalCalleeResolver.maxIdentityDepth = 64

type Record = { [string]: any }

export type DefinitionResolver = (Record, Record) -> Record?

local function unwrapExpression(value: any): Record?
	if type(value) ~= "table" then
		return nil
	end
	local expression = value :: Record
	local seen: { [any]: boolean } = {}
	while expression.type == "AstExprGroup"
		or expression.type == "AstExprTypeAssertion"
		or expression.type == "AstExprInstantiate"
	do
		if seen[expression] == true or type(expression.expr) ~= "table" then
			return nil
		end
		seen[expression] = true
		expression = expression.expr :: Record
	end
	return expression
end

local function directLocalLocation(expression: Record): string?
	local localNode = expression["local"]
	if expression.type ~= "AstExprLocal"
		or type(localNode) ~= "table"
		or (localNode :: Record).type ~= "AstLocal"
		or type((localNode :: Record).name) ~= "string"
		or (localNode :: Record).name == ""
		or type((localNode :: Record).location) ~= "string"
		or (localNode :: Record).location == ""
	then
		return nil
	end
	return (localNode :: Record).location :: string
end

function TemporalCalleeResolver.resolve(
	useNode: Record,
	value: any,
	resolveDefinition: DefinitionResolver
): Record?
	local expression = unwrapExpression(value)
	local seenLocations: { [string]: boolean } = {}
	local identityDepth = 0
	while expression ~= nil and expression.type == "AstExprLocal" do
		local location = directLocalLocation(expression)
		if location == nil
			or seenLocations[location :: string] == true
			or identityDepth >= TemporalCalleeResolver.maxIdentityDepth
		then
			return nil
		end
		seenLocations[location :: string] = true
		identityDepth += 1

		local definition = resolveDefinition(useNode, expression)
		if definition == nil then
			return nil
		end
		useNode = definition :: Record
		expression = unwrapExpression(definition)
	end
	return if expression ~= nil and expression.type == "AstExprFunction" then expression else nil
end

return table.freeze(TemporalCalleeResolver)
