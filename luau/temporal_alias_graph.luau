--!strict

-- Resolves bounded transparent-local alias graphs. Source indexing and
-- reaching-definition policy stay with the temporal identity owner.

local TargetOriginReturnSelector = require("./target_origin_return_selector")

local TemporalAliasGraph = {}

type Record = { [string]: any }

export type Definition = { [string]: any }

export type Reaching = {
	definitions: { Definition },
	path_conditional: boolean,
}

export type Host = {
	max_depth: number,
	max_candidates: number,
	matches_origin: (Record, number, Record) -> boolean,
	reaching: (Record, Record, string) -> Reaching,
}

export type Root = {
	value: Record,
	result_ordinal: number,
	anchor: Definition,
	seen_location: string,
}

export type Match = {
	depth: number,
	anchor: Definition,
}

export type RootResult = {
	result: Match?,
}

type Budget = {
	expanded: number,
}

local function declarationLocation(value: any, label: string): string
	assert(type(value) == "table" and value.type == "AstLocal", `{label} must be an AST local declaration`)
	local location = value.location
	assert(type(location) == "string" and location ~= "", `{label} must have a source location`)
	return location
end

local function transparentExpression(value: any): Record?
	if type(value) ~= "table" then
		return nil
	end
	local expression = value :: Record
	while expression.type == "AstExprGroup"
		or expression.type == "AstExprTypeAssertion"
		or expression.type == "AstExprInstantiate"
	do
		if type(expression.expr) ~= "table" then
			return nil
		end
		expression = expression.expr :: Record
	end
	return expression
end

local function transparentLocalReference(value: any): (Record?, Record?, string?)
	local expression = transparentExpression(value)
	if expression == nil then
		return nil, nil, nil
	end
	if expression.type ~= "AstExprLocal" or type(expression["local"]) ~= "table" then
		return nil, nil, nil
	end
	local declaration = expression["local"] :: Record
	return declaration, expression, declarationLocation(declaration, "temporal target alias")
end

local function consumeCandidate(host: Host, budget: Budget)
	budget.expanded += 1
	assert(budget.expanded <= host.max_candidates, "temporal target alias candidate expansion exceeds the limit")
end

local function extendPath(seen: { [string]: boolean }, location: string): { [string]: boolean }
	assert(seen[location] ~= true, `temporal target alias chain contains a cycle at {location}`)
	local extended: { [string]: boolean } = {}
	for priorLocation in seen do
		extended[priorLocation] = true
	end
	extended[location] = true
	return extended
end

local function merge(current: Match?, candidate: Match, mismatch: string): Match
	if current == nil then
		return candidate
	end
	local prior = current :: Match
	assert(prior.anchor == candidate.anchor, mismatch)
	return {
		depth = math.max(prior.depth, candidate.depth),
		anchor = prior.anchor,
	}
end

local canonicalDefinition: (Host, Definition, { [string]: boolean }, number, Budget) -> Match
local matchValue: (Host, Record, number, Record, { [string]: boolean }, number, Definition, Budget) -> Match?

local function definitionResultOrdinal(definition: Definition): number
	local ordinal = definition.resultOrdinal
	return if type(ordinal) == "number" and ordinal >= 1 and ordinal % 1 == 0 then ordinal else 1
end

canonicalDefinition = function(
	host: Host,
	definition: Definition,
	seen: { [string]: boolean },
	depth: number,
	budget: Budget
): Match
	local value = definition.expression
	if value == nil then
		return { depth = depth, anchor = definition }
	end
	if definitionResultOrdinal(definition) ~= 1 then
		return { depth = depth, anchor = definition }
	end
	local declaration, expression, location = transparentLocalReference(value)
	if declaration == nil or expression == nil or location == nil then
		return { depth = depth, anchor = definition }
	end
	assert(depth < host.max_depth, "temporal target alias chain exceeds the depth limit")
	local extended = extendPath(seen, location)
	local reaching = host.reaching(expression :: Record, declaration :: Record, "temporal alias anchor")
	local common: Match? = nil
	for _, candidate in reaching.definitions do
		consumeCandidate(host, budget)
		common = merge(
			common,
			canonicalDefinition(host, candidate, extended, depth + 1, budget),
			`temporal alias anchor {location} does not share one stable identity`
		)
	end
	assert(common ~= nil)
	return common :: Match
end

matchValue = function(
	host: Host,
	value: Record,
	resultOrdinal: number,
	origin: Record,
	seen: { [string]: boolean },
	depth: number,
	anchor: Definition,
	budget: Budget
): Match?
	if host.matches_origin(value, resultOrdinal, origin) then
		if resultOrdinal == 1 and (origin.kind == "local_value" or origin.kind == "local_place") then
			local declaration, expression, location = transparentLocalReference(value)
			if declaration ~= nil and expression ~= nil and location ~= nil then
				local reaching = host.reaching(expression :: Record, declaration :: Record, "temporal alias anchor")
				if reaching.path_conditional then
					local extended = extendPath(seen, location)
					local common: Match? = nil
					for _, candidate in reaching.definitions do
						consumeCandidate(host, budget)
						common = merge(
							common,
							canonicalDefinition(host, candidate, extended, depth, budget),
							`temporal alias anchor {location} does not share one stable identity`
						)
					end
					assert(common ~= nil)
					return common :: Match
				end
				anchor = reaching.definitions[1]
				assert(anchor ~= nil)
			end
		end
		return { depth = depth, anchor = anchor }
	end

	assert(depth < host.max_depth, "temporal target alias chain exceeds the depth limit")
	if resultOrdinal ~= 1 then
		return nil
	end
	local transparent = transparentExpression(value)
	if transparent ~= nil and transparent.type == "AstExprIfElse" then
		local selected = TargetOriginReturnSelector.selectedConditionalExpression(transparent, nil)
		if selected == nil then
			return nil
		end
		if selected ~= transparent then
			consumeCandidate(host, budget)
			return matchValue(
				host,
				selected :: Record,
				1,
				origin,
				seen,
				depth + 1,
				anchor,
				budget
			)
		end
		consumeCandidate(host, budget)
		local trueMatch = matchValue(
			host,
			transparent.trueExpr :: Record,
			1,
			origin,
			seen,
			depth + 1,
			anchor,
			budget
		)
		if trueMatch == nil then
			return nil
		end
		consumeCandidate(host, budget)
		local falseMatch = matchValue(
			host,
			transparent.falseExpr :: Record,
			1,
			origin,
			seen,
			depth + 1,
			anchor,
			budget
		)
		if falseMatch == nil then
			return nil
		end
		return merge(
			trueMatch :: Match,
			falseMatch :: Match,
			"temporal conditional alias does not share one stable authenticated identity"
		)
	end
	local declaration, expression, location = transparentLocalReference(value)
	if declaration == nil or expression == nil or location == nil then
		return nil
	end
	local extended = extendPath(seen, location)
	local reaching = host.reaching(expression :: Record, declaration :: Record, "temporal alias")
	local common: Match? = nil
	for _, definition in reaching.definitions do
		consumeCandidate(host, budget)
		local definitionExpression = definition.expression
		local matched = if definitionExpression == nil
			then nil
			else matchValue(
				host,
				definitionExpression :: Record,
				definitionResultOrdinal(definition),
				origin,
				extended,
				depth + 1,
				definition,
				budget
			)
		if matched == nil then
			if reaching.path_conditional then
				assert(false, `temporal alias place {location} has an unauthenticated feasible definition`)
			end
			return nil
		end
		common = merge(
			common,
			matched :: Match,
			`temporal alias place {location} does not share one stable authenticated identity`
		)
	end
	return common
end

function TemporalAliasGraph.resolve(host: Host, roots: { Root }, origin: Record): { RootResult }
	local budget: Budget = { expanded = 0 }
	local results: { RootResult } = {}
	for _, root in roots do
		consumeCandidate(host, budget)
		table.insert(results, {
			result = matchValue(
				host,
				root.value,
				root.result_ordinal,
				origin,
				{ [root.seen_location] = true },
				0,
				root.anchor,
				budget
			),
		})
	end
	return results
end

return table.freeze(TemporalAliasGraph)
