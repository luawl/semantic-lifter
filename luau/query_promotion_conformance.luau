--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")

local LifterIR = require("./lifter_ir")

local function sameArray(left: { any }, right: { any }): boolean
	if #left ~= #right then
		return false
	end
	for index, value in left do
		if right[index] ~= value then
			return false
		end
	end
	return true
end

local function closureContains(program: any, root: number, target: number, seen: { [number]: boolean }?): boolean
	if root == target then
		return true
	end
	local visited = seen or {}
	if visited[root] then
		return false
	end
	visited[root] = true
	local operation = program.solver_terms[root + 1].operation
	local dependencies = {}
	if operation.value_definition ~= nil then
		table.insert(dependencies, operation.value_definition.expression)
		if operation.value_definition.valid_when ~= nil then
			table.insert(dependencies, operation.value_definition.valid_when)
		end
	elseif operation.binary ~= nil then
		table.insert(dependencies, operation.binary.left)
		table.insert(dependencies, operation.binary.right)
	elseif operation.logical_not ~= nil then
		table.insert(dependencies, operation.logical_not)
	elseif operation.is_nonzero ~= nil then
		table.insert(dependencies, operation.is_nonzero)
	elseif operation.division ~= nil then
		table.insert(dependencies, operation.division.left)
		table.insert(dependencies, operation.division.right)
		table.insert(dependencies, operation.division.defined_by)
	elseif operation.remainder ~= nil then
		table.insert(dependencies, operation.remainder.left)
		table.insert(dependencies, operation.remainder.right)
		table.insert(dependencies, operation.remainder.defined_by)
	end
	for _, dependency in dependencies do
		if closureContains(program, dependency, target, visited) then
			return true
		end
	end
	return false
end

local mode = process.args[1]
assert(mode ~= nil and mode ~= "", "expected an output path or audit mode")

if mode == "audit" then
	local rawPath = process.args[2]
	local resolvedPath = process.args[3]
	local reresolvedPath = process.args[4]
	local generatedPath = process.args[5]
	local expectedEngine = process.args[6]
	assert(
		rawPath ~= nil
			and resolvedPath ~= nil
			and reresolvedPath ~= nil
			and generatedPath ~= nil
			and expectedEngine ~= nil,
		"expected raw IR, resolved IR, re-resolved IR, generated Luau, and engine"
	)
	local raw: any = serde.decode("json", fs.readFile(rawPath))
	local resolvedEncoded = fs.readFile(resolvedPath)
	assert(resolvedEncoded == fs.readFile(reresolvedPath), "materialized query promotion IR is not byte-idempotent")
	local resolved: any = serde.decode("json", resolvedEncoded)
	assert(#raw.queries == 3 and #resolved.queries == 3, "query promotion changed stable query cardinality")
	assert(#raw.claims == 2 and #resolved.claims == 2, "query promotion changed stable claim cardinality")
	assert(#raw.obligations == 1 and #resolved.obligations == 1, "query promotion changed stable obligation cardinality")

	local remainderValue = nil
	local floorValue = nil
	local divisorValue = nil
	for _, value in raw.values do
		if value.name_hint == "remainder_result" then
			remainderValue = value.id
		elseif value.name_hint == "floor_result" then
			floorValue = value.id
		elseif value.name_hint == "divisor" then
			divisorValue = value.id
		end
	end
	assert(remainderValue ~= nil and floorValue ~= nil and divisorValue ~= nil, "query fixture values were not preserved")

	local rawRemainderTerm = nil
	local rawFloorTerm = nil
	local guardTerm = nil
	for _, term in raw.solver_terms do
		if term.operation.value == remainderValue then
			rawRemainderTerm = term
		elseif term.operation.value == floorValue then
			rawFloorTerm = term
		elseif term.operation.is_nonzero ~= nil then
			local operand = raw.solver_terms[term.operation.is_nonzero + 1]
			if operand.operation.value == divisorValue then
				guardTerm = term
			end
		end
		assert(term.operation.value_definition == nil, "frontend authored a value definition")
	end
	assert(rawRemainderTerm ~= nil and rawFloorTerm ~= nil and guardTerm ~= nil, "raw query terms are incomplete")

	local rawPromotedQuery = raw.queries[1]
	local resolvedPromotedQuery = resolved.queries[1]
	assert(rawPromotedQuery.id == 0 and resolvedPromotedQuery.id == 0, "eligible query ID was replaced")
	assert(rawPromotedQuery.goal ~= resolvedPromotedQuery.goal, "eligible query goal was not normalized")
	assert(
		sameArray(rawPromotedQuery.assumptions, resolvedPromotedQuery.assumptions)
			and sameArray(rawPromotedQuery.path_rewrites, resolvedPromotedQuery.path_rewrites),
		"query promotion changed assumptions or path authority"
	)
	assert(#resolvedPromotedQuery.assumptions == 1 and resolvedPromotedQuery.assumptions[1] == 0, "exact guard assumption was not retained")
	assert(closureContains(raw, rawPromotedQuery.goal, rawRemainderTerm.id), "raw query does not contain the intended value leaf")

	local remainderDefinition = nil
	for _, term in resolved.solver_terms do
		local definition = term.operation.value_definition
		if definition ~= nil and definition.value == remainderValue then
			remainderDefinition = term
		end
	end
	assert(remainderDefinition ~= nil, "Zig did not promote the raw modulo value")
	assert(
		closureContains(resolved, resolvedPromotedQuery.goal, remainderDefinition.id),
		"normalized query does not use the promoted modulo definition"
	)
	assert(
		not closureContains(resolved, resolvedPromotedQuery.goal, rawRemainderTerm.id),
		"normalized query retained the raw modulo leaf"
	)
	local remainderExpression = resolved.solver_terms[remainderDefinition.operation.value_definition.expression + 1]
	assert(remainderExpression.operation.remainder ~= nil, "promoted modulo definition changed operation kind")
	assert(
		remainderExpression.operation.remainder.defined_by == guardTerm.id,
		"promoted modulo definition did not adopt the exact admitted guard"
	)

	local promotedClaim = resolved.claims[1]
	assert(promotedClaim.query == 0 and promotedClaim.predicate == resolvedPromotedQuery.goal, "claim predicate was not normalized with its query")
	assert(promotedClaim.status == "proved" and promotedClaim.certificate ~= nil, "normalized required claim was not proved")
	local promotedCertificate = resolved.certificates[promotedClaim.certificate + 1]
	assert(promotedCertificate.query == 0 and promotedCertificate.resolution == "proved", "normalized query certificate is invalid")
	assert(promotedCertificate.engine == expectedEngine, "normalized query used the wrong solver engine")

	local rawMaterializedQuery = raw.queries[2]
	local resolvedMaterializedQuery = resolved.queries[2]
	assert(rawMaterializedQuery.id == 1 and resolvedMaterializedQuery.id == 1, "materialized query ID changed")
	assert(rawMaterializedQuery.goal == resolvedMaterializedQuery.goal, "materialized query goal was rewritten")
	assert(
		sameArray(rawMaterializedQuery.assumptions, resolvedMaterializedQuery.assumptions)
			and sameArray(rawMaterializedQuery.path_rewrites, resolvedMaterializedQuery.path_rewrites),
		"materialized query authority changed"
	)
	assert(closureContains(resolved, resolvedMaterializedQuery.goal, rawFloorTerm.id), "materialized query lost its raw value leaf")
	local rawCertificate = raw.certificates[1]
	local resolvedCertificate = resolved.certificates[1]
	assert(
		resolvedCertificate.id == rawCertificate.id
			and resolvedCertificate.query == rawCertificate.query
			and resolvedCertificate.engine == rawCertificate.engine
			and resolvedCertificate.resolution == rawCertificate.resolution
			and resolvedCertificate.certificate_digest == rawCertificate.certificate_digest,
		"materialized certificate changed during unrelated query promotion"
	)
	local materializedClaim = resolved.claims[2]
	assert(
		materializedClaim.query == 1
			and materializedClaim.predicate == raw.claims[2].predicate
			and materializedClaim.status == "proved"
			and materializedClaim.certificate == 0,
		"materialized claim changed during unrelated query promotion"
	)

	local rawModelQuery = raw.queries[3]
	local resolvedModelQuery = resolved.queries[3]
	assert(rawModelQuery.id == 2 and resolvedModelQuery.id == 2, "model query ID was replaced")
	assert(rawModelQuery.goal ~= resolvedModelQuery.goal, "model query goal was not normalized")
	assert(resolvedModelQuery.goal == resolvedPromotedQuery.goal, "equivalent promoted queries did not reuse a canonical goal")
	assert(
		sameArray(rawModelQuery.assumptions, resolvedModelQuery.assumptions)
			and sameArray(rawModelQuery.path_rewrites, resolvedModelQuery.path_rewrites),
		"model query promotion changed assumptions or path authority"
	)
	local modelObligation = resolved.obligations[1]
	assert(modelObligation.query == 2 and modelObligation.status == "discharged", "model-only obligation was not discharged")
	assert(
		modelObligation.requirement.kind == "find_model"
			and modelObligation.requirement.predicate == resolvedModelQuery.goal,
		"model obligation requirement was not normalized with its query"
	)
	assert(modelObligation.certificate ~= nil, "model-only obligation has no certificate")
	local modelCertificate = resolved.certificates[modelObligation.certificate + 1]
	assert(modelCertificate.query == 2 and modelCertificate.resolution == "proved", "model query certificate is invalid")
	assert(modelCertificate.engine == expectedEngine, "model query used the wrong solver engine")
	assert(modelCertificate.model ~= nil and modelCertificate.unsat_core == nil, "model query produced the wrong artifact kind")
	local model = resolved.solver_models[modelCertificate.model + 1]
	assert(model.query == 2, "model artifact is bound to the wrong query")

	local generated = fs.readFile(generatedPath)
	assert(string.find(generated, "%", 1, true) ~= nil, "live modulo operation disappeared from generated Luau")
	assert(string.find(generated, "__lifter", 1, true) == nil, "query promotion emitted a backend helper placeholder")
	return
end

local outputPath = mode
local builder = LifterIR.Builder.new("generic-unresolved-query-promotion")
local proof = builder:addEvidence("dynamic_fixture", "fixture:generic-unresolved-query-promotion")
local evidence = { proof }
local pure = LifterIR.Effects.pure()
local integer = LifterIR.Types.integer()
local integerSort = LifterIR.SolverSort.integer()
local booleanSort = LifterIR.SolverSort.boolean()

local chunk = builder:reserveFunction({ name_hint = "chunk", evidence = evidence })
local probe = builder:reserveFunction({ name_hint = "query_probe", evidence = evidence })
local chunkBlock = builder:reserveBlock(chunk, { evidence = evidence })
local probeBlock = builder:reserveBlock(probe, { evidence = evidence })
builder:setEntryFunction(chunk)
builder:setFunctionEntry(chunk, chunkBlock)
builder:setFunctionEntry(probe, probeBlock)

local _, exportedResults = builder:addInstruction(
	chunkBlock,
	LifterIR.Operation.functionRef(probe),
	{ { type = LifterIR.Types.functionValue(), name_hint = "exported" } },
	{ effects = pure, evidence = evidence }
)

local function addInteger(value: string, nameHint: string): number
	local _, results = builder:addInstruction(
		probeBlock,
		LifterIR.Operation.constant(LifterIR.Literal.integer(value)),
		{ { type = integer, name_hint = nameHint } },
		{ effects = pure, evidence = evidence }
	)
	return results[1]
end

local dividend = addInteger("7", "dividend")
local divisor = addInteger("3", "divisor")
local _, floorResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("floor_divide", dividend, divisor),
	{ { type = integer, name_hint = "floor_result" } },
	{ effects = pure, evidence = evidence }
)
local _, remainderResults = builder:addInstruction(
	probeBlock,
	LifterIR.Operation.binary("modulo", dividend, divisor),
	{ { type = integer, name_hint = "remainder_result" } },
	{ effects = pure, evidence = evidence }
)

local divisorTerm = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.value(divisor))
local nonzeroGuard = builder:addSolverTerm(booleanSort, LifterIR.SolverTerm.isNonzero(divisorTerm))
local guardConstraint = builder:addConstraint(nonzeroGuard, evidence)

local rawRemainder = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.value(remainderResults[1]))
local two = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral("2"))
local nestedSum = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.binary("add", rawRemainder, two))
local three = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.integerLiteral("3"))
local promotedGoal = builder:addSolverTerm(booleanSort, LifterIR.SolverTerm.binary("equal", nestedSum, three))
local promotedQuery = builder:addQuery("prove_true", { guardConstraint }, promotedGoal)
builder:addClaim(
	LifterIR.Entity.program(),
	promotedGoal,
	"unproven",
	true,
	evidence,
	nil,
	nil,
	promotedQuery
)

local rawFloor = builder:addSolverTerm(integerSort, LifterIR.SolverTerm.value(floorResults[1]))
local materializedGoal = builder:addSolverTerm(booleanSort, LifterIR.SolverTerm.binary("equal", rawFloor, rawFloor))
local materializedQuery = builder:addQuery("prove_true", { guardConstraint }, materializedGoal)
local materializedCertificate = builder:addCertificate(
	materializedQuery,
	"imported",
	"proved",
	evidence,
	"fixture:generic-unresolved-query-promotion:materialized-v1"
)
builder:addClaim(
	LifterIR.Entity.program(),
	materializedGoal,
	"proved",
	false,
	evidence,
	materializedCertificate,
	nil,
	materializedQuery
)

local modelQuery = builder:addQuery("find_model", { guardConstraint }, promotedGoal)
builder:addObligation(
	"numeric_domain",
	LifterIR.Entity.program(),
	"open",
	"readable_luau",
	"materialize a model for the normalized modulo identity",
	modelQuery,
	nil,
	evidence
)

builder:finalizeBlock(chunkBlock, LifterIR.Terminator.returnValues({ exportedResults[1] }))
builder:finalizeBlock(probeBlock, LifterIR.Terminator.returnValues({ remainderResults[1] }))
builder:finalizeFunction(chunk)
builder:finalizeFunction(probe)

local encoded = LifterIR.encodeJson(builder:finish(), true)
local decoded: any = serde.decode("json", encoded)
assert(#decoded.solver_terms == 9, "query frontend authored an unexpected solver surface")
assert(
	#decoded.constraints == 1
		and #decoded.queries == 3
		and #decoded.certificates == 1
		and #decoded.obligations == 1,
	"query fixture proof surface is incomplete"
)
for _, term in decoded.solver_terms do
	assert(term.operation.value_definition == nil, "query frontend unexpectedly authored a value definition")
end
fs.writeFile(outputPath, encoded .. "\n")
