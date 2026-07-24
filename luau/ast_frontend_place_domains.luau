--!strict

-- Finalizes lexical place domains after the complete source program is known.
-- Closure bindings make captured-place alias classes explicit, so each class
-- is refined only when all of its writes agree on one concrete domain.

local OperatorDomains = require("./ast_frontend_operator_domains")
local LifterIR = require("./lifter_ir")

local PlaceDomains = {}

type Record = { [string]: any }

type Candidate = {
	value_type: Record?,
	writes: { Record },
	blocked: boolean,
	fixed: boolean,
}

type InferenceCache = {
	types: { [number]: Record },
	unresolved: { [number]: boolean },
	visiting: { [number]: boolean },
}

local function sameType(left: Record, right: Record): boolean
	return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed
end

local function copyType(valueType: Record): Record
	return {
		kind = valueType.kind,
		bit_width = valueType.bit_width,
		signed = valueType.signed,
	}
end

local function isNumeric(valueType: Record): boolean
	return valueType.kind == "integer" or valueType.kind == "number"
end

local function commonStorageType(left: Record, right: Record): Record?
	if sameType(left, right) then
		return copyType(left)
	elseif isNumeric(left) and isNumeric(right) then
		return LifterIR.Types.number()
	end
	return nil
end

local function storageAccepts(target: Record, source: Record): boolean
	local joined = commonStorageType(target, source)
	return joined ~= nil and sameType(joined, target)
end

local function findRoot(parents: { number }, placeId: number): number
	local root = placeId
	while parents[root + 1] ~= root do
		root = parents[root + 1]
	end
	local current = placeId
	while current ~= root do
		local parent = parents[current + 1]
		parents[current + 1] = root
		current = parent
	end
	return root
end

local function unionPlaces(parents: { number }, left: number, right: number)
	local leftRoot = findRoot(parents, left)
	local rightRoot = findRoot(parents, right)
	if leftRoot == rightRoot then
		return
	end
	if leftRoot < rightRoot then
		parents[rightRoot + 1] = leftRoot
	else
		parents[leftRoot + 1] = rightRoot
	end
end

local function buildAliasGraph(program: Record): ({ number }, { [number]: boolean })
	local parents = {}
	for _, place in program.places do
		assert(place.id == #parents, `place table is not dense at {place.id}`)
		table.insert(parents, place.id)
	end

	local mappedCaptures: { [number]: boolean } = {}
	for _, instruction in program.instructions do
		local closure = instruction.operation.make_closure
		if closure ~= nil then
			local target = program.functions[closure["function"] + 1]
			assert(target ~= nil and target.id == closure["function"], `closure targets missing function {closure["function"]}`)
			assert(#target.captures == #closure.bindings, `closure {instruction.id} has inconsistent capture arity`)
			for index, captureId in target.captures do
				local capture = program.captures[captureId + 1]
				assert(capture ~= nil and capture.id == captureId, `function {target.id} names missing capture {captureId}`)
				local capturedPlace = capture.kind.shared_place
				if capturedPlace ~= nil then
					local boundPlace = closure.bindings[index].place
					assert(boundPlace ~= nil, `closure {instruction.id} binds shared capture {captureId} as a value`)
					unionPlaces(parents, capturedPlace, boundPlace)
					mappedCaptures[captureId] = true
				end
			end
		end
	end
	return parents, mappedCaptures
end

local function mergePlaceType(candidate: Candidate, valueType: Record)
	if candidate.value_type == nil then
		candidate.value_type = copyType(valueType)
	elseif not sameType(candidate.value_type, valueType) then
		candidate.blocked = true
	end
	candidate.fixed = true
end

local function mergeWriteSeed(candidate: Candidate, valueType: Record)
	if valueType.kind == "dynamic" then
		return
	end
	if candidate.value_type == nil then
		candidate.value_type = copyType(valueType)
	elseif candidate.fixed then
		if not storageAccepts(candidate.value_type, valueType) then
			candidate.blocked = true
		end
	else
		local joined = commonStorageType(candidate.value_type, valueType)
		if joined == nil then
			candidate.blocked = true
		else
			candidate.value_type = joined
		end
	end
end

local function inferValueType(
	program: Record,
	parents: { number },
	classRoot: number,
	assumedType: Record,
	valueId: number,
	cache: InferenceCache
): Record?
	local value = program.values[valueId + 1]
	assert(value ~= nil and value.id == valueId, `domain inference names missing value {valueId}`)
	if value.type.kind ~= "dynamic" then
		return value.type
	end
	if cache.types[valueId] ~= nil then
		return cache.types[valueId]
	elseif cache.unresolved[valueId] == true or cache.visiting[valueId] == true then
		return nil
	end

	cache.visiting[valueId] = true
	local inferred: Record? = nil
	local origin = value.origin.instruction_result
	if origin ~= nil then
		local instruction = program.instructions[origin.instruction + 1]
		assert(
			instruction ~= nil and instruction.id == origin.instruction,
			`value {valueId} names missing instruction {origin.instruction}`
		)
		local placeId = instruction.operation.place_read
		local copySource = instruction.operation.copy
		local unary = instruction.operation.unary
		local binary = instruction.operation.binary
		if placeId ~= nil then
			local place = program.places[placeId + 1]
			assert(place ~= nil and place.id == placeId, `place read {instruction.id} names missing place {placeId}`)
			if findRoot(parents, placeId) == classRoot then
				inferred = assumedType
			elseif place.type.kind ~= "dynamic" then
				inferred = place.type
			end
		elseif copySource ~= nil then
			inferred = inferValueType(program, parents, classRoot, assumedType, copySource, cache)
		elseif unary ~= nil and unary.mode == "semantic" then
			local operandType = inferValueType(program, parents, classRoot, assumedType, unary.operand, cache)
			if operandType ~= nil then
				local resultType, staticDomain = OperatorDomains.unary(unary.operator, operandType)
				if staticDomain then
					inferred = resultType
				end
			end
		elseif binary ~= nil and binary.mode == "semantic" then
			local leftType = inferValueType(program, parents, classRoot, assumedType, binary.left, cache)
			local rightType = inferValueType(program, parents, classRoot, assumedType, binary.right, cache)
			if leftType ~= nil and rightType ~= nil then
				local resultType, staticDomain = OperatorDomains.binary(binary.operator, leftType, rightType)
				if staticDomain then
					inferred = resultType
				end
			end
		end
	end

	cache.visiting[valueId] = nil
	if inferred == nil then
		cache.unresolved[valueId] = true
	else
		cache.types[valueId] = inferred
	end
	return inferred
end

local function solveCandidate(program: Record, parents: { number }, root: number, candidate: Candidate): Record?
	local seed = candidate.value_type
	if candidate.blocked or #candidate.writes == 0 or seed == nil then
		return nil
	end
	local assumedType = copyType(seed)
	while true do
		local cache: InferenceCache = { types = {}, unresolved = {}, visiting = {} }
		local nextType = assumedType
		for _, instruction in candidate.writes do
			local write = instruction.operation.place_write
			assert(write ~= nil, `place candidate contains non-write instruction {instruction.id}`)
			local writeType = inferValueType(program, parents, root, assumedType, write.value, cache)
			if writeType == nil then
				return nil
			elseif candidate.fixed then
				if not storageAccepts(assumedType, writeType) then
					return nil
				end
			else
				local joined = commonStorageType(nextType, writeType)
				if joined == nil then
					return nil
				end
				nextType = joined
			end
		end
		if candidate.fixed or sameType(nextType, assumedType) then
			return assumedType
		end
		assumedType = nextType
	end
end

function PlaceDomains.refine(program: Record): number
	local parents, mappedCaptures = buildAliasGraph(program)
	local candidates: { [number]: Candidate } = {}
	for _, place in program.places do
		local root = findRoot(parents, place.id)
		local candidate = candidates[root]
		if candidate == nil then
			candidate = { value_type = nil, writes = {}, blocked = false, fixed = false }
			candidates[root] = candidate
		end
		if place.type.kind ~= "dynamic" then
			mergePlaceType(candidate, place.type)
		end
		local captureId = place.origin.capture
		if captureId ~= nil then
			local capture = program.captures[captureId + 1]
			assert(
				capture ~= nil
					and capture.id == captureId
					and capture["function"] == place["function"]
					and capture.kind.shared_place == place.id,
				`place {place.id} has an inconsistent capture origin`
			)
			if capture["function"] == program.entry_function or mappedCaptures[captureId] ~= true then
				candidate.blocked = true
			end
		end
	end

	for _, instruction in program.instructions do
		local write = instruction.operation.place_write
		if write ~= nil then
			local candidate = candidates[findRoot(parents, write.place)]
			assert(candidate ~= nil, `place write {instruction.id} names missing place {write.place}`)
			table.insert(candidate.writes, instruction)
			mergeWriteSeed(candidate, program.values[write.value + 1].type)
		end
	end

	local inferredTypes: { [number]: Record } = {}
	for root, candidate in candidates do
		local inferred = solveCandidate(program, parents, root, candidate)
		if inferred ~= nil then
			inferredTypes[root] = inferred
		end
	end

	local refinedCount = 0
	for _, place in program.places do
		local valueType = inferredTypes[findRoot(parents, place.id)]
		if valueType ~= nil then
			if place.type.kind == "dynamic" then
				place.type = copyType(valueType)
				refinedCount += 1
			else
				assert(sameType(place.type, valueType), `place {place.id} has a conflicting concrete type`)
			end
		end
	end

	for _, instruction in program.instructions do
		local placeId = instruction.operation.place_read
		local valueType = if placeId ~= nil then program.places[placeId + 1].type else nil
		if valueType ~= nil and valueType.kind ~= "dynamic" then
			assert(#instruction.results == 1, `place read {instruction.id} does not have one result`)
			local result = program.values[instruction.results[1] + 1]
			assert(result.type.kind == "dynamic" or sameType(result.type, valueType), `place read {instruction.id} has a conflicting result type`)
			if result.type.kind == "dynamic" then
				result.type = copyType(valueType)
				refinedCount += 1
			end
		end
	end

	return refinedCount
end

return table.freeze(PlaceDomains)
