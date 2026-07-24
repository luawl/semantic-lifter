--!strict

-- Shared semantic domains for source operators. Lowering, place inference,
-- and whole-program refinement all consume this one authority.

local LifterIR = require("./lifter_ir")

local OperatorDomains = {}

type Record = { [string]: any }

local comparisonOperators: { [string]: boolean } = {
	equal = true,
	not_equal = true,
	less = true,
	less_equal = true,
	greater = true,
	greater_equal = true,
}

local primitiveEqualityKinds: { [string]: boolean } = {
	nil_value = true,
	boolean = true,
	integer = true,
	number = true,
	string = true,
	["function"] = true,
	thread = true,
}

local numericBinaryOperators: { [string]: boolean } = {
	add = true,
	subtract = true,
	multiply = true,
	divide = true,
	floor_divide = true,
	modulo = true,
	power = true,
}

local orderedComparisonOperators: { [string]: boolean } = {
	less = true,
	less_equal = true,
	greater = true,
	greater_equal = true,
}

local function isNumeric(valueType: Record): boolean
	return valueType.kind == "integer" or valueType.kind == "number"
end

local function isStringConvertible(valueType: Record): boolean
	return valueType.kind == "string" or isNumeric(valueType)
end

local function hasStaticBinaryDomain(operatorName: string, leftType: Record, rightType: Record): boolean
	if numericBinaryOperators[operatorName] then
		return isNumeric(leftType) and isNumeric(rightType)
	elseif operatorName == "concat" then
		return isStringConvertible(leftType) and isStringConvertible(rightType)
	elseif operatorName == "equal" or operatorName == "not_equal" then
		return primitiveEqualityKinds[leftType.kind] == true and primitiveEqualityKinds[rightType.kind] == true
	elseif orderedComparisonOperators[operatorName] then
		return (isNumeric(leftType) and isNumeric(rightType))
			or (leftType.kind == "string" and rightType.kind == "string")
	end
	return false
end

function OperatorDomains.binary(operatorName: string, leftType: Record, rightType: Record): (Record, boolean)
	local staticDomain = hasStaticBinaryDomain(operatorName, leftType, rightType)
	if comparisonOperators[operatorName] then
		return LifterIR.Types.boolean(), staticDomain
	elseif not staticDomain then
		return LifterIR.Types.dynamic(), false
	elseif operatorName == "concat" then
		return LifterIR.Types.string(), true
	end
	return LifterIR.Types.number(), true
end

function OperatorDomains.unary(operatorName: string, operandType: Record): (Record, boolean)
	if operatorName == "logical_not" then
		return LifterIR.Types.boolean(), true
	elseif operatorName == "negate" and isNumeric(operandType) then
		return LifterIR.Types.number(), true
	elseif operatorName == "length" and operandType.kind == "string" then
		return LifterIR.Types.integer(), true
	end
	return LifterIR.Types.dynamic(), false
end

local function sameType(left: Record, right: Record): boolean
	return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed
end

local function hasExactPureEffects(effects: Record): boolean
	return effects.precision == "exact"
		and not effects.reads_memory
		and not effects.writes_memory
		and not effects.may_throw
		and not effects.may_yield
		and not effects.invokes_unknown_code
end

function OperatorDomains.refine(program: Record): number
	local totalRefined = 0
	while true do
		local passRefined = 0
		for _, instruction in program.instructions do
			local resultType: Record? = nil
			local staticDomain = false
			local binary = instruction.operation.binary
			local unary = instruction.operation.unary
			if binary ~= nil and binary.mode == "semantic" then
				resultType, staticDomain = OperatorDomains.binary(
					binary.operator,
					program.values[binary.left + 1].type,
					program.values[binary.right + 1].type
				)
			elseif unary ~= nil and unary.mode == "semantic" then
				resultType, staticDomain = OperatorDomains.unary(unary.operator, program.values[unary.operand + 1].type)
			end
			if staticDomain and resultType ~= nil then
				assert(#instruction.results == 1, `static operator {instruction.id} does not have one result`)
				local result = program.values[instruction.results[1] + 1]
				local changed = false
				if result.type.kind == "dynamic" then
					result.type = resultType
					changed = true
				else
					assert(sameType(result.type, resultType), `static operator {instruction.id} has a conflicting result type`)
				end
				if not hasExactPureEffects(instruction.effects) then
					instruction.effects = LifterIR.Effects.pure()
					changed = true
				end
				if changed then
					passRefined += 1
				end
			end
		end
		if passRefined == 0 then
			return totalRefined
		end
		totalRefined += passRefined
	end
end

return table.freeze(OperatorDomains)
