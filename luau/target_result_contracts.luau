--!strict

-- Matches authenticated opaque-call result ordinals against existing AST
-- expressions. Sessions keep provenance local to one promoted target, while
-- the owner rejects contracts that never participate in a verified identity.

local AstAdmission = require("./ast_admission")
local InvocationFrame = require("./invocation_frame")
local TargetProofBundle = require("./target_proof_bundle")

local TargetResultContracts = {}
TargetResultContracts.maxResultOrdinal = TargetProofBundle.maxResultOrdinal

type Record = { [string]: any }

export type Evidence = {
	kind: string,
	locator: string,
	digest: string?,
}

export type Contract = {
	producer_call_location: string,
	result_ordinal: number,
	origin: any,
	evidence: Evidence,
	proof: {
		content: string,
		evidence: Evidence,
	},
}

type IndexedContract = {
	call: Record,
	originKey: string,
	evidence: Evidence,
	proofEvidence: Evidence,
	index: number,
}

export type Matcher = {
	contracts: { IndexedContract },
	byKey: { [string]: IndexedContract },
	used: { [number]: boolean },
	begin: (self: Matcher, origin: any) -> Session,
	assertFullyUsed: (self: Matcher, label: string) -> (),
}

export type Session = {
	matcher: Matcher,
	originKey: string,
	matched: { [number]: boolean },
	committed: boolean,
	matches: (self: Session, value: any, resultOrdinal: number, origin: Record) -> boolean,
	commit: (self: Session) -> { Evidence },
}

local MatcherMethods = {}
MatcherMethods.__index = MatcherMethods

local SessionMethods = {}
SessionMethods.__index = SessionMethods

local function expectLocation(value: any, label: string): string
	assert(type(value) == "string" and value ~= "", `{label} must have a source location`)
	return value
end

local function contractKey(location: string, resultOrdinal: number): string
	return location .. "\0" .. tostring(resultOrdinal)
end

function TargetResultContracts.new(document: Record, contracts: { Contract }): Matcher
	assert(#contracts > 0, "target result contract list must not be empty")
	local callsByLocation: { [string]: Record } = {}
	AstAdmission.visitRuntime(document, function(record: Record)
		if record.type == "AstExprCall" then
			local location = expectLocation(record.location, "target result producer call")
			assert(callsByLocation[location] == nil, `target result producer call location {location} is ambiguous`)
			callsByLocation[location] = record
		end
	end)

	local indexed: { IndexedContract } = {}
	local byKey: { [string]: IndexedContract } = {}
	for index, contract in contracts do
		local location = expectLocation(contract.producer_call_location, `target result contract {index}.producer_call_location`)
		local ordinal = contract.result_ordinal
		assert(
			type(ordinal) == "number"
				and ordinal >= 1
				and ordinal <= TargetResultContracts.maxResultOrdinal
				and ordinal % 1 == 0,
			`target result contract {index}.result_ordinal is invalid`
		)
		local call = callsByLocation[location]
		assert(call ~= nil, `target result contract {index} does not identify an exact producer call`)
		local key = contractKey(location, ordinal)
		assert(byKey[key] == nil, `target result contract {index} duplicates a producer result ordinal`)
		local item: IndexedContract = {
			call = call :: Record,
			originKey = TargetProofBundle.targetOriginKey(contract.origin),
			evidence = contract.evidence,
			proofEvidence = contract.proof.evidence,
			index = index,
		}
		byKey[key] = item
		table.insert(indexed, item)
	end

	return setmetatable({
		contracts = indexed,
		byKey = byKey,
		used = {},
	}, MatcherMethods) :: any
end

function MatcherMethods:begin(origin: any): Session
	return setmetatable({
		matcher = self,
		originKey = TargetProofBundle.targetOriginKey(origin),
		matched = {},
		committed = false,
	}, SessionMethods) :: any
end

function SessionMethods:matches(value: any, resultOrdinal: number, _origin: Record): boolean
	local session = self :: any
	assert(not session.committed, "target result contract session was used after commit")
	if resultOrdinal < 1
		or resultOrdinal > TargetResultContracts.maxResultOrdinal
		or resultOrdinal % 1 ~= 0
	then
		return false
	end
	local expression = InvocationFrame.unwrapExpression(value, "target result contract candidate")
	if expression.type ~= "AstExprCall" or type(expression.location) ~= "string" then
		return false
	end
	local contract = session.matcher.byKey[contractKey(expression.location, resultOrdinal)]
	if contract == nil or contract.call ~= expression or contract.originKey ~= session.originKey then
		return false
	end
	session.matched[contract.index] = true
	return true
end

function SessionMethods:commit(): { Evidence }
	local session = self :: any
	assert(not session.committed, "target result contract session was committed more than once")
	session.committed = true
	local evidence: { Evidence } = {}
	local seenEvidence: { [string]: boolean } = {}
	local function append(item: Evidence)
		local key = item.kind .. "\0" .. item.locator .. "\0" .. (item.digest or "")
		if seenEvidence[key] ~= true then
			seenEvidence[key] = true
			table.insert(evidence, item)
		end
	end
	for _, contract in session.matcher.contracts do
		if session.matched[contract.index] == true then
			session.matcher.used[contract.index] = true
			append(contract.evidence)
			append(contract.proofEvidence)
		end
	end
	return evidence
end

function MatcherMethods:assertFullyUsed(label: string)
	local matcher = self :: any
	for _, contract in matcher.contracts do
		assert(matcher.used[contract.index] == true, `{label} contains unused result contract {contract.index}`)
	end
end

return table.freeze(TargetResultContracts)
