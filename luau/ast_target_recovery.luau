--!strict

-- Adapts authenticated target recovery into frontend-local sites and lowers
-- verified source origins. Manifest/proof verification stays with the recovery
-- owners; generic expression semantics stay with ast_frontend_expressions.

local IntrinsicBindings = require("./intrinsic_bindings")
local LifterIR = require("./lifter_ir")
local AstExpressionScalar = require("./ast_expression_scalar")

local AstTargetRecovery = {}
local TargetLowerer = {}
TargetLowerer.__index = TargetLowerer

type Record = { [string]: any }

export type Resolution = {
	kind: string,
	intrinsic_kind: string?,
	value_origin: Record?,
	table_origin: Record?,
	table_key_origin: Record?,
	access_path_origin: Record?,
	receiver_origin: Record?,
	namecall_method: string?,
	temporal_identity: Record?,
	preserve_source_target: boolean,
	evidence: number,
	proof_evidence: { number }?,
}

type Site = {
	detail: string,
	evidence: number,
	consumed: boolean,
	dead: boolean,
	resolution: Resolution?,
	resolution_used: boolean,
}

export type State = {
	by_location: { [string]: Site },
	consumed: number,
	dead: number,
	resolved: number,
	expected_lowered: number?,
	expected_unresolved: number?,
	expected_resolved: number?,
	recovered_binding_names: { [string]: string },
}

type Host = {
	diagnostic: (string, Record, string) -> never,
	local_key: (Record) -> string,
	resolve_local_binding: (any, Record) -> any,
	materialize_binding: (any, Record, any, { number }?) -> any,
	instruction_options: (any, Record, Record, { number }?) -> Record,
	evidence_for: (any, Record) -> { number },
}

export type Lowerer = typeof(setmetatable({} :: { host: Host }, TargetLowerer))

function AstTargetRecovery.new(host: Host): Lowerer
	return setmetatable({ host = host }, TargetLowerer)
end

local function emptyState(): State
	return {
		by_location = {},
		consumed = 0,
		dead = 0,
		resolved = 0,
		expected_lowered = nil,
		expected_unresolved = nil,
		expected_resolved = nil,
		recovered_binding_names = {},
	}
end

function TargetLowerer:initialize(builder: any, root: Record, verified: any?): State
	local host: Host = self.host
	local state = emptyState()
	if verified == nil then
		return state
	end
	state.expected_lowered = verified.lowered_unresolved_call_count
	state.expected_unresolved = verified.unresolved_call_count
	state.expected_resolved = verified.resolved_call_count
	local mutableNamesAreClosed = verified.resolved_call_count == verified.unresolved_call_count

	local recoveryEvidence: number? = nil
	local proofBundleEvidence: number? = nil
	if verified.proof_bundle_evidence ~= nil then
		local evidence = verified.proof_bundle_evidence
		proofBundleEvidence = builder:addEvidence(evidence.kind, evidence.locator, evidence.digest)
	end
	for location, site in verified.by_call_location do
		if recoveryEvidence == nil then
			recoveryEvidence = builder:addEvidence(site.evidence.kind, site.evidence.locator, site.evidence.digest)
		end
		local resolution: Resolution? = nil
		if site.resolution ~= nil then
			local resolutionEvidence = builder:addEvidence(
				site.resolution.evidence.kind,
				site.resolution.evidence.locator,
				site.resolution.evidence.digest
			)
			local proofEvidence: { number } = {}
			if site.resolution.proof_evidence ~= nil then
				table.insert(proofEvidence, builder:addEvidence(
					site.resolution.proof_evidence.kind,
					site.resolution.proof_evidence.locator,
					site.resolution.proof_evidence.digest
				))
			end
			if site.resolution.result_contract_evidence ~= nil then
				for _, evidence in site.resolution.result_contract_evidence do
					local evidenceId = builder:addEvidence(evidence.kind, evidence.locator, evidence.digest)
					if not table.find(proofEvidence, evidenceId) then
						table.insert(proofEvidence, evidenceId)
					end
				end
			end
			if proofBundleEvidence ~= nil then
				if not table.find(proofEvidence, proofBundleEvidence) then
					table.insert(proofEvidence, proofBundleEvidence)
				end
			end
			local origin = site.resolution.origin
			if origin.kind == "intrinsic" then
				local intrinsicKind = IntrinsicBindings.kindForPath(origin.path)
				if intrinsicKind == nil then
					host.diagnostic("target_recovery_mismatch", root, "target recovery uses an unsupported intrinsic origin")
				end
				resolution = {
					kind = "intrinsic",
					intrinsic_kind = intrinsicKind,
					preserve_source_target = site.resolution.preserve_source_target,
					evidence = resolutionEvidence,
				}
			elseif origin.kind == "local_value"
				or origin.kind == "local_place"
				or origin.kind == "environment"
				or origin.kind == "closure_value"
			then
				resolution = {
					kind = origin.kind :: string,
					value_origin = origin,
					preserve_source_target = site.resolution.preserve_source_target,
					evidence = resolutionEvidence,
				}
			elseif origin.kind == "table_get" then
				resolution = {
					kind = "table_get",
					table_origin = origin.table_origin,
					table_key_origin = origin.key_origin,
					preserve_source_target = site.resolution.preserve_source_target,
					evidence = resolutionEvidence,
				}
			elseif origin.kind == "access_path" then
				resolution = {
					kind = "access_path",
					access_path_origin = origin,
					preserve_source_target = site.resolution.preserve_source_target,
					evidence = resolutionEvidence,
				}
			elseif origin.kind == "namecall" then
				resolution = {
					kind = "namecall",
					receiver_origin = origin.receiver_origin,
					namecall_method = origin.method,
					preserve_source_target = site.resolution.preserve_source_target,
					evidence = resolutionEvidence,
				}
			else
				host.diagnostic("target_recovery_mismatch", root, "target recovery uses an unsupported semantic origin")
			end
			if resolution ~= nil then
				resolution.proof_evidence = if #proofEvidence > 0 then proofEvidence else nil
			end
			if resolution ~= nil and site.resolution.temporal_identity ~= nil then
				resolution.temporal_identity = site.resolution.temporal_identity :: any
				local declaration = site.resolution.temporal_identity.declaration
				if type(declaration) == "table"
					and (site.resolution.temporal_identity.binding_kind == "value" or mutableNamesAreClosed)
				then
					state.recovered_binding_names[host.local_key(declaration :: Record)] = "recovered_target"
				end
			end
		end
		state.by_location[location] = {
			detail = site.detail,
			evidence = recoveryEvidence :: number,
			consumed = false,
			dead = false,
			resolution = resolution,
			resolution_used = false,
		}
	end
	return state
end

function TargetLowerer:resolutionAt(state: State, node: Record): Resolution?
	local location = if type(node.location) == "string" then node.location else ""
	local site = state.by_location[location]
	return if site ~= nil then site.resolution else nil
end

function TargetLowerer:markDead(state: State, value: any)
	if type(value) ~= "table" then
		return
	end
	local host: Host = self.host
	local record = value :: Record
	if record.type == "AstExprCall" and type(record.location) == "string" then
		local site = state.by_location[record.location]
		if site ~= nil and not site.consumed and not site.dead then
			if site.resolution ~= nil then
				host.diagnostic(
					"target_recovery_dead_resolution",
					record,
					"authenticated target resolution identifies a structurally dead call"
				)
			end
			site.dead = true
			state.dead += 1
		end
	end
	for _, child in record do
		self:markDead(state, child)
	end
end

local function lowerValueOrigin(host: Host, context: any, node: Record, origin: Record, evidence: number): any
	if origin.kind == "local_value" or origin.kind == "local_place" then
		local declaration = origin.declaration
		if type(declaration) ~= "table" then
			host.diagnostic("target_recovery_origin_mismatch", node, "verified local origin has no declaration identity")
		end
		local binding = host.resolve_local_binding(context, declaration :: Record)
		local expectedKind = if origin.kind == "local_value" then "value" else "place"
		if binding.kind ~= expectedKind then
			host.diagnostic(
				"target_recovery_origin_kind_mismatch",
				node,
				`verified {origin.kind} origin resolved to a {binding.kind} binding`
			)
		end
		return host.materialize_binding(context, node, binding, { evidence })
	elseif origin.kind == "environment" then
		local name = origin.name
		if type(name) ~= "string" or name == "" then
			host.diagnostic("target_recovery_origin_mismatch", node, "verified environment origin has no binding name")
		end
		local _, results = context.frontend.builder:addInstruction(
			context.block,
			LifterIR.Operation.environmentGet(LifterIR.EnvironmentTarget.ambient(), name :: string),
			{ { type = LifterIR.Types.dynamic(), name_hint = name } },
			host.instruction_options(context.frontend, node, LifterIR.Effects.semanticTableRead(), { evidence })
		)
		return { id = results[1], type = LifterIR.Types.dynamic() }
	end
	return host.diagnostic("target_recovery_origin_mismatch", node, "verified table root has an unsupported value origin")
end

local function lowerAccessKey(host: Host, context: any, node: Record, origin: Record, evidence: number): any
	if origin.kind == "source_expression" then
		return host.diagnostic(
			"target_recovery_origin_mismatch",
			node,
			"verified source-expression table key cannot be rematerialized"
		)
	end
	if origin.kind ~= "constant_string" and origin.kind ~= "constant_boolean" and origin.kind ~= "constant_number" then
		return lowerValueOrigin(host, context, node, origin, evidence)
	end
	local literal: Record
	local literalType: Record
	if origin.kind == "constant_string" then
		if type(origin.value) ~= "string" then
			host.diagnostic("target_recovery_origin_mismatch", node, "verified static access key has no string value")
		end
		literal = LifterIR.Literal.string(origin.value :: string)
		literalType = LifterIR.Types.string()
	elseif origin.kind == "constant_boolean" then
		if type(origin.value) ~= "boolean" then
			host.diagnostic("target_recovery_origin_mismatch", node, "verified static access key has no Boolean value")
		end
		literal = LifterIR.Literal.boolean(origin.value :: boolean)
		literalType = LifterIR.Types.boolean()
	else
		local numberValue = origin.value
		if type(numberValue) ~= "number"
			or numberValue ~= numberValue
			or numberValue == math.huge
			or numberValue == -math.huge
		then
			host.diagnostic("target_recovery_origin_mismatch", node, "verified static access key has no finite numeric value")
		end
		literal = LifterIR.Literal.number(if numberValue == 0 then 0 else numberValue)
		literalType = LifterIR.Types.number()
	end
	local _, results = context.frontend.builder:addInstruction(
		context.block,
		LifterIR.Operation.constant(literal),
		{ { type = literalType, name_hint = "target_key" } },
		host.instruction_options(context.frontend, node, LifterIR.Effects.pure(), { evidence })
	)
	return { id = results[1], type = literalType }
end

local function lowerTableGet(
	host: Host,
	context: any,
	node: Record,
	tableValue: any,
	keyValue: any,
	evidence: number
): any
	local _, results = context.frontend.builder:addInstruction(
		context.block,
		LifterIR.Operation.tableGet(tableValue.id, keyValue.id),
		{ { type = LifterIR.Types.dynamic(), name_hint = "recovered_target" } },
		host.instruction_options(context.frontend, node, LifterIR.Effects.semanticTableRead(), { evidence })
	)
	return { id = results[1], type = LifterIR.Types.dynamic() }
end

local function lowerAccessOrigin(host: Host, context: any, node: Record, origin: Record, evidence: number): any
	if origin.kind ~= "access_path" then
		return lowerValueOrigin(host, context, node, origin, evidence)
	end
	if type(origin.root_origin) ~= "table" or type(origin.key_origins) ~= "table" then
		host.diagnostic("target_recovery_origin_mismatch", node, "verified access path has no root or keys")
	end
	local value = lowerValueOrigin(host, context, node, origin.root_origin :: Record, evidence)
	for _, keyOrigin in origin.key_origins :: { Record } do
		local key = lowerAccessKey(host, context, node, keyOrigin, evidence)
		value = lowerTableGet(host, context, node, value, key, evidence)
	end
	return value
end

function TargetLowerer:lowerOrigin(context: any, node: Record, resolution: Resolution): any
	local host: Host = self.host
	local temporalIdentity = resolution.temporal_identity
	if temporalIdentity ~= nil then
		if type(temporalIdentity.declaration) ~= "table"
			or (temporalIdentity.binding_kind ~= "value" and temporalIdentity.binding_kind ~= "place")
		then
			host.diagnostic("target_recovery_origin_mismatch", node, "verified temporal target has no binding identity")
		end
		local binding = host.resolve_local_binding(context, temporalIdentity.declaration :: Record)
		if binding.kind ~= temporalIdentity.binding_kind then
			host.diagnostic(
				"target_recovery_origin_kind_mismatch",
				node,
				`verified temporal target resolved to a {binding.kind} binding instead of {temporalIdentity.binding_kind}`
			)
		end
		return host.materialize_binding(context, node, binding, { resolution.evidence })
	end
	if resolution.kind == "local_value" or resolution.kind == "local_place" or resolution.kind == "environment" then
		local valueOrigin = resolution.value_origin
		if type(valueOrigin) ~= "table" then
			host.diagnostic("target_recovery_origin_mismatch", node, "verified target has no value origin")
		end
		return lowerValueOrigin(host, context, node, valueOrigin :: Record, resolution.evidence)
	elseif resolution.kind == "table_get" then
		local tableOrigin = resolution.table_origin
		local keyOrigin = resolution.table_key_origin
		if type(tableOrigin) ~= "table" or type(keyOrigin) ~= "table" then
			host.diagnostic("target_recovery_origin_mismatch", node, "verified table target has no root or key")
		end
		local tableValue = lowerValueOrigin(host, context, node, tableOrigin :: Record, resolution.evidence)
		local keyValue = lowerAccessKey(host, context, node, keyOrigin :: Record, resolution.evidence)
		return lowerTableGet(host, context, node, tableValue, keyValue, resolution.evidence)
	elseif resolution.kind == "access_path" then
		local accessPath = resolution.access_path_origin
		if type(accessPath) ~= "table" then
			host.diagnostic("target_recovery_origin_mismatch", node, "verified target has no access path")
		end
		return lowerAccessOrigin(host, context, node, accessPath :: Record, resolution.evidence)
	elseif resolution.kind == "namecall" then
		local receiverOrigin = resolution.receiver_origin
		if type(receiverOrigin) ~= "table" then
			host.diagnostic("target_recovery_origin_mismatch", node, "verified namecall target has no receiver origin")
		end
		return lowerAccessOrigin(host, context, node, receiverOrigin :: Record, resolution.evidence)
	end
	return host.diagnostic("target_recovery_origin_mismatch", node, "nonmaterialized recovery origin was sent through value lowering")
end

function TargetLowerer:markResolutionUsed(state: State, node: Record)
	local host: Host = self.host
	local location = if type(node.location) == "string" then node.location else ""
	local site = state.by_location[location]
	if site == nil or site.resolution == nil then
		host.diagnostic("target_recovery_resolution_mismatch", node, "call lowering used a target resolution that was not verified")
	end
	if (site :: Site).resolution_used then
		host.diagnostic("target_recovery_duplicate_resolution", node, "one target resolution was used more than once")
	end
	(site :: Site).resolution_used = true
end

function TargetLowerer:addObligation(context: any, node: Record, subject: Record)
	local host: Host = self.host
	local state: State = context.frontend.target_recovery
	local location = if type(node.location) == "string" then node.location else ""
	local site = state.by_location[location]
	if site == nil then
		return
	end
	if site.consumed then
		host.diagnostic("target_recovery_duplicate_lowering", node, "one target recovery site was lowered more than once")
	end
	site.consumed = true
	state.consumed += 1
	if site.resolution ~= nil then
		if not site.resolution_used then
			host.diagnostic("target_recovery_resolution_unused", node, "verified target resolution did not determine the lowered callee")
		end
		state.resolved += 1
		return
	end
	local obligationEvidence = host.evidence_for(context.frontend, node)
	if not table.find(obligationEvidence, site.evidence) then
		table.insert(obligationEvidence, site.evidence)
	end
	table.sort(obligationEvidence)
	local usesSelf, flagProblem = AstExpressionScalar.callUsesSelf(node)
	if flagProblem ~= nil then
		host.diagnostic(flagProblem.code, flagProblem.node, flagProblem.detail)
	end
	local obligationKind = if usesSelf == true
		then LifterIR.ObligationKind.dispatchProof
		else LifterIR.ObligationKind.unresolvedIdentity
	context.frontend.builder:addObligation(
		obligationKind,
		subject,
		LifterIR.ObligationStatus.open,
		LifterIR.AdmissionProfile.readableLuau,
		site.detail,
		nil,
		nil,
		obligationEvidence
	)
end

function TargetLowerer:assertComplete(state: State, root: Record)
	if state.expected_unresolved == nil then
		return
	end
	local expectedLowered = state.expected_lowered :: number
	local expectedUnresolved = state.expected_unresolved :: number
	local expectedResolved = state.expected_resolved :: number
	if state.consumed == expectedLowered
		and state.consumed + state.dead == expectedUnresolved
		and state.resolved == expectedResolved
	then
		return
	end
	local unrepresented = {}
	for location, site in state.by_location do
		if not site.consumed and not site.dead then
			table.insert(unrepresented, location)
		end
	end
	table.sort(unrepresented)
	self.host.diagnostic(
		"target_recovery_unrepresented",
		root,
		`target recovery expected {expectedLowered} lowered sites and {expectedResolved} resolutions from {expectedUnresolved} source sites but classified {state.consumed} lowered, {state.resolved} resolved, and {state.dead} dead; unrepresented sites: {table.concat(unrepresented, ", ")}`
	)
end

return table.freeze(AstTargetRecovery)
