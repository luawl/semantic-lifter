--!strict

-- Expression and result-pack lowering for ast_frontend.luau. The host owns
-- lexical bindings and function construction; this module owns evaluation
-- order and expression-level Luau semantics.

local LifterIR = require("./lifter_ir")
local IntrinsicBindings = require("./intrinsic_bindings")
local Outcome = require("./ast_frontend_outcome")
local AstExpressionScalar = require("./ast_expression_scalar")
local OperatorDomains = require("./ast_frontend_operator_domains")
local AstTables = require("./ast_frontend_tables")

local AstExpressions = {}
local ExpressionLowerer = {}
ExpressionLowerer.__index = ExpressionLowerer

type Record = { [string]: any }

type Host = {
	diagnostic: (string, Record, string) -> never,
	expect_record: (any, string, string) -> Record,
	expect_array: (any, Record, string) -> { any },
	node_tag: (Record) -> string,
	scalar_result: (any, Record, Record, Record, string?, Record) -> any,
	instruction_options: (any, Record, Record, { number }?) -> Record,
	add_terminator_evidence: (any, Record, { number }?) -> (),
	add_target_recovery_obligation: (any, Record, Record) -> (),
	resolve_target_recovery: (any, Record) -> any?,
	lower_target_recovery_origin: (any, Record, Record) -> any,
	mark_target_recovery_resolution_used: (any, Record) -> (),
	resolve_local: (any, Record, Record) -> any,
	defer_register_local: (any, Record) -> (() -> any)?,
	resolve_intrinsic_alias: (any, Record) -> any?,
	lower_function: (any, Record, string?) -> any,
	lower_short_circuit: (any, Record, string?) -> any,
	lower_if_expression: (any, Record, string?) -> any,
}

export type Lowerer = typeof(setmetatable({} :: { host: Host }, ExpressionLowerer))

function AstExpressions.new(host: Host): Lowerer
	return setmetatable({ host = host }, ExpressionLowerer)
end

function ExpressionLowerer:_constantNumber(context: any, node: Record, nameHint: string?): any
	local value, valueProblem = AstExpressionScalar.numberValue(node)
	if valueProblem ~= nil then
		self.host.diagnostic(valueProblem.code, valueProblem.node, valueProblem.detail)
	end
	local numericValue = value :: number
	local specialNumber = AstExpressionScalar.specialNumberName(numericValue)
	if specialNumber ~= nil then
		return self.host.scalar_result(
			context,
			node,
			LifterIR.Operation.constant(LifterIR.Literal.specialNumber(specialNumber)),
			LifterIR.Types.number(),
			nameHint,
			LifterIR.Effects.pure()
		)
	end
	local negativeZero = numericValue == 0 and 1 / numericValue == -math.huge
	if not negativeZero and numericValue % 1 == 0 and math.abs(numericValue) <= 9007199254740991 then
		return self.host.scalar_result(
			context,
			node,
			LifterIR.Operation.constant(LifterIR.Literal.integer(string.format("%.0f", numericValue))),
			LifterIR.Types.integer(),
			nameHint,
			LifterIR.Effects.pure()
		)
	end
	return self.host.scalar_result(
		context,
		node,
		LifterIR.Operation.constant(LifterIR.Literal.number(numericValue)),
		LifterIR.Types.number(),
		nameHint,
		LifterIR.Effects.pure()
	)
end

function ExpressionLowerer:_constantInteger(context: any, node: Record, nameHint: string?): any
	local value, valueProblem = AstExpressionScalar.integerValue(node)
	if valueProblem ~= nil then
		self.host.diagnostic(valueProblem.code, valueProblem.node, valueProblem.detail)
	end
	local integerValue = value :: AstExpressionScalar.IntegerValue
	local valueType = if integerValue.wide then LifterIR.Types.integer(65535, integerValue.signed) else LifterIR.Types.integer()
	return self.host.scalar_result(
		context,
		node,
		LifterIR.Operation.constant(LifterIR.Literal.integer(integerValue.decimal)),
		valueType,
		nameHint,
		LifterIR.Effects.pure()
	)
end

function ExpressionLowerer:_constantString(context: any, node: Record, value: string, nameHint: string?): any
	return self.host.scalar_result(
		context,
		node,
		LifterIR.Operation.constant(LifterIR.Literal.string(value)),
		LifterIR.Types.string(),
		nameHint,
		LifterIR.Effects.pure()
	)
end

-- Luau reads a register local that is the base (or, for an assignment target, the key) of an index
-- at the indexing instruction, after the key and the assigned values ran; another base or key is
-- computed in order. A read's base place read follows its key.
-- With deferTarget the base and key reads are returned unread (read_table, read_key) for the caller.
function ExpressionLowerer:lowerIndexAddress(context: any, node: Record, deferTarget: boolean?): any
	local host: Host = self.host
	local tag = host.node_tag(node)
	if tag == "AstExprIndexExpr" then
		local tableNode = host.expect_record(node.expr, "malformed_index", "index expression is missing its table")
		local readTable = host.defer_register_local(context, tableNode)
		local tableValue = nil
		if readTable == nil then
			local tableOutcome = self:lower(context, tableNode, nil)
			if tableOutcome.kind == "terminated" then
				return tableOutcome
			end
			tableValue = tableOutcome.value
		end
		local keyNode = host.expect_record(node.index, "malformed_index", "index expression is missing its key")
		local readKey = if deferTarget then host.defer_register_local(context, keyNode) else nil
		local keyValue = nil
		if readKey == nil then
			local keyOutcome = self:lower(context, keyNode, nil)
			if keyOutcome.kind == "terminated" then
				return keyOutcome
			end
			keyValue = keyOutcome.value
		end
		if deferTarget then
			return Outcome.value({ table_value = tableValue, key = keyValue, read_table = readTable, read_key = readKey })
		end
		if readTable ~= nil then
			tableValue = readTable()
		end
		return Outcome.value({ table_value = tableValue, key = keyValue })
	elseif tag == "AstExprIndexName" then
		local index, indexProblem = AstExpressionScalar.indexName(node)
		if indexProblem ~= nil then
			host.diagnostic(indexProblem.code, indexProblem.node, indexProblem.detail)
		end
		local tableNode = host.expect_record(node.expr, "malformed_index", "named index is missing its table")
		local readTable = if deferTarget then host.defer_register_local(context, tableNode) else nil
		local tableValue = nil
		if readTable == nil then
			local tableOutcome = self:lower(context, tableNode, nil)
			if tableOutcome.kind == "terminated" then
				return tableOutcome
			end
			tableValue = tableOutcome.value
		end
		return Outcome.value({
			table_value = tableValue,
			key = self:_constantString(context, node, index :: string, "field_key"),
			read_table = readTable,
		})
	end
	return host.diagnostic("unsupported_index_address", node, `expression node {tag} is not an indexed place`)
end

function ExpressionLowerer:_lowerInterpolation(context: any, node: Record, nameHint: string?): any
	local host: Host = self.host
	local interpolation, interpolationProblem = AstExpressionScalar.interpolationValue(node)
	if interpolationProblem ~= nil then
		host.diagnostic(interpolationProblem.code, interpolationProblem.node, interpolationProblem.detail)
	end
	local interpolationValue = interpolation :: AstExpressionScalar.InterpolationValue
	local values: { number } = {}
	for _, expressionValue in interpolationValue.expressions do
		local valueOutcome = self:lower(
			context,
			host.expect_record(expressionValue, "malformed_interpolation", "interpolation value is not an AST expression"),
			nil
		)
		if valueOutcome.kind == "terminated" then
			return valueOutcome
		end
		table.insert(values, valueOutcome.value.id)
	end
	return Outcome.value(host.scalar_result(
		context,
		node,
		LifterIR.Operation.stringInterpolate(interpolationValue.segments, values),
		LifterIR.Types.string(),
		nameHint,
		LifterIR.Effects.stringInterpolation()
	))
end

function ExpressionLowerer:compoundOperatorName(node: Record): string
	local operatorName, operatorProblem = AstExpressionScalar.compoundOperatorName(node)
	if operatorProblem ~= nil then
		self.host.diagnostic(operatorProblem.code, operatorProblem.node, operatorProblem.detail)
	end
	return operatorName :: string
end

function ExpressionLowerer:lowerBinaryValues(
	context: any,
	node: Record,
	operatorName: string,
	left: any,
	right: any,
	nameHint: string?
): any
	local operatorProblem = AstExpressionScalar.binaryOperatorProblem(node, operatorName, true)
	if operatorProblem ~= nil then
		self.host.diagnostic(operatorProblem.code, operatorProblem.node, operatorProblem.detail)
	end
	local operator = AstExpressionScalar.binaryOperator(operatorName)
	assert(operator ~= nil, "admitted binary operator is not mapped")
	local resultType, staticDomain = OperatorDomains.binary(operator :: string, left.type, right.type)
	local effects = if staticDomain then LifterIR.Effects.pure() else LifterIR.Effects.dynamicCall()
	return self.host.scalar_result(
		context,
		node,
		LifterIR.Operation.binary(operator :: string, left.id, right.id),
		resultType,
		nameHint,
		effects
	)
end

local function splitCallArguments(host: Host, node: Record): ({ any }, number, Record?)
	local argumentNodes = host.expect_array(node.args, node, "args")
	local scalarCount = #argumentNodes
	local openArgument: Record? = nil
	if scalarCount > 0 then
		local lastArgument = host.expect_record(argumentNodes[scalarCount], "malformed_call", "call argument is not an AST node")
		local lastTag = host.node_tag(lastArgument)
		if lastTag == "AstExprCall" or lastTag == "AstExprVarargs" then
			openArgument = lastArgument
			scalarCount -= 1
		end
	end
	return argumentNodes, scalarCount, openArgument
end

local function staticIntrinsicPath(host: Host, functionNode: Record): string?
	local functionTag = host.node_tag(functionNode)
	if functionTag == "AstExprGlobal" then
		if type(functionNode.global) == "string" and IntrinsicBindings.kindForPath(functionNode.global) ~= nil then
			return functionNode.global
		end
		return nil
	end
	if functionTag ~= "AstExprIndexName" or type(functionNode.index) ~= "string" or type(functionNode.expr) ~= "table" then
		return nil
	end
	local receiver = functionNode.expr :: Record
	if receiver.type ~= "AstExprGlobal" or receiver.global ~= "coroutine" then
		return nil
	end
	local path = "coroutine." .. functionNode.index
	if IntrinsicBindings.kindForPath(path) == nil then
		return nil
	end
	return path
end

local function attachIntrinsicIdentity(host: Host, context: any, node: Record, value: any): any
	local path = staticIntrinsicPath(host, node)
	if path == nil then
		return value
	end
	local evidence = context.frontend.intrinsic_evidence_by_path[path]
	local kind = IntrinsicBindings.kindForPath(path)
	if evidence ~= nil and kind ~= nil then
		value.intrinsic = { kind = kind, evidence = evidence }
	end
	return value
end

local function callUsesSelf(host: Host, node: Record): boolean
	local usesSelf, flagProblem = AstExpressionScalar.callUsesSelf(node)
	if flagProblem ~= nil then
		host.diagnostic(flagProblem.code, flagProblem.node, flagProblem.detail)
	end
	return usesSelf :: boolean
end

local function callMethodName(host: Host, node: Record): string?
	local methodName, methodProblem = AstExpressionScalar.callMethodName(node)
	if methodProblem ~= nil then
		host.diagnostic(methodProblem.code, methodProblem.node, methodProblem.detail)
	end
	return methodName
end

local function lowerableIntrinsic(
	host: Host,
	context: any,
	node: Record,
	functionNode: Record,
	scalarCount: number,
	openArgument: Record?
): (string?, number?)
	if callUsesSelf(host, node) then
		return nil, nil
	end
	local path = staticIntrinsicPath(host, functionNode)
	if path == nil then
		return nil, nil
	end
	local evidence = context.frontend.intrinsic_evidence_by_path[path]
	local kind = IntrinsicBindings.kindForPath(path)
	if evidence == nil or kind == nil or not IntrinsicBindings.canLower(kind, scalarCount, openArgument ~= nil) then
		return nil, nil
	end
	return kind, evidence
end

local function lowerableValueIntrinsic(value: any, scalarCount: number, openArgument: Record?): (string?, number?)
	local identity = value.intrinsic
	if identity == nil
		or type(identity.kind) ~= "string"
		or type(identity.evidence) ~= "number"
		or not IntrinsicBindings.canLower(identity.kind, scalarCount, openArgument ~= nil)
	then
		return nil, nil
	end
	return identity.kind, identity.evidence
end

local function recoveredIntrinsicIdentity(resolution: any?): any?
	if resolution == nil or resolution.kind ~= "intrinsic" or resolution.preserve_source_target == true then
		return nil
	end
	return { kind = resolution.intrinsic_kind, evidence = resolution.evidence }
end

local function recoveredResolutionEvidence(resolution: any?): { number }?
	if resolution == nil then
		return nil
	end
	local evidence: { number } = { resolution.evidence }
	if resolution.proof_evidence ~= nil then
		assert(type(resolution.proof_evidence) == "table", "verified target proof evidence must be an ID array")
		for _, evidenceId in resolution.proof_evidence do
			assert(type(evidenceId) == "number", "verified target proof evidence must contain IDs")
			if not table.find(evidence, evidenceId) then
				table.insert(evidence, evidenceId)
			end
		end
	end
	return evidence
end

local function exactOpenResultTypes(host: Host, context: any, node: Record): { any }?
	if host.node_tag(node) ~= "AstExprCall" then
		return nil
	end
	local functionNode = host.expect_record(node.func, "malformed_call", "call is missing its callee")
	local _, scalarCount, openArgument = splitCallArguments(host, node)
	local recoveredResolution = host.resolve_target_recovery(context, node)
	local recoveredIdentity = recoveredIntrinsicIdentity(recoveredResolution)
	local kind = if recoveredIdentity ~= nil
		then lowerableValueIntrinsic({ intrinsic = recoveredIdentity }, scalarCount, openArgument)
		elseif recoveredResolution == nil then lowerableIntrinsic(host, context, node, functionNode, scalarCount, openArgument)
		else nil
	if kind == nil and recoveredResolution == nil and host.node_tag(functionNode) == "AstExprLocal" then
		local localNode = host.expect_record(functionNode["local"], "malformed_local_expression", "local expression has no declaration identity")
		local identity = host.resolve_intrinsic_alias(context, localNode)
		if identity ~= nil and IntrinsicBindings.canLower(identity.kind, scalarCount, openArgument ~= nil) then
			kind = identity.kind
		end
	end
	if kind == nil then
		return nil
	end
	return IntrinsicBindings.exactOpenResultTypes(kind)
end

local maxErrorLevel = 2147483647

local function staticErrorLevel(host: Host, originalNode: Record): number?
	local node = originalNode
	local tag = host.node_tag(node)
	while tag == "AstExprGroup" or tag == "AstExprTypeAssertion" or tag == "AstExprInstantiate" do
		node = host.expect_record(node.expr, "malformed_error_level", "error level wrapper is missing its expression")
		tag = host.node_tag(node)
	end
	if tag == "AstExprConstantNil" then
		return 1
	elseif tag == "AstExprConstantNumber" then
		local value = node.value
		if type(value) == "number" and value >= 0 and value <= maxErrorLevel and value % 1 == 0 then
			return value
		end
	elseif tag == "AstExprConstantInteger" then
		local value = node.value
		if type(value) == "number" and value >= 0 and value <= maxErrorLevel and value % 1 == 0 then
			return value
		elseif type(value) == "string" and string.match(value, "^%d+$") ~= nil then
			local parsed = tonumber(value)
			if parsed ~= nil and parsed <= maxErrorLevel then
				return parsed
			end
		end
	end
	return nil
end

local function intrinsicResultName(kind: string, index: number): string
	if index == 1 then
		if kind == "coroutine_create" then
			return "thread"
		elseif kind == "protected_call" or kind == "protected_call_with_handler" or kind == "coroutine_resume" then
			return "status"
		end
		return "yield_result"
	end
	return `intrinsic_result_{index}`
end

function ExpressionLowerer:lowerTerminatingCall(
	context: any,
	node: Record,
	intrinsicIdentity: any?,
	recoveryEvidence: { number }?
): any?
	local host: Host = self.host
	if callUsesSelf(host, node) then
		return nil
	end
	local evidence: number?
	local kind: string?
	if intrinsicIdentity ~= nil then
		evidence = intrinsicIdentity.evidence
		kind = intrinsicIdentity.kind
	else
		local functionNode = host.expect_record(node.func, "malformed_call", "call is missing its callee")
		local path = staticIntrinsicPath(host, functionNode)
		if path == nil then
			return nil
		end
		evidence = context.frontend.intrinsic_evidence_by_path[path]
		kind = IntrinsicBindings.kindForPath(path)
	end
	if evidence == nil or kind == nil then
		return nil
	end
	local argumentNodes, scalarCount, openArgument = splitCallArguments(host, node)
	local exactOpenTypes = if scalarCount == 0 and openArgument ~= nil
		then exactOpenResultTypes(host, context, openArgument)
		else nil
	local exactOpenMessage = kind == "error_termination" and exactOpenTypes ~= nil and #exactOpenTypes == 1
	if not IntrinsicBindings.canTerminate(kind, scalarCount, openArgument ~= nil) and not exactOpenMessage then
		return nil
	end

	local level = 1
	local dynamicLevelArgument = false
	if scalarCount >= 2 then
		local staticLevel = staticErrorLevel(
			host,
			host.expect_record(argumentNodes[2], "malformed_call", "error level is not an AST node")
		)
		if staticLevel ~= nil then
			level = staticLevel
		else
			dynamicLevelArgument = true
		end
	end

	local message: any? = nil
	local dynamicLevel: any? = nil
	local openConsumedAsMessage = false
	if exactOpenMessage then
		local openOutcome = self:lowerOpen(context, openArgument :: Record)
		if openOutcome.kind == "terminated" then
			return openOutcome
		end
		if openOutcome.kind ~= "open_pack" or openOutcome.exact_types == nil or #openOutcome.exact_types ~= 1 then
			host.diagnostic("intrinsic_open_shape_mismatch", openArgument :: Record, "authenticated exact-one call did not produce an exact-one open pack")
		end
		local _, adjusted = context.frontend.builder:addInstruction(
			context.block,
			LifterIR.Operation.adjustPack(openOutcome.pack),
			{ { type = (exactOpenTypes :: { any })[1], name_hint = "error_message" } },
			host.instruction_options(context.frontend, openArgument :: Record, LifterIR.Effects.pure(), nil)
		)
		message = { id = adjusted[1], type = (exactOpenTypes :: { any })[1] }
		openConsumedAsMessage = true
	elseif scalarCount == 0 then
		message = host.scalar_result(
			context,
			node,
			LifterIR.Operation.constant(LifterIR.Literal.nilValue()),
			LifterIR.Types.nilValue(),
			"error_message",
			LifterIR.Effects.pure()
		)
	else
		for index = 1, scalarCount do
			local argumentNode = argumentNodes[index]
			local argumentOutcome = self:lower(
				context,
				host.expect_record(argumentNode, "malformed_call", "call argument is not an AST node"),
				nil
			)
			if argumentOutcome.kind == "terminated" then
				return argumentOutcome
			end
			if index == 1 then
				message = argumentOutcome.value
			elseif index == 2 and dynamicLevelArgument then
				dynamicLevel = argumentOutcome.value
			end
		end
	end
	if openArgument ~= nil and not openConsumedAsMessage then
		if host.node_tag(openArgument) == "AstExprCall" then
			local openOutcome = self:lowerCall(context, openArgument, 0)
			if openOutcome.kind == "terminated" then
				return openOutcome
			end
		end
	end
	if message == nil then
		host.diagnostic("malformed_error_call", node, "error termination has no message value")
	end
	if dynamicLevelArgument and dynamicLevel == nil then
		host.diagnostic("malformed_error_call", node, "dynamic error level has no value")
	end
	local evidenceIds = { evidence }
	if recoveryEvidence ~= nil then
		for _, evidenceId in recoveryEvidence do
			if not table.find(evidenceIds, evidenceId) then
				table.insert(evidenceIds, evidenceId)
			end
		end
	end
	host.add_terminator_evidence(context, node, evidenceIds)
	host.add_target_recovery_obligation(context, node, LifterIR.Entity.block(context.block))
	context.frontend.builder:finalizeBlock(
		context.block,
		LifterIR.Terminator.throwError(
			(message :: any).id,
			if dynamicLevel == nil then level else 0,
			if dynamicLevel == nil then nil else (dynamicLevel :: any).id
		)
	)
	context.terminated = true
	return Outcome.terminated()
end

function ExpressionLowerer:lowerCall(context: any, node: Record, resultCount: number): any
	local host: Host = self.host
	local recoveredResolution = host.resolve_target_recovery(context, node)
	local recoveredIdentity = recoveredIntrinsicIdentity(recoveredResolution)
	local recoveryEvidence = recoveredResolutionEvidence(recoveredResolution)
	if recoveredResolution ~= nil then
		host.mark_target_recovery_resolution_used(context, node)
	end
	local terminatingOutcome = self:lowerTerminatingCall(context, node, recoveredIdentity, recoveryEvidence)
	if terminatingOutcome ~= nil then
		return terminatingOutcome
	end
	local arguments = {}
	local functionNode = host.expect_record(node.func, "malformed_call", "call is missing its callee")
	local argumentNodes, scalarCount, openArgument = splitCallArguments(host, node)
	local argumentPack: number? = nil

	local intrinsicKind: string?
	local intrinsicEvidence: number?
	if recoveredIdentity ~= nil then
		intrinsicKind, intrinsicEvidence = lowerableValueIntrinsic(
			{ intrinsic = recoveredIdentity },
			scalarCount,
			openArgument
		)
		if intrinsicKind == nil or intrinsicEvidence == nil then
			host.diagnostic(
				"target_recovery_unsupported_intrinsic_shape",
				node,
				"authenticated intrinsic target cannot preserve this call's argument or result shape"
			)
		end
	elseif recoveredResolution == nil then
		intrinsicKind, intrinsicEvidence = lowerableIntrinsic(host, context, node, functionNode, scalarCount, openArgument)
	end

	local callee: any? = nil
	local namecallReceiver: any? = nil
	local namecallMethod: string? = nil
	local staticMethodName = callMethodName(host, node)
	if intrinsicKind == nil and staticMethodName ~= nil then
		if recoveredResolution ~= nil then
			if recoveredResolution.kind ~= "namecall"
				or type(recoveredResolution.namecall_method) ~= "string"
				or recoveredResolution.namecall_method ~= staticMethodName
			then
				host.diagnostic("target_recovery_origin_mismatch", node, "verified target does not match this method call")
			end
		end
		if recoveredResolution ~= nil and recoveredResolution.preserve_source_target ~= true then
			namecallReceiver = host.lower_target_recovery_origin(context, node, recoveredResolution)
		else
			local receiverOutcome = self:lower(
				context,
				host.expect_record(functionNode.expr, "malformed_method_call", "method call is missing its receiver"),
				"receiver"
			)
			if receiverOutcome.kind == "terminated" then
				return receiverOutcome
			end
			namecallReceiver = receiverOutcome.value
		end
		namecallMethod = if recoveredResolution ~= nil then recoveredResolution.namecall_method else staticMethodName
	elseif intrinsicKind == nil then
		if recoveredResolution ~= nil and recoveredResolution.kind == "namecall" then
			host.diagnostic("target_recovery_origin_mismatch", node, "verified namecall target was applied to an ordinary call")
		end
		local calleeValue: any
		if recoveredResolution ~= nil and recoveredResolution.preserve_source_target ~= true then
			calleeValue = host.lower_target_recovery_origin(context, node, recoveredResolution)
		else
			local calleeOutcome = self:lower(context, functionNode, nil :: any)
			if calleeOutcome.kind == "terminated" then
				return calleeOutcome
			end
			calleeValue = calleeOutcome.value
		end
		if recoveredResolution == nil and calleeValue.intrinsic ~= nil then
			local aliasTermination = self:lowerTerminatingCall(context, node, calleeValue.intrinsic, nil)
			if aliasTermination ~= nil then
				return aliasTermination
			end
			intrinsicKind, intrinsicEvidence = lowerableValueIntrinsic(calleeValue, scalarCount, openArgument)
		end
		if intrinsicKind == nil then
			callee = calleeValue
		end
	end
	for index = 1, scalarCount do
		local argumentOutcome = self:lower(
			context,
			host.expect_record(argumentNodes[index], "malformed_call", "call argument is not an AST node"),
			nil :: any
		)
		if argumentOutcome.kind == "terminated" then
			return argumentOutcome
		end
		table.insert(arguments, argumentOutcome.value.id)
	end
	if openArgument ~= nil then
		local argumentOutcome = self:lowerOpen(context, openArgument)
		if argumentOutcome.kind == "terminated" then
			return argumentOutcome
		end
		argumentPack = argumentOutcome.pack
	end

	if intrinsicKind ~= nil and intrinsicEvidence ~= nil then
		local intrinsicEvidenceIds = { intrinsicEvidence }
		if recoveryEvidence ~= nil then
			for _, evidenceId in recoveryEvidence do
				if not table.find(intrinsicEvidenceIds, evidenceId) then
					table.insert(intrinsicEvidenceIds, evidenceId)
				end
			end
		end
		local options = host.instruction_options(
			context.frontend,
			node,
			IntrinsicBindings.effects(intrinsicKind),
			intrinsicEvidenceIds
		)
		if resultCount < 0 then
			local instruction, pack = IntrinsicBindings.addOpen(
				intrinsicKind,
				context.frontend.builder,
				context.block,
				arguments,
				options,
				argumentPack
			)
			host.add_target_recovery_obligation(context, node, LifterIR.Entity.instruction(instruction))
			return Outcome.openPack(pack, IntrinsicBindings.exactOpenResultTypes(intrinsicKind))
		end

		local actualResultCount = IntrinsicBindings.fixedResultCount(intrinsicKind, resultCount)
		local resultSpecs = {}
		for index = 1, actualResultCount do
			table.insert(resultSpecs, {
				type = IntrinsicBindings.resultType(intrinsicKind, index),
				name_hint = intrinsicResultName(intrinsicKind, index),
			})
		end
		local instruction, results = context.frontend.builder:addInstruction(
			context.block,
			IntrinsicBindings.operation(intrinsicKind, arguments, actualResultCount, argumentPack),
			resultSpecs,
			options
		)
		host.add_target_recovery_obligation(context, node, LifterIR.Entity.instruction(instruction))
		if resultCount == 0 then
			return Outcome.effect()
		end
		return Outcome.value({ id = results[1], type = IntrinsicBindings.resultType(intrinsicKind, 1) })
	end

	local options = host.instruction_options(context.frontend, node, LifterIR.Effects.dynamicCall(), recoveryEvidence)
	if resultCount < 0 then
		local instruction, pack
		if namecallReceiver ~= nil and namecallMethod ~= nil then
			instruction, pack = context.frontend.builder:addOpenNamecall(
				context.block,
				(namecallReceiver :: any).id,
				namecallMethod,
				arguments,
				options,
				argumentPack
			)
		else
			instruction, pack = context.frontend.builder:addOpenCall(context.block, (callee :: any).id, arguments, options, argumentPack)
		end
		host.add_target_recovery_obligation(context, node, LifterIR.Entity.instruction(instruction))
		return Outcome.openPack(pack, nil)
	end
	local resultSpecs = {}
	for index = 1, resultCount do
		table.insert(resultSpecs, {
			type = LifterIR.Types.dynamic(),
			name_hint = if index == 1 then "call_result" else `call_result_{index}`,
		})
	end
	local operation = if namecallReceiver ~= nil and namecallMethod ~= nil
		then LifterIR.Operation.namecall(
			(namecallReceiver :: any).id,
			namecallMethod,
			arguments,
			LifterIR.ResultArity.fixed(resultCount),
			argumentPack
		)
		else LifterIR.Operation.call((callee :: any).id, arguments, LifterIR.ResultArity.fixed(resultCount), argumentPack)
	local instruction, results = context.frontend.builder:addInstruction(
		context.block,
		operation,
		resultSpecs,
		options
	)
	host.add_target_recovery_obligation(context, node, LifterIR.Entity.instruction(instruction))
	if resultCount == 0 then
		return Outcome.effect()
	end
	return Outcome.value({ id = results[1], type = LifterIR.Types.dynamic() })
end

function ExpressionLowerer:lowerOpen(context: any, node: Record): any
	local tag = self.host.node_tag(node)
	if tag == "AstExprVarargs" then
		if context.vararg_pack == nil then
			self.host.diagnostic("varargs_outside_variadic_function", node, "varargs have no owning function pack")
		end
		return Outcome.openPack(context.vararg_pack, nil)
	elseif tag == "AstExprCall" then
		local callOutcome = self:lowerCall(context, node, -1)
		if callOutcome.kind == "terminated" then
			return callOutcome
		end
		if callOutcome.kind ~= "open_pack" then
			self.host.diagnostic("malformed_call_result", node, "open call did not produce a value pack")
		end
		return callOutcome
	end
	return self.host.diagnostic("unsupported_open_expression", node, `expression node {tag} cannot produce an open result pack`)
end

function ExpressionLowerer:lower(context: any, node: Record, nameHint: string?): any
	local host: Host = self.host
	local tag = host.node_tag(node)
	if tag == "AstExprGroup" then
		return self:lower(context, host.expect_record(node.expr, "malformed_group", "group is missing its expression"), nameHint)
	elseif tag == "AstExprTypeAssertion" then
		return self:lower(
			context,
			host.expect_record(node.expr, "malformed_type_assertion", "type assertion is missing its runtime expression"),
			nameHint
		)
	elseif tag == "AstExprInstantiate" then
		return self:lower(
			context,
			host.expect_record(node.expr, "malformed_instantiation", "generic instantiation is missing its runtime expression"),
			nameHint
		)
	elseif tag == "AstExprConstantNil" then
		return Outcome.value(host.scalar_result(
			context,
			node,
			LifterIR.Operation.constant(LifterIR.Literal.nilValue()),
			LifterIR.Types.nilValue(),
			nameHint,
			LifterIR.Effects.pure()
		))
	elseif tag == "AstExprConstantBool" then
		local value, valueProblem = AstExpressionScalar.booleanValue(node)
		if valueProblem ~= nil then
			host.diagnostic(valueProblem.code, valueProblem.node, valueProblem.detail)
		end
		return Outcome.value(host.scalar_result(
			context,
			node,
			LifterIR.Operation.constant(LifterIR.Literal.boolean(value :: boolean)),
			LifterIR.Types.boolean(),
			nameHint,
			LifterIR.Effects.pure()
		))
	elseif tag == "AstExprConstantNumber" then
		return Outcome.value(self:_constantNumber(context, node, nameHint))
	elseif tag == "AstExprConstantInteger" then
		return Outcome.value(self:_constantInteger(context, node, nameHint))
	elseif tag == "AstExprConstantString" then
		local value, valueProblem = AstExpressionScalar.stringValue(node)
		if valueProblem ~= nil then
			host.diagnostic(valueProblem.code, valueProblem.node, valueProblem.detail)
		end
		return Outcome.value(host.scalar_result(
			context,
			node,
			LifterIR.Operation.constant(LifterIR.Literal.string(value :: string)),
			LifterIR.Types.string(),
			nameHint,
			LifterIR.Effects.pure()
		))
	elseif tag == "AstExprLocal" then
		local localNode = host.expect_record(node["local"], "malformed_local_expression", "local expression has no declaration identity")
		return Outcome.value(host.resolve_local(context, node, localNode))
	elseif tag == "AstExprGlobal" then
		local name, nameProblem = AstExpressionScalar.globalName(node)
		if nameProblem ~= nil then
			host.diagnostic(nameProblem.code, nameProblem.node, nameProblem.detail)
		end
		return Outcome.value(attachIntrinsicIdentity(host, context, node, host.scalar_result(
			context,
			node,
			LifterIR.Operation.environmentGet(LifterIR.EnvironmentTarget.ambient(), name :: string),
			LifterIR.Types.dynamic(),
			nameHint or (name :: string),
			LifterIR.Effects.semanticTableRead()
		)))
	elseif tag == "AstExprIndexExpr" or tag == "AstExprIndexName" then
		local addressOutcome = self:lowerIndexAddress(context, node)
		if addressOutcome.kind == "terminated" then
			return addressOutcome
		end
		local address = addressOutcome.value
		return Outcome.value(attachIntrinsicIdentity(host, context, node, host.scalar_result(
			context,
			node,
			LifterIR.Operation.tableGet(address.table_value.id, address.key.id),
			LifterIR.Types.dynamic(),
			nameHint or "field",
			LifterIR.Effects.semanticTableRead()
		)))
	elseif tag == "AstExprTable" then
		return AstTables.lower(self, host, context, node, nameHint)
	elseif tag == "AstExprInterpString" then
		return self:_lowerInterpolation(context, node, nameHint)
	elseif tag == "AstExprBinary" then
		if node.op == "And" or node.op == "Or" then
			return host.lower_short_circuit(context, node, nameHint)
		end
		-- Luau reads a register local named by the left operand of an arithmetic or comparison
		-- operator at the operator instruction, after the right operand ran; a concatenation copies
		-- its operands in order (SOURCE-FRONTEND-READ-ORDER).
		local leftNode = host.expect_record(node.left, "malformed_binary", "binary expression is missing its left operand")
		local deferredLeft = if node.op ~= "Concat" then host.defer_register_local(context, leftNode) else nil
		local left = nil
		if deferredLeft == nil then
			local leftOutcome = self:lower(context, leftNode, nil)
			if leftOutcome.kind == "terminated" then
				return leftOutcome
			end
			left = leftOutcome.value
		end
		local rightOutcome = self:lower(context, host.expect_record(node.right, "malformed_binary", "binary expression is missing its right operand"), nil)
		if rightOutcome.kind == "terminated" then
			return rightOutcome
		end
		if deferredLeft ~= nil then
			left = deferredLeft()
		end
		return Outcome.value(self:lowerBinaryValues(context, node, node.op, left, rightOutcome.value, nameHint))
	elseif tag == "AstExprUnary" then
		local operator = AstExpressionScalar.unaryOperator(node.op)
		if operator == nil then
			host.diagnostic("unsupported_unary_operator", node, `unary operator {tostring(node.op)} is not mapped`)
		end
		local operandOutcome = self:lower(context, host.expect_record(node.expr, "malformed_unary", "unary expression is missing its operand"), nil)
		if operandOutcome.kind == "terminated" then
			return operandOutcome
		end
		local resultType, staticDomain = OperatorDomains.unary(operator :: string, operandOutcome.value.type)
		local effects = if staticDomain then LifterIR.Effects.pure() else LifterIR.Effects.dynamicCall()
		return Outcome.value(host.scalar_result(
			context,
			node,
			LifterIR.Operation.unary(operator :: string, operandOutcome.value.id),
			resultType,
			nameHint,
			effects
		))
	elseif tag == "AstExprCall" then
		local callOutcome = self:lowerCall(context, node, 1)
		if callOutcome.kind == "terminated" then
			return callOutcome
		end
		if callOutcome.kind ~= "value" then
			host.diagnostic("malformed_call_result", node, "scalar call did not produce a value")
		end
		return callOutcome
	elseif tag == "AstExprVarargs" then
		local packOutcome = self:lowerOpen(context, node)
		if packOutcome.kind == "terminated" then
			return packOutcome
		end
		return Outcome.value(host.scalar_result(
			context,
			node,
			LifterIR.Operation.adjustPack(packOutcome.pack),
			LifterIR.Types.dynamic(),
			nameHint or "vararg",
			LifterIR.Effects.pure()
		))
	elseif tag == "AstExprFunction" then
		return Outcome.value(host.lower_function(context, node, nameHint))
	elseif tag == "AstExprIfElse" then
		return host.lower_if_expression(context, node, nameHint)
	elseif tag == "AstExprError" then
		host.diagnostic("malformed_source_expression", node, "parser recovery expression cannot be admitted as runtime semantics")
	end
	return host.diagnostic("unsupported_expression", node, `expression node {tag} is not supported by this frontend slice`)
end

return table.freeze(AstExpressions)
