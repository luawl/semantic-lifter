--!strict

-- Pure lowering from the pinned luau-ast JSON shape into the shared semantic
-- IR. Parser process management belongs to lift_source.luau; this module only
-- interprets AST semantics and can be reused by other Luau frontends.

local LifterIR = require("./lifter_ir")
local Outcome = require("./ast_frontend_outcome")
local AstExpressions = require("./ast_frontend_expressions")
local OperatorDomains = require("./ast_frontend_operator_domains")
local PlaceDomains = require("./ast_frontend_place_domains")
local AstControl = require("./ast_frontend_control")
local AstIteration = require("./ast_frontend_iteration")
local AstAdmission = require("./ast_admission")
local AstExpressionScalar = require("./ast_expression_scalar")
local AstTargetRecovery = require("./ast_target_recovery")
local IntrinsicBindings = require("./intrinsic_bindings")
local RecoveryAdmission = require("./recovery_admission")
local TargetRecovery = require("./target_recovery")

local AstFrontend = {}

type Record = { [string]: any }
type RecordArray = { Record }

export type Options = {
	program_id: string,
	source_name: string,
	source_text: string?,
	program_obligations: { ProgramObligation }?,
	intrinsic_bindings: { IntrinsicBinding }?,
	target_recovery: TargetRecovery.Spec?,
}

export type IntrinsicBinding = {
	path: string,
	evidence: {
		kind: string,
		locator: string,
		digest: string?,
	},
}

export type ProgramObligation = {
	kind: string,
	blocks_profile: string,
	detail: string,
	evidence: {
		kind: string,
		locator: string,
		digest: string?,
	},
}

export type Diagnostic = {
	code: string,
	location: string,
	detail: string,
}

export type LiftResult = {
	program: Record?,
	diagnostics: { Diagnostic },
}

type ValueRef = {
	id: number,
	type: Record,
	intrinsic: {
		kind: string,
		evidence: number,
	}?,
}

type Binding = {
	kind: "value" | "place",
	value: ValueRef?,
	place: number?,
	type: Record,
	name: string,
}

type LoopTargets = {
	continue_block: number,
	break_block: number,
	continue_arguments: { number }?,
	break_arguments: { number }?,
	continue_reachable: boolean?,
	break_reachable: boolean?,
}

type FunctionContext = {
	frontend: FrontendState,
	id: number,
	parent: FunctionContext?,
	block: number,
	bindings: { [string]: Binding },
	capture_bindings: RecordArray,
	vararg_pack: number?,
	loop_stack: { LoopTargets },
	terminated: boolean,
}

type FrontendState = {
	builder: any,
	options: Options,
	evidence_by_location: { [string]: number },
	intrinsic_evidence_by_path: { [string]: number },
	target_recovery: AstTargetRecovery.State,
	mutable_locals: { [string]: boolean },
	reassigned_locals: { [string]: boolean },
}

local FrontendDiagnostic = {}
FrontendDiagnostic.__index = FrontendDiagnostic

local function diagnostic(code: string, node: Record?, detail: string): never
	local location = if node ~= nil and type(node.location) == "string" then node.location else "unknown"
	error(setmetatable({
		code = code,
		location = location,
		detail = detail,
	}, FrontendDiagnostic), 0)
end

local function expectRecord(value: any, code: string, detail: string): Record
	if type(value) ~= "table" then
		diagnostic(code, nil, detail)
	end
	return value :: Record
end

local function expectArray(value: any, node: Record, field: string): { any }
	if type(value) ~= "table" then
		diagnostic("malformed_ast", node, `expected array field {field}`)
	end
	return value :: { any }
end

local function localKey(localNode: Record): string
	if localNode.type ~= "AstLocal" or type(localNode.location) ~= "string" then
		diagnostic("malformed_local_identity", localNode, "local declaration is missing its source location")
	end
	return localNode.location
end

local function localName(localNode: Record): string
	if type(localNode.name) ~= "string" or localNode.name == "" then
		diagnostic("malformed_local_identity", localNode, "local declaration is missing its name")
	end
	return localNode.name
end

local function recoveredLocalName(state: FrontendState, localNode: Record): string
	return state.target_recovery.recovered_binding_names[localKey(localNode)] or localName(localNode)
end

local function nodeTag(node: Record): string
	if type(node.type) ~= "string" then
		diagnostic("malformed_ast", node, "AST node is missing its type tag")
	end
	return node.type
end

local function evidenceFor(state: FrontendState, node: Record): { number }
	local location = if type(node.location) == "string" then node.location else "unknown"
	local key = `{state.options.source_name}:{location}`
	local evidence = state.evidence_by_location[key]
	if evidence == nil then
		evidence = state.builder:addEvidence("source_span", `source:{key}`)
		state.evidence_by_location[key] = evidence
	end
	return { evidence }
end

local function instructionOptions(state: FrontendState, node: Record, effects: Record, additionalEvidence: { number }?): Record
	local evidence = evidenceFor(state, node)
	if additionalEvidence ~= nil then
		for _, evidenceId in additionalEvidence do
			if not table.find(evidence, evidenceId) then
				table.insert(evidence, evidenceId)
			end
		end
	end
	table.sort(evidence)
	return {
		effects = effects,
		evidence = evidence,
	}
end

local function scalarResult(
	context: FunctionContext,
	node: Record,
	operation: Record,
	valueType: Record,
	nameHint: string?,
	effects: Record
): ValueRef
	local _, results = context.frontend.builder:addInstruction(
		context.block,
		operation,
		{ { type = valueType, name_hint = nameHint } },
		instructionOptions(context.frontend, node, effects)
	)
	return { id = results[1], type = valueType }
end

local function bindLocal(context: FunctionContext, localNode: Record, binding: Binding)
	local key = localKey(localNode)
	if context.bindings[key] ~= nil then
		diagnostic("duplicate_local_identity", localNode, `local {localName(localNode)} was bound twice`)
	end
	context.bindings[key] = binding
end

local function findBinding(context: FunctionContext, localNode: Record): (Binding?, FunctionContext?)
	local key = localKey(localNode)
	local current: FunctionContext? = context
	while current ~= nil do
		local binding = current.bindings[key]
		if binding ~= nil then
			return binding, current
		end
		current = current.parent
	end
	return nil, nil
end

local function captureBinding(context: FunctionContext, localNode: Record, outer: Binding): Binding
	local state = context.frontend
	local evidence = evidenceFor(state, localNode)
	if outer.kind == "value" then
		local outerValue = outer.value
		if outerValue == nil then
			diagnostic("malformed_binding", localNode, "value binding has no value identity")
		end
		local value = outerValue :: ValueRef
		local capturedValue = state.builder:addValueCapture(context.id, outer.type, outer.name, evidence)
		table.insert(context.capture_bindings, LifterIR.CaptureBinding.value(value.id))
		return {
			kind = "value",
			value = { id = capturedValue, type = outer.type, intrinsic = value.intrinsic },
			type = outer.type,
			name = outer.name,
		}
	end

	local outerPlace = outer.place
	if outerPlace == nil then
		diagnostic("malformed_binding", localNode, "place binding has no place identity")
	end
	local place = outerPlace :: number
	local capturedPlace = state.builder:addPlaceCapture(context.id, outer.type, outer.name, evidence)
	table.insert(context.capture_bindings, LifterIR.CaptureBinding.place(place))
	return {
		kind = "place",
		place = capturedPlace,
		type = outer.type,
		name = outer.name,
	}
end

local function resolveLocalBinding(context: FunctionContext, localNode: Record): Binding
	local binding, owner = findBinding(context, localNode)
	if binding == nil or owner == nil then
		diagnostic("unresolved_local_identity", localNode, `local {localName(localNode)} has no lexical binding`)
	end
	local resolvedBinding = binding :: Binding
	local resolvedOwner = owner :: FunctionContext
	if resolvedOwner == context then
		return resolvedBinding
	end

	local parent = context.parent
	if parent == nil then
		diagnostic("invalid_capture_owner", localNode, "entry function cannot capture a local")
	end
	local parentBinding = resolveLocalBinding(parent :: FunctionContext, localNode)
	local captured = captureBinding(context, localNode, parentBinding)
	context.bindings[localKey(localNode)] = captured
	return captured
end

local function materializeBinding(
	context: FunctionContext,
	node: Record,
	binding: Binding,
	additionalEvidence: { number }?
): ValueRef
	if binding.kind == "value" then
		local value = binding.value
		if value == nil then
			diagnostic("malformed_binding", node, "value binding has no value identity")
		end
		return value :: ValueRef
	end
	local place = binding.place
	if place == nil then
		diagnostic("malformed_binding", node, "place binding has no place identity")
	end
	local _, results = context.frontend.builder:addInstruction(
		context.block,
		LifterIR.Operation.placeRead(place :: number),
		{ { type = binding.type, name_hint = binding.name } },
		instructionOptions(context.frontend, node, LifterIR.Effects.placeRead(), additionalEvidence)
	)
	return { id = results[1], type = binding.type }
end

local targetRecoveryLowerer = AstTargetRecovery.new({
	diagnostic = diagnostic,
	local_key = localKey,
	resolve_local_binding = function(context: FunctionContext, localNode: Record): Binding
		return resolveLocalBinding(context, localNode)
	end,
	materialize_binding = function(
		context: FunctionContext,
		node: Record,
		binding: Binding,
		additionalEvidence: { number }?
	): ValueRef
		return materializeBinding(context, node, binding, additionalEvidence)
	end,
	instruction_options = instructionOptions,
	evidence_for = evidenceFor,
})

local lowerFunctionExpression: (FunctionContext, Record, string?) -> ValueRef
local lowerStatement: (FunctionContext, Record) -> ()
local lowerStatementBlock: (FunctionContext, Record, boolean) -> ()
local bindDeclaredLocal: (FunctionContext, Record, Record, ValueRef) -> ()
local lowerValueList: (FunctionContext, { any }, number, { string }, Record, string, { Record }?) -> any
local expressionLowerer: any

local iterationLowerer = AstIteration.new({
	diagnostic = diagnostic,
	expect_record = expectRecord,
	evidence_for = evidenceFor,
	lower_expression = function(context: FunctionContext, node: Record, nameHint: string?): any
		return expressionLowerer:lower(context, node, nameHint)
	end,
	lower_statement_block = function(context: FunctionContext, node: Record, finalizeAtEnd: boolean)
		return lowerStatementBlock(context, node, finalizeAtEnd)
	end,
	bind_declared_local = function(context: FunctionContext, node: Record, localNode: Record, value: ValueRef)
		return bindDeclaredLocal(context, node, localNode, value)
	end,
	scalar_result = scalarResult,
	instruction_options = instructionOptions,
	lower_value_list = function(
		context: FunctionContext,
		expressionNodes: { any },
		targetCount: number,
		nameHints: { string },
		ownerNode: Record,
		malformedCode: string
	): any
		return lowerValueList(context, expressionNodes, targetCount, nameHints, ownerNode, malformedCode)
	end,
})

local controlLowerer = AstControl.new({
	diagnostic = diagnostic,
	expect_record = expectRecord,
	evidence_for = evidenceFor,
	lower_expression = function(context: FunctionContext, node: Record, nameHint: string?): any
		return expressionLowerer:lower(context, node, nameHint)
	end,
	lower_statement = function(context: FunctionContext, node: Record)
		return lowerStatement(context, node)
	end,
	lower_statement_block = function(context: FunctionContext, node: Record, finalizeAtEnd: boolean)
		return lowerStatementBlock(context, node, finalizeAtEnd)
	end,
})

expressionLowerer = AstExpressions.new({
	diagnostic = diagnostic,
	expect_record = expectRecord,
	expect_array = expectArray,
	node_tag = nodeTag,
	scalar_result = scalarResult,
	instruction_options = instructionOptions,
	add_terminator_evidence = function(context: FunctionContext, node: Record, additionalEvidence: { number }?)
		local options = instructionOptions(context.frontend, node, LifterIR.Effects.dynamicCall(), additionalEvidence)
		context.frontend.builder:addBlockEvidence(context.block, options.evidence)
	end,
	resolve_target_recovery = function(context: FunctionContext, node: Record): any?
		return targetRecoveryLowerer:resolutionAt(context.frontend.target_recovery, node)
	end,
	lower_target_recovery_origin = function(context: FunctionContext, node: Record, resolution: Record): ValueRef
		return targetRecoveryLowerer:lowerOrigin(context, node, resolution :: any) :: ValueRef
	end,
	mark_target_recovery_resolution_used = function(context: FunctionContext, node: Record)
		targetRecoveryLowerer:markResolutionUsed(context.frontend.target_recovery, node)
	end,
	add_target_recovery_obligation = function(context: FunctionContext, node: Record, subject: Record)
		targetRecoveryLowerer:addObligation(context, node, subject)
	end,
	resolve_local = function(context: FunctionContext, node: Record, localNode: Record): ValueRef
		return materializeBinding(context, node, resolveLocalBinding(context, localNode), nil)
	end,
	-- The left operand of a binary operator that names, through groups and type assertions, a place
	-- of the current function is read at the operator, after the right operand ran (Luau's register
	-- operand); a value binding emits nothing and a captured place is read in order, as an upvalue.
	defer_register_local = function(context: FunctionContext, node: Record): (() -> ValueRef)?
		local operand = node
		while nodeTag(operand) == "AstExprGroup" or nodeTag(operand) == "AstExprTypeAssertion" do
			operand = expectRecord(operand.expr, "malformed_group", "operand wrapper is missing its expression")
		end
		if nodeTag(operand) ~= "AstExprLocal" then
			return nil
		end
		local localNode = expectRecord(operand["local"], "malformed_local_expression", "local expression has no declaration identity")
		local binding = resolveLocalBinding(context, localNode)
		if binding.kind ~= "place" or binding.place == nil then
			return nil
		end
		local placeRecord = context.frontend.builder.program.places[(binding.place :: number) + 1]
		if placeRecord == nil or placeRecord.origin.capture ~= nil then
			return nil
		end
		return function(): ValueRef
			return materializeBinding(context, operand, binding, nil)
		end
	end,
	resolve_intrinsic_alias = function(context: FunctionContext, localNode: Record): any?
		local binding = resolveLocalBinding(context, localNode)
		if binding.kind == "value" and binding.value ~= nil then
			return binding.value.intrinsic
		end
		return nil
	end,
	lower_function = function(context: FunctionContext, node: Record, nameHint: string?): ValueRef
		return lowerFunctionExpression(context, node, nameHint)
	end,
	lower_short_circuit = function(context: FunctionContext, node: Record, nameHint: string?): any
		return controlLowerer:lowerShortCircuit(context, node, nameHint)
	end,
	lower_if_expression = function(context: FunctionContext, node: Record, nameHint: string?): any
		return controlLowerer:lowerIfExpression(context, node, nameHint)
	end,
})

local function lowerExpression(context: FunctionContext, node: Record, nameHint: string?): any
	return expressionLowerer:lower(context, node, nameHint)
end

local function lowerOpenExpression(context: FunctionContext, node: Record): any
	return expressionLowerer:lowerOpen(context, node)
end

local function lowerCall(context: FunctionContext, node: Record, resultCount: number): any
	return expressionLowerer:lowerCall(context, node, resultCount)
end
local function lowerReturn(context: FunctionContext, node: Record)
	local expressions = expectArray(node.list, node, "list")
	local values = {}
	local scalarCount = #expressions
	local openPack: number? = nil
	local openExpression: Record? = nil
	if scalarCount > 0 then
		local lastExpression = expectRecord(expressions[scalarCount], "malformed_return", "return expression is not an AST node")
		local lastTag = nodeTag(lastExpression)
		if lastTag == "AstExprCall" or lastTag == "AstExprVarargs" then
			openExpression = lastExpression
			scalarCount -= 1
		end
	end
	for index = 1, scalarCount do
		local valueOutcome = lowerExpression(
			context,
			expectRecord(expressions[index], "malformed_return", "return expression is not an AST node"),
			nil
		)
		if valueOutcome.kind == "terminated" then
			return
		end
		table.insert(values, valueOutcome.value.id)
	end
	if openExpression ~= nil then
		local openOutcome = lowerOpenExpression(context, openExpression)
		if openOutcome.kind == "terminated" then
			return
		end
		openPack = openOutcome.pack
	end
	if openPack ~= nil then
		if #values == 0 then
			context.frontend.builder:finalizeBlock(context.block, LifterIR.Terminator.returnPack(openPack))
		else
			context.frontend.builder:finalizeBlock(context.block, LifterIR.Terminator.returnExpanded(values, openPack))
		end
	else
		context.frontend.builder:finalizeBlock(context.block, LifterIR.Terminator.returnValues(values))
	end
	context.terminated = true
end

lowerValueList = function(
	context: FunctionContext,
	expressionNodes: { any },
	targetCount: number,
	nameHints: { string },
	ownerNode: Record,
	malformedCode: string,
	targets: { Record }?
): { any }
	local results: { any } = {}
	local scalarCount = #expressionNodes
	local openExpression: Record? = nil
	if scalarCount > 0 then
		local lastExpression = expectRecord(expressionNodes[scalarCount], malformedCode, "value-list member is not an AST node")
		local lastTag = nodeTag(lastExpression)
		if lastTag == "AstExprCall" or lastTag == "AstExprVarargs" then
			openExpression = lastExpression
			scalarCount -= 1
		end
	end

	for index = 1, scalarCount do
		local valueNode = expectRecord(expressionNodes[index], malformedCode, "value-list member is not an AST node")
		local deferredValue = nil
		if targets ~= nil and index <= targetCount then
			local target = targets[index]
			if target ~= nil and target.kind == "table" then
				deferredValue = expressionLowerer.host.defer_register_local(context, valueNode)
			end
		end
		if deferredValue ~= nil then
			if #results < targetCount then
				table.insert(results, deferredValue)
			end
		else
			local valueOutcome = lowerExpression(
				context,
				valueNode,
				if index <= targetCount then nameHints[index] else nil
			)
			if valueOutcome.kind == "terminated" then
				return valueOutcome
			end
			if #results < targetCount then
				table.insert(results, valueOutcome.value)
			end
		end
	end

	local remaining = targetCount - #results
	if openExpression ~= nil then
		if remaining > 0 then
			local openOutcome = lowerOpenExpression(context, openExpression)
			if openOutcome.kind == "terminated" then
				return openOutcome
			end
			local specs = {}
			local adjustedTypes = {}
			for index = 1, remaining do
				local resultType = LifterIR.Types.dynamic()
				if openOutcome.exact_types ~= nil then
					resultType = openOutcome.exact_types[index] or LifterIR.Types.nilValue()
				end
				table.insert(adjustedTypes, resultType)
				table.insert(specs, {
					type = resultType,
					name_hint = nameHints[#results + index],
				})
			end
			local _, adjusted = context.frontend.builder:addInstruction(
				context.block,
				LifterIR.Operation.adjustPack(openOutcome.pack),
				specs,
				instructionOptions(context.frontend, openExpression, LifterIR.Effects.pure())
			)
			for index, valueId in adjusted do
				table.insert(results, { id = valueId, type = adjustedTypes[index] })
			end
		elseif nodeTag(openExpression) == "AstExprCall" then
			local callOutcome = lowerCall(context, openExpression, 0)
			if callOutcome.kind == "terminated" then
				return callOutcome
			end
		end
	end

	while #results < targetCount do
		local index = #results + 1
		table.insert(results, scalarResult(
			context,
			ownerNode,
			LifterIR.Operation.constant(LifterIR.Literal.nilValue()),
			LifterIR.Types.nilValue(),
			nameHints[index],
			LifterIR.Effects.pure()
		))
	end
	return Outcome.value(results)
end

bindDeclaredLocal = function(context: FunctionContext, node: Record, localNode: Record, value: ValueRef)
	local name = recoveredLocalName(context.frontend, localNode)
	if context.frontend.mutable_locals[localKey(localNode)] then
		local placeType = LifterIR.Types.dynamic()
		local place: number
		if #context.loop_stack > 0 then
			place = context.frontend.builder:addAllocatedPlace(
				context.block,
				value.id,
				placeType,
				name,
				evidenceFor(context.frontend, localNode)
			)
		else
			place = context.frontend.builder:addLocalPlace(
				context.id,
				placeType,
				name,
				evidenceFor(context.frontend, localNode)
			)
			context.frontend.builder:addInstruction(
				context.block,
				LifterIR.Operation.placeWrite(place, value.id),
				{},
				instructionOptions(context.frontend, node, LifterIR.Effects.placeWrite())
			)
		end
		bindLocal(context, localNode, {
			kind = "place",
			place = place,
			type = placeType,
			name = name,
		})
	else
		bindLocal(context, localNode, {
			kind = "value",
			value = value,
			type = value.type,
			name = name,
		})
	end
end

local function lowerLocal(context: FunctionContext, node: Record)
	local variableNodes = expectArray(node.vars, node, "vars")
	local expressionNodes = expectArray(node.values, node, "values")
	local locals = {}
	local names = {}
	for _, variableValue in variableNodes do
		local localNode = expectRecord(variableValue, "malformed_local_declaration", "local declaration variable is not an AST local")
		table.insert(locals, localNode)
		table.insert(names, recoveredLocalName(context.frontend, localNode))
	end
	local valuesOutcome = lowerValueList(context, expressionNodes, #locals, names, node, "malformed_local_declaration")
	if valuesOutcome.kind == "terminated" then
		return
	end
	local values = valuesOutcome.value
	for index, localNode in locals do
		bindDeclaredLocal(context, node, localNode, values[index])
	end
end

local function lowerLocalFunction(context: FunctionContext, node: Record)
	local localNode = expectRecord(node.name, "malformed_local_function", "local function is missing its lexical identity")
	local functionNode = expectRecord(node.func, "malformed_local_function", "local function is missing its function expression")
	local name = recoveredLocalName(context.frontend, localNode)
	local placeType = if #context.loop_stack > 0 or context.frontend.reassigned_locals[localKey(localNode)]
		then LifterIR.Types.dynamic()
		else LifterIR.Types.functionValue()
	local place: number
	if #context.loop_stack > 0 then
		local empty = scalarResult(
			context,
			node,
			LifterIR.Operation.constant(LifterIR.Literal.nilValue()),
			LifterIR.Types.nilValue(),
			name,
			LifterIR.Effects.pure()
		)
		place = context.frontend.builder:addAllocatedPlace(
			context.block,
			empty.id,
			placeType,
			name,
			evidenceFor(context.frontend, localNode)
		)
	else
		place = context.frontend.builder:addLocalPlace(
			context.id,
			placeType,
			name,
			evidenceFor(context.frontend, localNode)
		)
	end
	bindLocal(context, localNode, {
		kind = "place",
		place = place,
		type = placeType,
		name = name,
	})
	local closureOutcome = lowerExpression(context, functionNode, name)
	if closureOutcome.kind == "terminated" then
		return
	end
	local closure = closureOutcome.value
	context.frontend.builder:addInstruction(
		context.block,
		LifterIR.Operation.placeWrite(place, closure.id),
		{},
		instructionOptions(context.frontend, node, LifterIR.Effects.placeWrite())
	)
end

local function prepareAssignmentTarget(context: FunctionContext, target: Record, deferTarget: boolean?): Record
	local targetTag = nodeTag(target)
	if targetTag == "AstExprLocal" then
		local localNode = expectRecord(target["local"], "malformed_assignment", "local assignment has no declaration identity")
		local binding = resolveLocalBinding(context, localNode)
		if binding.kind ~= "place" or binding.place == nil then
			diagnostic("mutable_analysis_mismatch", target, `assigned local {binding.name} was not represented as a place`)
		end
		return Outcome.value({ kind = "local", binding = binding })
	elseif targetTag == "AstExprIndexExpr" or targetTag == "AstExprIndexName" then
		local addressOutcome = expressionLowerer:lowerIndexAddress(context, target, deferTarget)
		if addressOutcome.kind == "terminated" then
			return addressOutcome
		end
		return Outcome.value({
			kind = "table",
			table_value = addressOutcome.value.table_value,
			key = addressOutcome.value.key,
			read_table = addressOutcome.value.read_table,
			read_key = addressOutcome.value.read_key,
		})
	elseif targetTag == "AstExprGlobal" then
		if type(target.global) ~= "string" or target.global == "" then
			diagnostic("malformed_global_assignment", target, "global assignment target has no name")
		end
		return Outcome.value({ kind = "global", name = target.global })
	end
	return diagnostic("unsupported_assignment_target", target, `assignment target node {targetTag} is not supported`)
end

-- A table target's register-local base or key (read_table, read_key) is read where Luau reads its
-- register: at the store, and once more for a compound assignment's current value
-- in the order Luau evaluates them.
local function tableTargetOperands(target: Record): (ValueRef, ValueRef)
	local tableValue = if target.read_table ~= nil then target.read_table() else target.table_value
	local keyValue = if target.read_key ~= nil then target.read_key() else target.key
	return tableValue, keyValue
end

local function writeAssignmentTarget(context: FunctionContext, node: Record, target: Record, value: ValueRef)
	if target.kind == "local" then
		local binding = target.binding :: Binding
		context.frontend.builder:addInstruction(
			context.block,
			LifterIR.Operation.placeWrite(binding.place :: number, value.id),
			{},
			instructionOptions(context.frontend, node, LifterIR.Effects.placeWrite())
		)
	elseif target.kind == "table" then
		local tableValue, keyValue = tableTargetOperands(target)
		context.frontend.builder:addInstruction(
			context.block,
			LifterIR.Operation.tableSet(tableValue.id, keyValue.id, value.id),
			{},
			instructionOptions(context.frontend, node, LifterIR.Effects.semanticTableWrite())
		)
	elseif target.kind == "global" then
		context.frontend.builder:addInstruction(
			context.block,
			LifterIR.Operation.environmentSet(LifterIR.EnvironmentTarget.ambient(), target.name, value.id),
			{},
			instructionOptions(context.frontend, node, LifterIR.Effects.semanticTableWrite())
		)
	else
		diagnostic("malformed_assignment_target", node, `prepared assignment target has unknown kind {tostring(target.kind)}`)
	end
end

local function readAssignmentTarget(context: FunctionContext, node: Record, target: Record): ValueRef
	if target.kind == "local" then
		return materializeBinding(context, node, target.binding :: Binding, nil)
	elseif target.kind == "table" then
		local tableValue, keyValue = tableTargetOperands(target)
		return scalarResult(
			context,
			node,
			LifterIR.Operation.tableGet(tableValue.id, keyValue.id),
			LifterIR.Types.dynamic(),
			"compound_current",
			LifterIR.Effects.semanticTableRead()
		)
	elseif target.kind == "global" then
		return scalarResult(
			context,
			node,
			LifterIR.Operation.environmentGet(LifterIR.EnvironmentTarget.ambient(), target.name),
			LifterIR.Types.dynamic(),
			target.name,
			LifterIR.Effects.semanticTableRead()
		)
	end
	return diagnostic("malformed_assignment_target", node, `prepared compound target has unknown kind {tostring(target.kind)}`)
end

local function lowerFunctionStatement(context: FunctionContext, node: Record)
	local targetNode = expectRecord(node.name, "malformed_function_statement", "function statement is missing its assignment target")
	local functionNode = expectRecord(node.func, "malformed_function_statement", "function statement is missing its function expression")
	local targetTag = nodeTag(targetNode)
	local nameHint = if targetTag == "AstExprGlobal" and type(targetNode.global) == "string"
		then targetNode.global
		else if targetTag == "AstExprIndexName" and type(targetNode.index) == "string"
			then targetNode.index
			else "function"
	local closureOutcome = lowerExpression(context, functionNode, nameHint)
	if closureOutcome.kind == "terminated" then
		return
	end
	local targetOutcome = prepareAssignmentTarget(context, targetNode)
	if targetOutcome.kind == "terminated" then
		return
	end
	writeAssignmentTarget(context, node, targetOutcome.value, closureOutcome.value)
end

local function lowerAssignment(context: FunctionContext, node: Record)
	local targetNodes = expectArray(node.vars, node, "vars")
	local expressionNodes = expectArray(node.values, node, "values")
	local targets = {}
	local names = {}
	for index, targetValue in targetNodes do
		local targetNode = expectRecord(targetValue, "malformed_assignment", "assignment target is not an AST node")
		local targetOutcome = prepareAssignmentTarget(context, targetNode, true)
		if targetOutcome.kind == "terminated" then
			return
		end
		table.insert(targets, targetOutcome.value)
		table.insert(names, `assigned_{index}`)
	end
	local valuesOutcome = lowerValueList(context, expressionNodes, #targets, names, node, "malformed_assignment", targets)
	if valuesOutcome.kind == "terminated" then
		return
	end
	local values = valuesOutcome.value
	-- Luau stores through a register-local base or key as it is after every value ran and before the
	-- statement assigns any of its locals, so every deferred read comes before the first write.
	for index, target in targets do
		if target.kind == "table" then
			local tableValue, keyValue = tableTargetOperands(target)
			targets[index] = { kind = "table", table_value = tableValue, key = keyValue }
			local deferredValue = values[index]
			if type(deferredValue) == "function" then
				values[index] = deferredValue()
			end
		end
	end
	for index, target in targets do
		writeAssignmentTarget(context, node, target, values[index])
	end
end

local function lowerCompoundAssignment(context: FunctionContext, node: Record)
	local targetNode = expectRecord(node.var, "malformed_compound_assignment", "compound assignment is missing its target")
	local targetOutcome = prepareAssignmentTarget(context, targetNode, true)
	if targetOutcome.kind == "terminated" then
		return
	end
	local target = targetOutcome.value
	local operatorName = expressionLowerer:compoundOperatorName(node)
	local current: ValueRef? = nil
	if target.kind ~= "local" or operatorName == "Concat" then
		current = readAssignmentTarget(context, targetNode, target)
	end
	local rightOutcome = lowerExpression(
		context,
		expectRecord(node.value, "malformed_compound_assignment", "compound assignment is missing its value"),
		nil
	)
	if rightOutcome.kind == "terminated" then
		return
	end
	if current == nil then
		current = readAssignmentTarget(context, targetNode, target)
	end
	local result = expressionLowerer:lowerBinaryValues(context, node, operatorName, current, rightOutcome.value, "compound_result")
	writeAssignmentTarget(context, node, target, result)
end

lowerStatement = function(context: FunctionContext, statement: Record)
	local tag = nodeTag(statement)
	if tag == "AstStatLocal" then
		lowerLocal(context, statement)
	elseif tag == "AstStatLocalFunction" then
		lowerLocalFunction(context, statement)
	elseif tag == "AstStatFunction" then
		lowerFunctionStatement(context, statement)
	elseif tag == "AstStatAssign" then
		lowerAssignment(context, statement)
	elseif tag == "AstStatCompoundAssign" then
		lowerCompoundAssignment(context, statement)
	elseif tag == "AstStatIf" then
		controlLowerer:lowerIf(context, statement)
	elseif tag == "AstStatWhile" then
		controlLowerer:lowerWhile(context, statement)
	elseif tag == "AstStatRepeat" then
		controlLowerer:lowerRepeat(context, statement)
	elseif tag == "AstStatFor" then
		iterationLowerer:lowerNumericFor(context, statement)
	elseif tag == "AstStatForIn" then
		iterationLowerer:lowerGenericFor(context, statement)
	elseif tag == "AstStatContinue" then
		controlLowerer:lowerLoopTransfer(context, statement, true)
	elseif tag == "AstStatBreak" then
		controlLowerer:lowerLoopTransfer(context, statement, false)
	elseif tag == "AstStatReturn" then
		lowerReturn(context, statement)
	elseif tag == "AstStatBlock" then
		lowerStatementBlock(context, statement, false)
	elseif tag == "AstStatTypeAlias" or tag == "AstStatTypeFunction" or tag == "AstStatDeclareClass" or tag == "AstStatDeclareGlobal" or
		tag == "AstStatDeclareFunction" or tag == "AstStatDeclareExternType"
	then
		-- Type and declaration statements have no runtime behavior.
		return
	elseif tag == "AstStatError" then
		diagnostic("malformed_source_statement", statement, "parser recovery statement cannot be admitted as runtime semantics")
	elseif tag == "AstStatExpr" then
		local expression = expectRecord(statement.expr, "malformed_expression_statement", "expression statement is missing its expression")
		if nodeTag(expression) ~= "AstExprCall" then
			diagnostic("unsupported_expression_statement", statement, "only call expressions are valid standalone expressions")
		end
		local callOutcome = lowerCall(context, expression, 0)
		if callOutcome.kind ~= "effect" and callOutcome.kind ~= "terminated" then
			diagnostic("malformed_call_result", expression, "discarded call did not produce an effect outcome")
		end
	else
		diagnostic("unsupported_statement", statement, `statement node {tag} is not supported by this frontend slice`)
	end
end

lowerStatementBlock = function(context: FunctionContext, block: Record, finalizeAtEnd: boolean)
	if nodeTag(block) ~= "AstStatBlock" then
		diagnostic("malformed_block", block, "expected an AstStatBlock")
	end
	for _, statementNode in expectArray(block.body, block, "body") do
		local statement = expectRecord(statementNode, "malformed_statement", "block member is not an AST node")
		if context.terminated then
			targetRecoveryLowerer:markDead(context.frontend.target_recovery, statement)
		else
			lowerStatement(context, statement)
		end
	end
	if not context.terminated and finalizeAtEnd then
		context.frontend.builder:finalizeBlock(context.block, LifterIR.Terminator.returnValues({}))
		context.terminated = true
	end
end

lowerFunctionExpression = function(parent: FunctionContext, node: Record, nameHint: string?): ValueRef
	local state = parent.frontend
	local variadicValue, variadicProblem = AstExpressionScalar.functionIsVariadic(node)
	if variadicProblem ~= nil then
		diagnostic(variadicProblem.code, variadicProblem.node, variadicProblem.detail)
	end
	local isVariadic = variadicValue :: boolean
	local functionId = state.builder:reserveFunction({
		name_hint = nameHint or "closure",
		lexical_parent = parent.id,
		is_variadic = isVariadic,
		evidence = evidenceFor(state, node),
	})
	local block = state.builder:reserveBlock(functionId, {
		name_hint = "entry",
		evidence = evidenceFor(state, expectRecord(node.body, "malformed_function", "function is missing its body")),
	})
	state.builder:setFunctionEntry(functionId, block)
	local context: FunctionContext = {
		frontend = state,
		id = functionId,
		parent = parent,
		block = block,
		bindings = {},
		capture_bindings = {},
		vararg_pack = nil,
		loop_stack = {},
		terminated = false,
	}
	local parameters = {}
	if type(node.self) == "table" then
		table.insert(parameters, node.self)
	end
	for _, argumentNode in expectArray(node.args, node, "args") do
		table.insert(parameters, argumentNode)
	end
	for _, argumentNode in parameters do
		local argument = expectRecord(argumentNode, "malformed_function_parameter", "function parameter is not a local declaration")
		local name = recoveredLocalName(state, argument)
		local valueId = state.builder:addParameter(functionId, LifterIR.Types.dynamic(), name)
		if state.mutable_locals[localKey(argument)] then
			local placeType = LifterIR.Types.dynamic()
			local place = state.builder:addLocalPlace(functionId, placeType, name, evidenceFor(state, argument))
			state.builder:addInstruction(
				block,
				LifterIR.Operation.placeWrite(place, valueId),
				{},
				instructionOptions(state, argument, LifterIR.Effects.placeWrite())
			)
			bindLocal(context, argument, {
				kind = "place",
				place = place,
				type = placeType,
				name = name,
			})
		else
			bindLocal(context, argument, {
				kind = "value",
				value = { id = valueId, type = LifterIR.Types.dynamic() },
				type = LifterIR.Types.dynamic(),
				name = name,
			})
		end
	end
	if isVariadic then
		context.vararg_pack = state.builder:addVarargPack(functionId, evidenceFor(state, node))
	end
	lowerStatementBlock(context, expectRecord(node.body, "malformed_function", "function is missing its body"), true)
	state.builder:finalizeFunction(functionId)
	return scalarResult(
		parent,
		node,
		LifterIR.Operation.makeClosure(functionId, context.capture_bindings),
		LifterIR.Types.functionValue(),
		nameHint,
		LifterIR.Effects.pure()
	)
end

local function admitOptionsArray(value: any, label: string, limit: number): { any }
	local ok, admitted = pcall(RecoveryAdmission.expectDenseArray, value, label, limit)
	if not ok then
		diagnostic("invalid_options", nil, tostring(admitted))
	end
	return admitted :: { any }
end

local function liftUnchecked(document: Record, options: Options): Record
	if options.program_id == "" then
		diagnostic("invalid_options", nil, "program_id must not be empty")
	end
	if options.source_name == "" then
		diagnostic("invalid_options", nil, "source_name must not be empty")
	end
	local programObligations = if options.program_obligations ~= nil
		then admitOptionsArray(
			options.program_obligations,
			"program_obligations",
			RecoveryAdmission.maxCollectionItems
		) :: { ProgramObligation }
		else nil
	local intrinsicBindings = if options.intrinsic_bindings ~= nil
		then admitOptionsArray(
			options.intrinsic_bindings,
			"intrinsic_bindings",
			RecoveryAdmission.maxIntrinsicBindings
		) :: { IntrinsicBinding }
		else nil
	local root = expectRecord(document.root, "malformed_document", "luau-ast document is missing its root block")
	local inspection, astProblem = AstAdmission.inspect(document)
	if astProblem ~= nil then
		diagnostic(astProblem.code, astProblem.node, astProblem.detail)
	end
	local admittedSourceText: string? = nil
	if options.source_text ~= nil then
		local ok, value = pcall(AstAdmission.expectSourceBytes, options.source_text, "source_text")
		if not ok then
			diagnostic("invalid_options", root, tostring(value))
		end
		admittedSourceText = value :: string
	end
	local verifiedTargetRecovery: TargetRecovery.Verified? = nil
	if options.target_recovery ~= nil then
		if admittedSourceText == nil then
			diagnostic("invalid_options", root, "target recovery requires the exact source text")
		end
		local ok, value = pcall(TargetRecovery.verify, document, admittedSourceText :: string, options.target_recovery :: TargetRecovery.Spec)
		if not ok then
			diagnostic("target_recovery_mismatch", root, tostring(value))
		end
		verifiedTargetRecovery = value :: TargetRecovery.Verified
	end
	local mutableLocals = {}
	for _, localNode in (inspection :: AstAdmission.Inspection).mutable_local_nodes do
		mutableLocals[localKey(localNode)] = true
	end
	local reassignedLocals = {}
	for _, localNode in (inspection :: AstAdmission.Inspection).reassigned_local_nodes do
		reassignedLocals[localKey(localNode)] = true
	end
	local builder = LifterIR.Builder.new(options.program_id)
	local intrinsicEvidenceByPath = {}
	if intrinsicBindings ~= nil then
		for _, binding in intrinsicBindings do
			if type(binding.path) ~= "string" or IntrinsicBindings.kindForPath(binding.path) == nil then
				diagnostic("invalid_options", nil, "intrinsic binding path is not supported")
			end
			if intrinsicEvidenceByPath[binding.path] ~= nil then
				diagnostic("invalid_options", nil, `intrinsic binding {binding.path} was declared twice`)
			end
			local evidence = binding.evidence
			if type(evidence) ~= "table"
				or type(evidence.kind) ~= "string"
				or evidence.kind == ""
				or type(evidence.locator) ~= "string"
				or evidence.locator == ""
				or (evidence.digest ~= nil and (type(evidence.digest) ~= "string" or evidence.digest == ""))
			then
				diagnostic("invalid_options", nil, `intrinsic binding {binding.path} has malformed evidence`)
			end
			intrinsicEvidenceByPath[binding.path] = builder:addEvidence(
				evidence.kind,
				evidence.locator,
				evidence.digest
			)
		end
	end
	local targetRecovery = targetRecoveryLowerer:initialize(builder, root, verifiedTargetRecovery)
	local state: FrontendState = {
		builder = builder,
		options = options,
		evidence_by_location = {},
		intrinsic_evidence_by_path = intrinsicEvidenceByPath,
		target_recovery = targetRecovery,
		mutable_locals = mutableLocals,
		reassigned_locals = reassignedLocals,
	}
	local chunk = builder:reserveFunction({
		name_hint = "chunk",
		is_variadic = true,
		evidence = evidenceFor(state, root),
	})
	local entry = builder:reserveBlock(chunk, { name_hint = "entry", evidence = evidenceFor(state, root) })
	builder:setEntryFunction(chunk)
	builder:setFunctionEntry(chunk, entry)
	local context: FunctionContext = {
		frontend = state,
		id = chunk,
		parent = nil,
		block = entry,
		bindings = {},
		capture_bindings = {},
		vararg_pack = builder:addVarargPack(chunk, evidenceFor(state, root)),
		loop_stack = {},
		terminated = false,
	}
	lowerStatementBlock(context, root, true)
	targetRecoveryLowerer:assertComplete(state.target_recovery, root)
	if programObligations ~= nil then
		for _, obligation in programObligations do
			local obligationEvidence = builder:addEvidence(
				obligation.evidence.kind,
				obligation.evidence.locator,
				obligation.evidence.digest
			)
			builder:addObligation(
				obligation.kind,
				LifterIR.Entity.program(),
				LifterIR.ObligationStatus.open,
				obligation.blocks_profile,
				obligation.detail,
				nil,
				nil,
				{ obligationEvidence }
			)
		end
	end
	builder:finalizeFunction(chunk)
	while true do
		local refined = PlaceDomains.refine(builder.program)
		refined += OperatorDomains.refine(builder.program)
		refined += AstControl.refineBlockParameterDomains(builder.program)
		if refined == 0 then
			break
		end
	end
	return builder:finish()
end

function AstFrontend.tryLift(document: Record, options: Options): LiftResult
	local ok, value = pcall(liftUnchecked, document, options)
	if ok then
		return { program = value :: Record, diagnostics = {} }
	end
	if type(value) == "table" and getmetatable(value :: any) == FrontendDiagnostic then
		return { program = nil, diagnostics = { value :: Diagnostic } }
	end
	error(value, 0)
end

function AstFrontend.formatDiagnostic(value: Diagnostic): string
	return `{value.code} at {value.location}: {value.detail}`
end

return table.freeze(AstFrontend)
