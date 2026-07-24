--!strict

-- Numeric and generalized iteration protocol lowering. These loops carry
-- hidden runtime state that is validated and re-emitted by the Zig backend.

local LifterIR = require("./lifter_ir")

local AstIteration = {}
local IterationLowerer = {}
IterationLowerer.__index = IterationLowerer

type Record = { [string]: any }

type Host = {
	diagnostic: (string, Record, string) -> never,
	expect_record: (any, string, string) -> Record,
	evidence_for: (any, Record) -> { number },
	lower_expression: (any, Record, string) -> any,
	lower_statement_block: (any, Record, boolean) -> (),
	bind_declared_local: (any, Record, Record, any) -> (),
	scalar_result: (any, Record, Record, Record, string, Record) -> any,
	instruction_options: (any, Record, Record) -> Record,
	lower_value_list: (any, { any }, number, { string }, Record, string) -> any,
}

export type Lowerer = typeof(setmetatable({} :: { host: Host }, IterationLowerer))

function AstIteration.new(host: Host): Lowerer
	return setmetatable({ host = host }, IterationLowerer)
end

function IterationLowerer:_branchContext(context: any, block: number): any
	return {
		frontend = context.frontend,
		id = context.id,
		parent = context.parent,
		block = block,
		bindings = context.bindings,
		capture_bindings = context.capture_bindings,
		vararg_pack = context.vararg_pack,
		loop_stack = context.loop_stack,
		terminated = false,
	}
end

function IterationLowerer:lowerNumericFor(context: any, node: Record)
	local host = self.host
	local state = context.frontend
	if type(node.from) ~= "table" then
		host.diagnostic("malformed_numeric_for", node, "numeric for is missing its initial value")
	end
	if type(node.to) ~= "table" then
		host.diagnostic("malformed_numeric_for", node, "numeric for is missing its limit")
	end
	local initialOutcome = host.lower_expression(context, node.from :: Record, "numeric_initial")
	if initialOutcome.kind == "terminated" then
		return
	end
	local limitOutcome = host.lower_expression(context, node.to :: Record, "numeric_limit")
	if limitOutcome.kind == "terminated" then
		return
	end
	local stepValue
	if type(node.step) == "table" then
		local stepOutcome = host.lower_expression(context, node.step :: Record, "numeric_step")
		if stepOutcome.kind == "terminated" then
			return
		end
		stepValue = stepOutcome.value
	else
		stepValue = host.scalar_result(
			context,
			node,
			LifterIR.Operation.constant(LifterIR.Literal.integer("1")),
			LifterIR.Types.integer(),
			"numeric_step",
			LifterIR.Effects.pure()
		)
	end
	local firstTransition = host.scalar_result(
		context,
		node,
		LifterIR.Operation.constant(LifterIR.Literal.boolean(true)),
		LifterIR.Types.boolean(),
		"numeric_initial_transition",
		LifterIR.Effects.pure()
	)
	local laterTransition = host.scalar_result(
		context,
		node,
		LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
		LifterIR.Types.boolean(),
		"numeric_later_transition",
		LifterIR.Effects.pure()
	)

	local headerBlock = state.builder:reserveBlock(context.id, {
		name_hint = "numeric_for_header",
		evidence = host.evidence_for(state, node),
	})
	if type(node.body) ~= "table" then
		host.diagnostic("malformed_numeric_for", node, "numeric for is missing its body")
	end
	local bodyNode = node.body :: Record
	local variableNode = host.expect_record(
		node.var,
		"malformed_numeric_for",
		"numeric for is missing its lexical variable"
	)
	if type(variableNode.name) ~= "string" or variableNode.name == "" then
		host.diagnostic("malformed_numeric_for", variableNode, "numeric-for variable has no name")
	end
	local variableName = variableNode.name :: string
	local bodyBlock = state.builder:reserveBlock(context.id, {
		name_hint = "numeric_for_body",
		evidence = host.evidence_for(state, bodyNode),
	})
	local exitBlock = state.builder:reserveBlock(context.id, {
		name_hint = "numeric_for_exit",
		evidence = host.evidence_for(state, node),
	})

	local controlParameter = state.builder:addBlockParameter(headerBlock, LifterIR.Types.dynamic(), "numeric_control")
	local limitParameter = state.builder:addBlockParameter(headerBlock, LifterIR.Types.dynamic(), "numeric_limit")
	local stepParameter = state.builder:addBlockParameter(headerBlock, LifterIR.Types.dynamic(), "numeric_step")
	local initialParameter = state.builder:addBlockParameter(headerBlock, LifterIR.Types.boolean(), "numeric_initial_transition")
	local loopVariable = state.builder:addBlockParameter(bodyBlock, LifterIR.Types.number(), variableName)

	state.builder:finalizeBlock(
		context.block,
		LifterIR.Terminator.jump(LifterIR.Edge(headerBlock, {
			initialOutcome.value.id,
			limitOutcome.value.id,
			stepValue.id,
			firstTransition.id,
		}))
	)
	local _, transition = state.builder:addInstruction(
		headerBlock,
		LifterIR.Operation.numericForNext(controlParameter, limitParameter, stepParameter, initialParameter),
		{
			{ type = LifterIR.Types.boolean(), name_hint = "numeric_has_value" },
			{ type = LifterIR.Types.number(), name_hint = "numeric_normalized_limit" },
			{ type = LifterIR.Types.number(), name_hint = "numeric_normalized_step" },
			{ type = LifterIR.Types.number(), name_hint = variableName },
		},
		host.instruction_options(state, node, LifterIR.Effects.numericForNext())
	)
	state.builder:finalizeBlock(
		headerBlock,
		LifterIR.Terminator.branch(
			transition[1],
			LifterIR.Edge(bodyBlock, { transition[4] }),
			LifterIR.Edge(exitBlock)
		)
	)

	local bodyContext = self:_branchContext(context, bodyBlock)
	local continueArguments = { transition[4], transition[2], transition[3], laterTransition.id }
	table.insert(bodyContext.loop_stack, {
		continue_block = headerBlock,
		break_block = exitBlock,
		continue_arguments = continueArguments,
	})
	host.bind_declared_local(
		bodyContext,
		node,
		variableNode,
		{ id = loopVariable, type = LifterIR.Types.number() }
	)
	host.lower_statement_block(bodyContext, bodyNode, false)
	table.remove(bodyContext.loop_stack)
	if not bodyContext.terminated then
		state.builder:finalizeBlock(bodyContext.block, LifterIR.Terminator.jump(LifterIR.Edge(headerBlock, continueArguments)))
	end

	context.block = exitBlock
	context.terminated = false
end

function IterationLowerer:lowerGenericFor(context: any, node: Record)
	local host = self.host
	local state = context.frontend
	local variableNodes = node.vars
	if type(variableNodes) ~= "table" or #variableNodes == 0 then
		host.diagnostic("malformed_generic_for", node, "generic for must declare at least one lexical variable")
	end
	local variables = variableNodes :: { any }
	local names = {}
	local locals = {}
	for _, variableValue in variables do
		local localNode = host.expect_record(variableValue, "malformed_generic_for", "generic-for variable is not a lexical local")
		if type(localNode.name) ~= "string" or localNode.name == "" then
			host.diagnostic("malformed_generic_for", localNode, "generic-for variable has no name")
		end
		table.insert(locals, localNode)
		table.insert(names, localNode.name)
	end

	local sourceNodes = node.values
	if type(sourceNodes) ~= "table" then
		host.diagnostic("malformed_generic_for", node, "generic for is missing its iterator expression list")
	end
	local sourceOutcome = host.lower_value_list(
		context,
		sourceNodes :: { any },
		3,
		{ "generic_iterator", "generic_state", "generic_control" },
		node,
		"malformed_generic_for"
	)
	if sourceOutcome.kind == "terminated" then
		return
	end
	local sourceValues = sourceOutcome.value
	local firstTransition = host.scalar_result(
		context,
		node,
		LifterIR.Operation.constant(LifterIR.Literal.boolean(true)),
		LifterIR.Types.boolean(),
		"generic_initial_transition",
		LifterIR.Effects.pure()
	)
	local laterTransition = host.scalar_result(
		context,
		node,
		LifterIR.Operation.constant(LifterIR.Literal.boolean(false)),
		LifterIR.Types.boolean(),
		"generic_later_transition",
		LifterIR.Effects.pure()
	)

	local headerBlock = state.builder:reserveBlock(context.id, {
		name_hint = "generic_for_header",
		evidence = host.evidence_for(state, node),
	})
	local bodyNode = host.expect_record(node.body, "malformed_generic_for", "generic for is missing its body")
	local bodyBlock = state.builder:reserveBlock(context.id, {
		name_hint = "generic_for_body",
		evidence = host.evidence_for(state, bodyNode),
	})
	local exitBlock = state.builder:reserveBlock(context.id, {
		name_hint = "generic_for_exit",
		evidence = host.evidence_for(state, node),
	})
	local iteratorParameter = state.builder:addBlockParameter(headerBlock, LifterIR.Types.dynamic(), "generic_iterator")
	local stateParameter = state.builder:addBlockParameter(headerBlock, LifterIR.Types.dynamic(), "generic_state")
	local controlParameter = state.builder:addBlockParameter(headerBlock, LifterIR.Types.dynamic(), "generic_control")
	local initialParameter = state.builder:addBlockParameter(headerBlock, LifterIR.Types.boolean(), "generic_initial_transition")
	local bodyParameters = {}
	for _, name in names do
		table.insert(bodyParameters, state.builder:addBlockParameter(bodyBlock, LifterIR.Types.dynamic(), name))
	end

	state.builder:finalizeBlock(
		context.block,
		LifterIR.Terminator.jump(LifterIR.Edge(headerBlock, {
			sourceValues[1].id,
			sourceValues[2].id,
			sourceValues[3].id,
			firstTransition.id,
		}))
	)
	local resultSpecs = {
		{ type = LifterIR.Types.boolean(), name_hint = "generic_has_value" },
		{ type = LifterIR.Types.dynamic(), name_hint = "generic_prepared_iterator" },
		{ type = LifterIR.Types.dynamic(), name_hint = "generic_prepared_state" },
	}
	for _, name in names do
		table.insert(resultSpecs, { type = LifterIR.Types.dynamic(), name_hint = name })
	end
	local _, transition = state.builder:addInstruction(
		headerBlock,
		LifterIR.Operation.genericForNext(
			iteratorParameter,
			stateParameter,
			controlParameter,
			initialParameter,
			#locals
		),
		resultSpecs,
		host.instruction_options(state, node, LifterIR.Effects.genericForNext())
	)
	local bodyArguments = {}
	for index = 1, #locals do
		table.insert(bodyArguments, transition[index + 3])
	end
	state.builder:finalizeBlock(
		headerBlock,
		LifterIR.Terminator.branch(
			transition[1],
			LifterIR.Edge(bodyBlock, bodyArguments),
			LifterIR.Edge(exitBlock)
		)
	)

	local bodyContext = self:_branchContext(context, bodyBlock)
	local continueArguments = { transition[2], transition[3], transition[4], laterTransition.id }
	table.insert(bodyContext.loop_stack, {
		continue_block = headerBlock,
		break_block = exitBlock,
		continue_arguments = continueArguments,
	})
	for index, localNode in locals do
		host.bind_declared_local(
			bodyContext,
			node,
			localNode,
			{ id = bodyParameters[index], type = LifterIR.Types.dynamic() }
		)
	end
	host.lower_statement_block(bodyContext, bodyNode, false)
	table.remove(bodyContext.loop_stack)
	if not bodyContext.terminated then
		state.builder:finalizeBlock(bodyContext.block, LifterIR.Terminator.jump(LifterIR.Edge(headerBlock, continueArguments)))
	end

	context.block = exitBlock
	context.terminated = false
end

return table.freeze(AstIteration)
