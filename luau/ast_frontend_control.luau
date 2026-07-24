--!strict

-- Structured CFG lowering for the Luau AST frontend. Lexical ownership and
-- expression semantics are injected by the host to keep this module focused
-- on control topology and edge construction.

local LifterIR = require("./lifter_ir")
local Outcome = require("./ast_frontend_outcome")

local AstControl = {}
local ControlLowerer = {}
ControlLowerer.__index = ControlLowerer

type Record = { [string]: any }

type JoinCandidate = {
	value_type: Record?,
	incoming: number,
	blocked: boolean,
}

type Host = {
	diagnostic: (string, Record, string) -> never,
	expect_record: (any, string, string) -> Record,
	evidence_for: (any, Record) -> { number },
	lower_expression: (any, Record, string?) -> any,
	lower_statement: (any, Record) -> (),
	lower_statement_block: (any, Record, boolean) -> (),
}

export type Lowerer = typeof(setmetatable({} :: { host: Host }, ControlLowerer))

function AstControl.new(host: Host): Lowerer
	return setmetatable({ host = host }, ControlLowerer)
end

local function commonIntrinsicIdentity(left: any, right: any): any?
	local leftIdentity = left.intrinsic
	local rightIdentity = right.intrinsic
	if leftIdentity ~= nil
		and rightIdentity ~= nil
		and leftIdentity.kind == rightIdentity.kind
		and leftIdentity.evidence == rightIdentity.evidence
	then
		return leftIdentity
	end
	return nil
end

local function sameValueType(left: Record, right: Record): boolean
	return left.kind == right.kind and left.bit_width == right.bit_width and left.signed == right.signed
end

local function commonValueType(left: Record, right: Record): Record?
	if sameValueType(left, right) then
		return left
	end
	return nil
end

local function copyValueType(valueType: Record): Record
	return {
		kind = valueType.kind,
		bit_width = valueType.bit_width,
		signed = valueType.signed,
	}
end

local function collectIncomingEdge(program: Record, candidates: { [number]: JoinCandidate }, edge: Record)
	local target = program.blocks[edge.target + 1]
	assert(target ~= nil and target.id == edge.target, `edge targets missing block {edge.target}`)
	assert(#edge.arguments == #target.parameters, `edge to block {edge.target} has inconsistent argument arity`)
	for index, parameterId in target.parameters do
		local candidate = candidates[parameterId]
		if candidate ~= nil then
			candidate.incoming += 1
			local argumentId = edge.arguments[index]
			local argument = program.values[argumentId + 1]
			assert(argument ~= nil and argument.id == argumentId, `edge argument names missing value {argumentId}`)
			if argument.type.kind == "dynamic" then
				candidate.blocked = true
			elseif candidate.value_type == nil then
				candidate.value_type = argument.type
			elseif not sameValueType(candidate.value_type, argument.type) then
				candidate.blocked = true
			end
		end
	end
end

function AstControl.refineBlockParameterDomains(program: Record): number
	local candidates: { [number]: JoinCandidate } = {}
	for _, block in program.blocks do
		for _, parameterId in block.parameters do
			if program.values[parameterId + 1].type.kind == "dynamic" then
				candidates[parameterId] = { value_type = nil, incoming = 0, blocked = false }
			end
		end
	end

	for _, block in program.blocks do
		local jump = block.terminator.jump
		local branch = block.terminator.branch
		if jump ~= nil then
			collectIncomingEdge(program, candidates, jump)
		elseif branch ~= nil then
			collectIncomingEdge(program, candidates, branch.then_edge)
			collectIncomingEdge(program, candidates, branch.else_edge)
		end
	end

	local refined = 0
	for parameterId, candidate in candidates do
		if not candidate.blocked and candidate.incoming > 0 and candidate.value_type ~= nil then
			program.values[parameterId + 1].type = copyValueType(candidate.value_type)
			refined += 1
		end
	end
	return refined
end

local function refineJoinedType(builder: any, result: number, joinedType: Record?): Record
	local resultType = joinedType or LifterIR.Types.dynamic()
	if resultType.kind ~= "dynamic" then
		builder:refineBlockParameterType(result, resultType)
	end
	return resultType
end

function ControlLowerer:_branchContext(context: any, block: number): any
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

function ControlLowerer:lowerShortCircuit(context: any, node: Record, nameHint: string?): any
	local host: Host = self.host
	local state = context.frontend
	local leftNode = host.expect_record(node.left, "malformed_short_circuit", "short-circuit expression is missing its left operand")
	local leftOutcome = host.lower_expression(
		context,
		leftNode,
		nil
	)
	if leftOutcome.kind == "terminated" then
		return leftOutcome
	end
	local left = leftOutcome.value
	local rightNode = host.expect_record(node.right, "malformed_short_circuit", "short-circuit expression is missing its right operand")
	local rightBlock = state.builder:reserveBlock(context.id, {
		name_hint = "logical_right",
		evidence = host.evidence_for(state, rightNode),
	})
	local shortBlock = state.builder:reserveBlock(context.id, {
		name_hint = "logical_short",
		evidence = host.evidence_for(state, node),
	})
	local joinBlock = state.builder:reserveBlock(context.id, {
		name_hint = "logical_join",
		evidence = host.evidence_for(state, node),
	})
	local result = state.builder:addBlockParameter(joinBlock, LifterIR.Types.dynamic(), nameHint or "logical_result")
	local thenTarget = if node.op == "And" then rightBlock else shortBlock
	local elseTarget = if node.op == "And" then shortBlock else rightBlock
	state.builder:finalizeBlock(
		context.block,
		LifterIR.Terminator.branch(left.id, LifterIR.Edge(thenTarget), LifterIR.Edge(elseTarget))
	)

	local rightContext = self:_branchContext(context, rightBlock)
	local rightOutcome = host.lower_expression(rightContext, rightNode, nameHint)
	if rightOutcome.kind ~= "terminated" then
		state.builder:finalizeBlock(rightContext.block, LifterIR.Terminator.jump(LifterIR.Edge(joinBlock, { rightOutcome.value.id })))
	end
	state.builder:finalizeBlock(shortBlock, LifterIR.Terminator.jump(LifterIR.Edge(joinBlock, { left.id })))

	context.block = joinBlock
	context.terminated = false
	local intrinsic = if rightOutcome.kind == "terminated"
		then left.intrinsic
		else commonIntrinsicIdentity(left, rightOutcome.value)
	local joinedType = if rightOutcome.kind == "terminated"
		then left.type
		else commonValueType(left.type, rightOutcome.value.type)
	return Outcome.value({ id = result, type = refineJoinedType(state.builder, result, joinedType), intrinsic = intrinsic })
end

function ControlLowerer:lowerIfExpression(context: any, node: Record, nameHint: string?): any
	local host: Host = self.host
	local state = context.frontend
	local conditionNode = host.expect_record(node.condition, "malformed_if_expression", "if expression is missing its condition")
	local conditionOutcome = host.lower_expression(
		context,
		conditionNode,
		nil
	)
	if conditionOutcome.kind == "terminated" then
		return conditionOutcome
	end
	local condition = conditionOutcome.value
	local trueNode = host.expect_record(node.trueExpr, "malformed_if_expression", "if expression is missing its true value")
	local falseNode = host.expect_record(node.falseExpr, "malformed_if_expression", "if expression is missing its false value")
	local trueBlock = state.builder:reserveBlock(context.id, {
		name_hint = "if_value_true",
		evidence = host.evidence_for(state, trueNode),
	})
	local falseBlock = state.builder:reserveBlock(context.id, {
		name_hint = "if_value_false",
		evidence = host.evidence_for(state, falseNode),
	})
	local joinBlock = state.builder:reserveBlock(context.id, {
		name_hint = "if_value_join",
		evidence = host.evidence_for(state, node),
	})
	local result = state.builder:addBlockParameter(joinBlock, LifterIR.Types.dynamic(), nameHint or "if_result")
	state.builder:finalizeBlock(
		context.block,
		LifterIR.Terminator.branch(condition.id, LifterIR.Edge(trueBlock), LifterIR.Edge(falseBlock))
	)

	local trueContext = self:_branchContext(context, trueBlock)
	local trueOutcome = host.lower_expression(trueContext, trueNode, nameHint)
	local falseContext = self:_branchContext(context, falseBlock)
	local falseOutcome = host.lower_expression(falseContext, falseNode, nameHint)
	if trueOutcome.kind == "terminated" and falseOutcome.kind == "terminated" then
		state.builder:finalizeBlock(joinBlock, LifterIR.Terminator.unreachable())
		context.terminated = true
		return Outcome.terminated()
	end
	if trueOutcome.kind ~= "terminated" then
		state.builder:finalizeBlock(trueContext.block, LifterIR.Terminator.jump(LifterIR.Edge(joinBlock, { trueOutcome.value.id })))
	end
	if falseOutcome.kind ~= "terminated" then
		state.builder:finalizeBlock(falseContext.block, LifterIR.Terminator.jump(LifterIR.Edge(joinBlock, { falseOutcome.value.id })))
	end

	context.block = joinBlock
	context.terminated = false
	local intrinsic
	if trueOutcome.kind == "terminated" then
		intrinsic = falseOutcome.value.intrinsic
	elseif falseOutcome.kind == "terminated" then
		intrinsic = trueOutcome.value.intrinsic
	else
		intrinsic = commonIntrinsicIdentity(trueOutcome.value, falseOutcome.value)
	end
	local joinedType: Record?
	if trueOutcome.kind == "terminated" then
		joinedType = falseOutcome.value.type
	elseif falseOutcome.kind == "terminated" then
		joinedType = trueOutcome.value.type
	else
		joinedType = commonValueType(trueOutcome.value.type, falseOutcome.value.type)
	end
	return Outcome.value({ id = result, type = refineJoinedType(state.builder, result, joinedType), intrinsic = intrinsic })
end

function ControlLowerer:lowerIf(context: any, node: Record)
	local host: Host = self.host
	local state = context.frontend
	local conditionNode = host.expect_record(node.condition, "malformed_if", "if statement is missing its condition")
	local conditionOutcome = host.lower_expression(
		context,
		conditionNode,
		"condition"
	)
	if conditionOutcome.kind == "terminated" then
		return
	end
	local condition = conditionOutcome.value
	local thenNode = host.expect_record(node.thenbody, "malformed_if", "if statement is missing its then body")
	local thenBlock = state.builder:reserveBlock(context.id, {
		name_hint = "then",
		evidence = host.evidence_for(state, thenNode),
	})
	local elseBlock = state.builder:reserveBlock(context.id, {
		name_hint = "else",
		evidence = host.evidence_for(state, if type(node.elsebody) == "table" then node.elsebody else node),
	})
	state.builder:finalizeBlock(
		context.block,
		LifterIR.Terminator.branch(condition.id, LifterIR.Edge(thenBlock), LifterIR.Edge(elseBlock))
	)

	local thenContext = self:_branchContext(context, thenBlock)
	host.lower_statement_block(thenContext, thenNode, false)

	local elseContext = self:_branchContext(context, elseBlock)
	if type(node.elsebody) == "table" then
		local elseNode = node.elsebody :: Record
		if type(elseNode.type) ~= "string" then
			host.diagnostic("malformed_ast", elseNode, "else body is missing its type tag")
		elseif elseNode.type == "AstStatBlock" then
			host.lower_statement_block(elseContext, elseNode, false)
		elseif elseNode.type == "AstStatIf" then
			host.lower_statement(elseContext, elseNode)
		else
			host.diagnostic("unsupported_else_body", elseNode, "else body must be a block or nested if")
		end
	end

	if thenContext.terminated and elseContext.terminated then
		context.terminated = true
		return
	end

	local joinBlock = state.builder:reserveBlock(context.id, {
		name_hint = "join",
		evidence = host.evidence_for(state, node),
	})
	if not thenContext.terminated then
		state.builder:finalizeBlock(thenContext.block, LifterIR.Terminator.jump(LifterIR.Edge(joinBlock)))
	end
	if not elseContext.terminated then
		state.builder:finalizeBlock(elseContext.block, LifterIR.Terminator.jump(LifterIR.Edge(joinBlock)))
	end
	context.block = joinBlock
	context.terminated = false
end

function ControlLowerer:lowerWhile(context: any, node: Record)
	local host: Host = self.host
	local state = context.frontend
	local bodyNode = host.expect_record(node.body, "malformed_while", "while statement is missing its body")
	local headerBlock = state.builder:reserveBlock(context.id, {
		name_hint = "while_header",
		evidence = host.evidence_for(state, node),
	})
	state.builder:finalizeBlock(context.block, LifterIR.Terminator.jump(LifterIR.Edge(headerBlock)))

	local headerContext = self:_branchContext(context, headerBlock)
	local conditionNode = host.expect_record(node.condition, "malformed_while", "while statement is missing its condition")
	local conditionOutcome = host.lower_expression(
		headerContext,
		conditionNode,
		"while_condition"
	)
	if conditionOutcome.kind == "terminated" then
		context.block = headerContext.block
		context.terminated = true
		return
	end
	local bodyBlock = state.builder:reserveBlock(context.id, {
		name_hint = "while_body",
		evidence = host.evidence_for(state, bodyNode),
	})
	local exitBlock = state.builder:reserveBlock(context.id, {
		name_hint = "while_exit",
		evidence = host.evidence_for(state, node),
	})
	state.builder:finalizeBlock(
		headerContext.block,
		LifterIR.Terminator.branch(conditionOutcome.value.id, LifterIR.Edge(bodyBlock), LifterIR.Edge(exitBlock))
	)

	local bodyContext = self:_branchContext(context, bodyBlock)
	table.insert(bodyContext.loop_stack, { continue_block = headerBlock, break_block = exitBlock })
	host.lower_statement_block(bodyContext, bodyNode, false)
	table.remove(bodyContext.loop_stack)
	if not bodyContext.terminated then
		state.builder:finalizeBlock(bodyContext.block, LifterIR.Terminator.jump(LifterIR.Edge(headerBlock)))
	end

	context.block = exitBlock
	context.terminated = false
end

function ControlLowerer:lowerRepeat(context: any, node: Record)
	local host: Host = self.host
	local state = context.frontend
	local bodyNode = host.expect_record(node.body, "malformed_repeat", "repeat statement is missing its body")
	local bodyBlock = state.builder:reserveBlock(context.id, {
		name_hint = "repeat_body",
		evidence = host.evidence_for(state, bodyNode),
	})
	local latchBlock = state.builder:reserveBlock(context.id, {
		name_hint = "repeat_latch",
		evidence = host.evidence_for(state, node),
	})
	local exitBlock = state.builder:reserveBlock(context.id, {
		name_hint = "repeat_exit",
		evidence = host.evidence_for(state, node),
	})
	state.builder:finalizeBlock(context.block, LifterIR.Terminator.jump(LifterIR.Edge(bodyBlock)))

	local bodyContext = self:_branchContext(context, bodyBlock)
	local loopTargets = {
		continue_block = latchBlock,
		break_block = exitBlock,
		continue_reachable = false,
		break_reachable = false,
	}
	table.insert(bodyContext.loop_stack, loopTargets)
	host.lower_statement_block(bodyContext, bodyNode, false)
	table.remove(bodyContext.loop_stack)
	if not bodyContext.terminated then
		state.builder:finalizeBlock(bodyContext.block, LifterIR.Terminator.jump(LifterIR.Edge(latchBlock)))
	end
	local latchReachable = not bodyContext.terminated or loopTargets.continue_reachable
	if not latchReachable then
		state.builder:finalizeBlock(latchBlock, LifterIR.Terminator.unreachable())
		if loopTargets.break_reachable then
			context.block = exitBlock
			context.terminated = false
		else
			state.builder:finalizeBlock(exitBlock, LifterIR.Terminator.unreachable())
			context.block = bodyContext.block
			context.terminated = true
		end
		return
	end

	local latchContext = self:_branchContext(context, latchBlock)
	local conditionNode = host.expect_record(node.condition, "malformed_repeat", "repeat statement is missing its condition")
	local conditionOutcome = host.lower_expression(
		latchContext,
		conditionNode,
		"until_condition"
	)
	if conditionOutcome.kind ~= "terminated" then
		state.builder:finalizeBlock(
			latchContext.block,
			LifterIR.Terminator.branch(conditionOutcome.value.id, LifterIR.Edge(exitBlock), LifterIR.Edge(bodyBlock))
		)
	elseif not loopTargets.break_reachable then
		state.builder:finalizeBlock(exitBlock, LifterIR.Terminator.unreachable())
		context.block = latchContext.block
		context.terminated = true
		return
	end

	context.block = exitBlock
	context.terminated = false
end

function ControlLowerer:lowerLoopTransfer(context: any, node: Record, isContinue: boolean)
	local targets = context.loop_stack[#context.loop_stack]
	if targets == nil then
		self.host.diagnostic(
			if isContinue then "continue_outside_loop" else "break_outside_loop",
			node,
			if isContinue then "continue has no enclosing loop" else "break has no enclosing loop"
		)
	end
	local target = if isContinue then targets.continue_block else targets.break_block
	local arguments = if isContinue then targets.continue_arguments else targets.break_arguments
	if isContinue then
		targets.continue_reachable = true
	else
		targets.break_reachable = true
	end
	context.frontend.builder:finalizeBlock(context.block, LifterIR.Terminator.jump(LifterIR.Edge(target, arguments or {})))
	context.terminated = true
end

return table.freeze(AstControl)
