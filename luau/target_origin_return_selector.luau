--!strict

-- Selects one exact terminal return from a bounded direct factory invocation.
-- Fixed conditions select one branch. Dynamic conditional expressions remain
-- explicit so the origin matcher can require agreement across both branches.

local AstExpressionScalar = require("./ast_expression_scalar")
local InvocationFrame = require("./invocation_frame")

local TargetOriginReturnSelector = {}
TargetOriginReturnSelector.maxConditionBindingDepth = 64

type Record = InvocationFrame.Record
type Context = InvocationFrame.Context

export type Selection = {
	returned: Record,
	resultOrdinal: number,
	statementCount: number,
}

local recordArrayLength = InvocationFrame.recordArrayLength
local unwrapExpression = InvocationFrame.unwrapExpression

local function exactTruthiness(value: any, label: string): boolean?
	if type(value) ~= "table" then
		return nil
	end
	local expression = unwrapExpression(value, label)
	if expression.type == "AstExprConstantBool" and type(expression.value) == "boolean" then
		return expression.value
	elseif expression.type == "AstExprConstantNil" then
		return false
	elseif expression.type == "AstExprConstantNumber" and type(expression.value) == "number" then
		return true
	elseif expression.type == "AstExprConstantString" and type(expression.value) == "string" then
		return true
	end
	return nil
end

local function fixedConditionTruthinessAt(
	condition: any,
	context: Context?,
	depth: number,
	active: { [any]: boolean }
): boolean?
	local literal = exactTruthiness(condition, "target conditional return condition")
	if literal ~= nil then
		return literal
	end
	local expression = unwrapExpression(condition, "target conditional return parameter")
	if expression.type == "AstExprUnary" then
		if depth >= TargetOriginReturnSelector.maxConditionBindingDepth
			or AstExpressionScalar.unaryOperator(expression.op) ~= "logical_not"
			or type(expression.expr) ~= "table"
			or type((expression.expr :: Record).type) ~= "string"
			or active[expression] == true
		then
			return nil
		end
		active[expression] = true
		local operand = fixedConditionTruthinessAt(expression.expr, context, depth + 1, active)
		active[expression] = nil
		return if operand == nil then nil else not (operand :: boolean)
	elseif expression.type == "AstExprBinary" then
		local op = expression.op
		if depth >= TargetOriginReturnSelector.maxConditionBindingDepth
			or (op ~= "And" and op ~= "Or")
			or type(expression.left) ~= "table"
			or type((expression.left :: Record).type) ~= "string"
			or type(expression.right) ~= "table"
			or type((expression.right :: Record).type) ~= "string"
			or active[expression] == true
		then
			return nil
		end
		active[expression] = true
		local left = fixedConditionTruthinessAt(expression.left, context, depth + 1, active)
		if (op == "And" and left == false) or (op == "Or" and left == true) then
			active[expression] = nil
			return left
		end
		local right = fixedConditionTruthinessAt(expression.right, context, depth + 1, active)
		active[expression] = nil
		if left == nil then
			if (op == "And" and right == false) or (op == "Or" and right == true) then
				return right
			end
			return nil
		end
		return right
	elseif context == nil or depth >= TargetOriginReturnSelector.maxConditionBindingDepth then
		return nil
	end
	if expression.type == "AstExprVarargs" then
		local adjustment, parent = InvocationFrame.adjustedContextVararg(expression, 1, context)
		if adjustment == nil then
			return nil
		elseif (adjustment :: InvocationFrame.ArgumentAdjustment).state == "implicit_nil" then
			return false
		end
		local selected = (adjustment :: InvocationFrame.ArgumentAdjustment).selected
		if (adjustment :: InvocationFrame.ArgumentAdjustment).state ~= "value"
			or selected == nil
			or (selected :: InvocationFrame.SelectedValue).resultOrdinal ~= 1
		then
			return nil
		end
		return fixedConditionTruthinessAt(
			(selected :: InvocationFrame.SelectedValue).expression,
			parent,
			depth + 1,
			active
		)
	end
	local selected, parent = InvocationFrame.calleeBinding(context, expression)
	if selected == nil
		or (selected :: InvocationFrame.Binding).kind ~= "parameter"
		or (selected :: InvocationFrame.Binding).resultOrdinal ~= 1
		or active[selected] == true
	then
		return nil
	end
	if (selected :: InvocationFrame.Binding).argumentState == "implicit_nil" then
		return false
	elseif (selected :: InvocationFrame.Binding).argumentState ~= "value"
		or (selected :: InvocationFrame.Binding).argument == nil
	then
		return nil
	end
	active[selected] = true
	local result = fixedConditionTruthinessAt(
		(selected :: InvocationFrame.Binding).argument,
		parent,
		depth + 1,
		active
	)
	active[selected] = nil
	return result
end

function TargetOriginReturnSelector.fixedConditionTruthiness(condition: any, context: Context?): boolean?
	return fixedConditionTruthinessAt(condition, context, 0, {})
end

local function singleReturn(value: any): Record?
	if type(value) ~= "table" or (value :: Record).type ~= "AstStatBlock" then
		return nil
	end
	local statementCount = recordArrayLength((value :: Record).body)
	if statementCount ~= 1 then
		return nil
	end
	local statement = (value :: Record).body[1] :: Record
	if statement.type ~= "AstStatReturn" or recordArrayLength(statement.list) == nil then
		return nil
	end
	return statement
end

local function terminalReturn(statements: { Record }, statementCount: number, context: Context?): Record?
	local terminal = statements[statementCount] :: Record
	if terminal.type == "AstStatReturn" then
		return terminal
	elseif terminal.type ~= "AstStatIf" then
		return nil
	end
	local condition = TargetOriginReturnSelector.fixedConditionTruthiness(terminal.condition, context)
	if condition == nil then
		return nil
	end
	local thenReturn = singleReturn(terminal.thenbody)
	local elseReturn = singleReturn(terminal.elsebody)
	if thenReturn == nil or elseReturn == nil then
		return nil
	end
	return if condition :: boolean then thenReturn else elseReturn
end

function TargetOriginReturnSelector.selectedConditionalExpression(returned: Record, context: Context?): Record?
	local expression = unwrapExpression(returned, "target conditional return expression")
	if expression.type ~= "AstExprIfElse" then
		return returned
	end
	local condition = TargetOriginReturnSelector.fixedConditionTruthiness(expression.condition, context)
	if type(expression.condition) ~= "table"
		or type((expression.condition :: Record).type) ~= "string"
		or type(expression.trueExpr) ~= "table"
		or type((expression.trueExpr :: Record).type) ~= "string"
		or type(expression.falseExpr) ~= "table"
		or type((expression.falseExpr :: Record).type) ~= "string"
	then
		return nil
	end
	if condition == nil then
		return expression
	end
	return if condition :: boolean then expression.trueExpr :: Record else expression.falseExpr :: Record
end

function TargetOriginReturnSelector.select(
	statementsValue: any,
	requestedResultOrdinal: number,
	context: Context?
): Selection?
	local statementCount = recordArrayLength(statementsValue)
	if statementCount == nil
		or statementCount == 0
		or requestedResultOrdinal < 1
		or requestedResultOrdinal > InvocationFrame.maxResultWidth
	then
		return nil
	end
	local statements = statementsValue :: { Record }
	local returnStatement = terminalReturn(statements, statementCount, context)
	if returnStatement == nil then
		return nil
	end
	local returnCount = recordArrayLength((returnStatement :: Record).list)
	if returnCount == nil or returnCount == 0 or returnCount > InvocationFrame.maxResultWidth then
		return nil
	end
	local returned: Record
	local resultOrdinal = 1
	if requestedResultOrdinal <= returnCount then
		returned = (returnStatement :: Record).list[requestedResultOrdinal] :: Record
	else
		returned = (returnStatement :: Record).list[returnCount] :: Record
		resultOrdinal = requestedResultOrdinal - returnCount + 1
		if returned.type == "AstExprCall" then
			if returned.self ~= false or recordArrayLength(returned.args) == nil then
				return nil
			end
		elseif returned.type ~= "AstExprVarargs" then
			return nil
		end
	end
	local selectedReturned = TargetOriginReturnSelector.selectedConditionalExpression(returned, context)
	if selectedReturned == nil then
		return nil
	end
	returned = selectedReturned :: Record
	return {
		returned = returned,
		resultOrdinal = resultOrdinal,
		statementCount = statementCount,
	}
end

return table.freeze(TargetOriginReturnSelector)
