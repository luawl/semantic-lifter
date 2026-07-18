--!strict

local LifterIR = require("./lifter_ir")

local IntrinsicBindings = {}

local kindsByPath = table.freeze({
	error = "error_termination",
	pcall = "protected_call",
	xpcall = "protected_call_with_handler",
	["coroutine.create"] = "coroutine_create",
	["coroutine.resume"] = "coroutine_resume",
	["coroutine.yield"] = "coroutine_yield",
})

function IntrinsicBindings.kindForPath(path: string): string?
	return kindsByPath[path]
end

local function tail(values: { number }, first: number): { number }
	local result = {}
	for index = first, #values do
		table.insert(result, values[index])
	end
	return result
end

function IntrinsicBindings.canLower(kind: string, scalarCount: number, hasOpenArgument: boolean): boolean
	if kind == "protected_call" then
		return scalarCount >= 1
	elseif kind == "protected_call_with_handler" then
		return scalarCount >= 2
	elseif kind == "coroutine_create" then
		return scalarCount == 1 and not hasOpenArgument
	elseif kind == "coroutine_resume" then
		return scalarCount >= 1
	elseif kind == "coroutine_yield" then
		return true
	end
	return false
end

function IntrinsicBindings.canTerminate(kind: string, scalarCount: number, hasOpenArgument: boolean): boolean
	return kind == "error_termination" and (not hasOpenArgument or scalarCount >= 2)
end

function IntrinsicBindings.effects(kind: string): any
	if kind == "protected_call" or kind == "protected_call_with_handler" then
		return LifterIR.Effects.protectedInvocation()
	elseif kind == "coroutine_create" then
		return LifterIR.Effects.coroutineCreate()
	elseif kind == "coroutine_resume" then
		return LifterIR.Effects.coroutineResume()
	elseif kind == "coroutine_yield" then
		return LifterIR.Effects.coroutineYield()
	end
	error(`unknown intrinsic kind {kind}`, 0)
end

function IntrinsicBindings.fixedResultCount(kind: string, requested: number): number
	if kind == "coroutine_create" then
		return 1
	elseif kind == "protected_call" or kind == "protected_call_with_handler" or kind == "coroutine_resume" then
		return math.max(requested, 1)
	end
	return requested
end

function IntrinsicBindings.resultType(kind: string, index: number): any
	if kind == "coroutine_create" then
		return LifterIR.Types.thread()
	elseif index == 1 and (kind == "protected_call" or kind == "protected_call_with_handler" or kind == "coroutine_resume") then
		return LifterIR.Types.boolean()
	end
	return LifterIR.Types.dynamic()
end

function IntrinsicBindings.exactOpenResultTypes(kind: string): { any }?
	if kind == "coroutine_create" then
		return { LifterIR.Types.thread() }
	end
	return nil
end

function IntrinsicBindings.operation(kind: string, arguments: { number }, resultCount: number, argumentPack: number?): any
	if kind == "protected_call" then
		return LifterIR.Operation.protectedCall(
			arguments[1],
			nil,
			tail(arguments, 2),
			LifterIR.ResultArity.fixed(resultCount),
			argumentPack
		)
	elseif kind == "protected_call_with_handler" then
		return LifterIR.Operation.protectedCall(
			arguments[1],
			arguments[2],
			tail(arguments, 3),
			LifterIR.ResultArity.fixed(resultCount),
			argumentPack
		)
	elseif kind == "coroutine_create" then
		return LifterIR.Operation.coroutineCreate(arguments[1])
	elseif kind == "coroutine_resume" then
		return LifterIR.Operation.coroutineResume(
			arguments[1],
			tail(arguments, 2),
			LifterIR.ResultArity.fixed(resultCount),
			argumentPack
		)
	elseif kind == "coroutine_yield" then
		return LifterIR.Operation.coroutineYield(arguments, LifterIR.ResultArity.fixed(resultCount), argumentPack)
	end
	error(`unknown intrinsic kind {kind}`, 0)
end

function IntrinsicBindings.addOpen(
	kind: string,
	builder: any,
	block: number,
	arguments: { number },
	options: any,
	argumentPack: number?
): (number, number)
	if kind == "protected_call" then
		return builder:addOpenProtectedCall(block, arguments[1], nil, tail(arguments, 2), options, argumentPack)
	elseif kind == "protected_call_with_handler" then
		return builder:addOpenProtectedCall(block, arguments[1], arguments[2], tail(arguments, 3), options, argumentPack)
	elseif kind == "coroutine_resume" then
		return builder:addOpenCoroutineResume(block, arguments[1], tail(arguments, 2), options, argumentPack)
	elseif kind == "coroutine_yield" then
		return builder:addOpenCoroutineYield(block, arguments, options, argumentPack)
	elseif kind == "coroutine_create" then
		local _, results = builder:addInstruction(
			block,
			LifterIR.Operation.coroutineCreate(arguments[1]),
			{ { type = LifterIR.Types.thread(), name_hint = "thread" } },
			options
		)
		return builder:addValuePack(block, { results[1] }, {
			effects = LifterIR.Effects.pure(),
			evidence = options.evidence,
		})
	end
	error(`intrinsic kind {kind} cannot produce an open result`, 0)
end

return table.freeze(IntrinsicBindings)
