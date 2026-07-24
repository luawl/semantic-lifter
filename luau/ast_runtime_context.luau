--!strict

-- Loop-transfer and vararg ownership contexts for the admission graph walk.

local AstExpressionScalar = require("./ast_expression_scalar")

local AstRuntimeContext = {}

type Record = { [string]: any }

export type Context = {
	loop_depth: number,
	variadic_function: boolean,
}

export type Problem = {
	code: string,
	node: Record?,
	detail: string,
}

function AstRuntimeContext.root(): Context
	return { loop_depth = 0, variadic_function = true }
end

function AstRuntimeContext.validate(record: Record, context: Context): Problem?
	if record.type == "AstStatBreak" and context.loop_depth == 0 then
		return { code = "break_outside_loop", node = record, detail = "break has no enclosing loop" }
	elseif record.type == "AstStatContinue" and context.loop_depth == 0 then
		return { code = "continue_outside_loop", node = record, detail = "continue has no enclosing loop" }
	elseif record.type == "AstExprVarargs" and not context.variadic_function then
		return {
			code = "varargs_outside_variadic_function",
			node = record,
			detail = "varargs have no owning function pack",
		}
	end
	return nil
end

function AstRuntimeContext.child(record: Record, key: any, child: Record, context: Context): Context
	if record.type == "AstExprFunction" then
		local isVariadic = AstExpressionScalar.functionIsVariadic(record)
		return { loop_depth = 0, variadic_function = isVariadic == true }
	elseif key == "body"
		and child == record.body
		and (record.type == "AstStatWhile"
			or record.type == "AstStatRepeat"
			or record.type == "AstStatFor"
			or record.type == "AstStatForIn")
	then
		return { loop_depth = context.loop_depth + 1, variadic_function = context.variadic_function }
	end
	return context
end

return table.freeze(AstRuntimeContext)
