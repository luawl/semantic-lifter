--!strict

-- Ordered table-constructor lowering. Ordinary constructors stay compact;
-- constructors whose general keys can fail before later fields commit writes
-- as explicit admitted operations.

local LifterIR = require("./lifter_ir")
local Outcome = require("./ast_frontend_outcome")

local AstTables = {}

type Record = { [string]: any }

type Host = {
	diagnostic: (string, Record, string) -> never,
	expect_record: (any, string, string) -> Record,
	expect_array: (any, Record, string) -> { any },
	node_tag: (Record) -> string,
	scalar_result: (any, Record, Record, Record, string?, Record) -> any,
	instruction_options: (any, Record, Record, { number }?) -> Record,
	defer_register_local: (any, Record) -> (() -> any)?,
}

local function item(host: Host, value: any): Record
	return host.expect_record(value, "malformed_table_item", "table item is not an AST node")
end

local function itemValue(host: Host, value: Record): Record
	return host.expect_record(value.value, "malformed_table_item", "table item is missing its value")
end

local function isListItem(value: Record): boolean
	return value.kind == "list" or value.kind == "item"
end

local function isDefinitelyValidKey(host: Host, originalNode: Record): boolean
	local node = originalNode
	local tag = host.node_tag(node)
	while tag == "AstExprGroup" or tag == "AstExprTypeAssertion" or tag == "AstExprInstantiate" do
		node = host.expect_record(node.expr, "malformed_table_item", "table key wrapper is missing its expression")
		tag = host.node_tag(node)
	end
	if tag == "AstExprConstantBool"
		or tag == "AstExprConstantString"
		or tag == "AstExprTable"
		or tag == "AstExprFunction"
	then
		return true
	end
	if tag == "AstExprConstantNumber" then
		return type(node.value) == "number" and node.value == node.value
	end
	return false
end

local function requiresOrderedWrites(host: Host, items: { any }): boolean
	for index = 1, #items - 1 do
		local tableItem = item(host, items[index])
		if tableItem.kind == "general" then
			local key = host.expect_record(tableItem.key, "malformed_table_item", "keyed table item is missing its key")
			if not isDefinitelyValidKey(host, key) then
				return true
			end
		end
	end
	return false
end

local function addWrite(host: Host, context: any, node: Record, tableValue: any, key: any, value: any)
	context.frontend.builder:addInstruction(
		context.block,
		LifterIR.Operation.tableSet(tableValue.id, key.id, value.id),
		{},
		host.instruction_options(context.frontend, node, LifterIR.Effects.semanticTableWrite(), nil)
	)
end

local function addPackWrite(host: Host, context: any, node: Record, tableValue: any, firstIndex: number, pack: number)
	context.frontend.builder:addInstruction(
		context.block,
		LifterIR.Operation.tableSetPack(tableValue.id, firstIndex, pack),
		{},
		host.instruction_options(context.frontend, node, LifterIR.Effects.rawTableWrite(), nil)
	)
end

local function lowerOrdered(expressions: any, host: Host, context: any, node: Record, nameHint: string?, items: { any }): any
	local tableValue = host.scalar_result(
		context,
		node,
		LifterIR.Operation.makeTable(),
		LifterIR.Types.table(),
		nameHint,
		LifterIR.Effects.tableConstructor()
	)
	local listIndex = 0
	for itemIndex, itemValueRecord in items do
		local tableItem = item(host, itemValueRecord)
		local valueNode = itemValue(host, tableItem)
		if isListItem(tableItem) then
			local valueTag = host.node_tag(valueNode)
			if itemIndex == #items and (valueTag == "AstExprCall" or valueTag == "AstExprVarargs") then
				local tailOutcome = expressions:lowerOpen(context, valueNode)
				if tailOutcome.kind == "terminated" then
					return tailOutcome
				end
				addPackWrite(host, context, tableItem, tableValue, listIndex + 1, tailOutcome.pack)
			else
				listIndex += 1
				local valueOutcome = expressions:lower(context, valueNode, nil)
				if valueOutcome.kind == "terminated" then
					return valueOutcome
				end
				local key = host.scalar_result(
					context,
					tableItem,
					LifterIR.Operation.constant(LifterIR.Literal.integer(tostring(listIndex))),
					LifterIR.Types.integer(),
					"table_index",
					LifterIR.Effects.pure()
				)
				addWrite(host, context, tableItem, tableValue, key, valueOutcome.value)
			end
		elseif tableItem.kind == "record" or tableItem.kind == "general" then
			-- Luau reads a register local key at the item's store, after the item's value ran;
			-- any other key is computed before the value, in source order.
			local keyNode = host.expect_record(tableItem.key, "malformed_table_item", "keyed table item is missing its key")
			local readKey = host.defer_register_local(context, keyNode)
			local key: any = nil
			if readKey == nil then
				local keyOutcome = expressions:lower(context, keyNode, nil)
				if keyOutcome.kind == "terminated" then
					return keyOutcome
				end
				key = keyOutcome.value
			end
			local valueOutcome = expressions:lower(context, valueNode, nil)
			if valueOutcome.kind == "terminated" then
				return valueOutcome
			end
			if readKey ~= nil then
				key = readKey()
			end
			addWrite(host, context, tableItem, tableValue, key, valueOutcome.value)
		else
			host.diagnostic("unsupported_table_item_kind", tableItem, `table item kind {tostring(tableItem.kind)} is not mapped`)
		end
	end
	return Outcome.value(tableValue)
end

local function lowerLiteral(expressions: any, host: Host, context: any, node: Record, nameHint: string?, items: { any }): any
	local fields = {}
	local tailPack: number? = nil
	for itemIndex, itemValueRecord in items do
		local tableItem = item(host, itemValueRecord)
		if isListItem(tableItem) then
			local valueNode = itemValue(host, tableItem)
			local valueTag = host.node_tag(valueNode)
			if itemIndex == #items and (valueTag == "AstExprCall" or valueTag == "AstExprVarargs") then
				local tailOutcome = expressions:lowerOpen(context, valueNode)
				if tailOutcome.kind == "terminated" then
					return tailOutcome
				end
				tailPack = tailOutcome.pack
			else
				local valueOutcome = expressions:lower(context, valueNode, nil)
				if valueOutcome.kind == "terminated" then
					return valueOutcome
				end
				table.insert(fields, LifterIR.TableConstructorField.list(valueOutcome.value.id))
			end
		elseif tableItem.kind == "record" or tableItem.kind == "general" then
			-- Luau reads a register local key at the item's store, after the item's value ran;
			-- any other key is computed before the value, in source order.
			local keyNode = host.expect_record(tableItem.key, "malformed_table_item", "keyed table item is missing its key")
			local readKey = host.defer_register_local(context, keyNode)
			local key: any = nil
			if readKey == nil then
				local keyOutcome = expressions:lower(context, keyNode, nil)
				if keyOutcome.kind == "terminated" then
					return keyOutcome
				end
				key = keyOutcome.value
			end
			local valueOutcome = expressions:lower(context, itemValue(host, tableItem), nil)
			if valueOutcome.kind == "terminated" then
				return valueOutcome
			end
			if readKey ~= nil then
				key = readKey()
			end
			table.insert(fields, LifterIR.TableConstructorField.keyed(key.id, valueOutcome.value.id))
		else
			host.diagnostic("unsupported_table_item_kind", tableItem, `table item kind {tostring(tableItem.kind)} is not mapped`)
		end
	end
	return Outcome.value(host.scalar_result(
		context,
		node,
		LifterIR.Operation.makeTableLiteral(fields, tailPack),
		LifterIR.Types.table(),
		nameHint,
		LifterIR.Effects.tableConstructor()
	))
end

function AstTables.lower(expressions: any, host: Host, context: any, node: Record, nameHint: string?): any
	local items = host.expect_array(node.items, node, "items")
	if not requiresOrderedWrites(host, items) then
		return lowerLiteral(expressions, host, context, node, nameHint, items)
	end
	return lowerOrdered(expressions, host, context, node, nameHint, items)
end

return table.freeze(AstTables)
