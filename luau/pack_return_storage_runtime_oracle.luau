--!strict

local PackReturnStorageRuntimeOracle = {}

function PackReturnStorageRuntimeOracle.run(chunk: any, source: string): () -> any
	local order: { string } = {}
	local producerCalls = 0
	local observerCalls = 0
	local consumerCalls = 0
	local activeCase = ""
	local returnWorker, invocationWorker, literalWorker, writeWorker, reuseWorker = chunk()
	assert(type(returnWorker) == "function", "return-tail worker was not exported")
	assert(type(invocationWorker) == "function", "invocation-tail worker was not exported")
	assert(type(literalWorker) == "function", "literal-tail worker was not exported")
	assert(type(writeWorker) == "function", "write-tail worker was not exported")
	assert(type(reuseWorker) == "function", "reuse-tail worker was not exported")

	local function producer(): ...any
		producerCalls += 1
		table.insert(order, activeCase .. ":produce")
		return 3, nil, 5
	end

	local function observe(): number
		observerCalls += 1
		table.insert(order, activeCase .. ":observe")
		return 17
	end

	local function consume(...: any): { [number]: any, n: number }
		consumerCalls += 1
		table.insert(order, activeCase .. ":consume")
		return table.pack(...)
	end

	activeCase = "return"
	local returned = table.pack(returnWorker(producer, observe))
	assert(returned.n == 4, "return-only stored pack changed expanded result arity")
	assert(returned[1] == 17, "return-only stored pack changed the observed prefix")
	assert(returned[2] == 3 and returned[3] == nil and returned[4] == 5, "return-only stored pack changed values or nil holes")

	activeCase = "invocation"
	local invoked = invocationWorker(producer, observe, consume)
	assert(type(invoked) == "table" and invoked.n == 4, "stored invocation tail changed argument arity")
	assert(invoked[1] == 17 and invoked[2] == 3 and invoked[3] == nil and invoked[4] == 5, "stored invocation tail changed values or nil holes")

	activeCase = "literal"
	local literal = literalWorker(producer, observe)
	assert(type(literal) == "table", "stored literal tail did not return a table")
	assert(literal[1] == 17 and literal[2] == 3 and literal[3] == nil and literal[4] == 5, "stored literal tail changed values or nil holes")

	activeCase = "write"
	local target: { [number]: any } = { "preserved" }
	local writeObserved = writeWorker(producer, observe, target)
	assert(writeObserved == 17, "stored table write lost the observation result")
	assert(target[1] == "preserved" and target[2] == 3 and target[3] == nil and target[4] == 5, "stored table write changed values or nil holes")

	activeCase = "reuse"
	local reuseTarget: { [number]: any } = { "preserved" }
	local reused = table.pack(reuseWorker(producer, observe, consume, reuseTarget))
	assert(reused.n == 7, "reused stored pack changed expanded result arity")
	for index = 1, 2 do
		local invocation = reused[index]
		assert(type(invocation) == "table" and invocation.n == 4, "reused invocation tail changed argument arity")
		assert(invocation[1] == 17 and invocation[2] == 3 and invocation[3] == nil and invocation[4] == 5, "reused invocation tail changed values or nil holes")
	end
	local reusedLiteral = reused[3]
	assert(type(reusedLiteral) == "table", "reused literal tail did not return a table")
	assert(reusedLiteral[1] == 17 and reusedLiteral[2] == 3 and reusedLiteral[3] == nil and reusedLiteral[4] == 5, "reused literal tail changed values or nil holes")
	assert(reused[4] == 17 and reused[5] == 3 and reused[6] == nil and reused[7] == 5, "reused expanded return changed values or nil holes")
	assert(reuseTarget[1] == "preserved" and reuseTarget[2] == 3 and reuseTarget[3] == nil and reuseTarget[4] == 5, "reused table write changed values or nil holes")

	assert(producerCalls == 5, "stored pack producer count changed")
	assert(observerCalls == 5, "stored pack observer count changed")
	assert(consumerCalls == 3, "stored invocation consumer count changed")
	assert(
		table.concat(order, ",")
			== "return:produce,return:observe,invocation:produce,invocation:observe,invocation:consume,literal:produce,literal:observe,write:produce,write:observe,reuse:produce,reuse:observe,reuse:consume,reuse:consume",
		"stored pack tails changed observable order"
	)
	assert(
		select(2, string.gsub(source, "local __lifter_stored_values_", "")) == 5,
		"stored pack carrier count changed"
	)
	assert(
		select(2, string.gsub(source, "__lifter_table_unpack%(__lifter_pack_", "")) == 9,
		"stored pack expansion count changed"
	)
	return function(): any
		return {
			returned = returned,
			invoked = invoked,
			literal = literal,
			target = target,
			reused = reused,
			reuseTarget = reuseTarget,
		}
	end
end

return PackReturnStorageRuntimeOracle
