--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")
local IR = require("../luau/lifter_ir")

local handoff: any = serde.decode("json", fs.readFile(process.args[1]))
local version2 = handoff.schema_version == "compiler_disassembly_handoff_v2"
assert(version2 or handoff.schema_version == "compiler_disassembly_handoff_v1")
local isVariadic = version2 and handoff.is_variadic == true
local builder = IR.Builder.new(process.args[3] or "compiler-disassembly")
local evidence = builder:addEvidence("decoded_record", `compiler-listing:{handoff.function_index}`, handoff.listing_sha256)
local root = builder:reserveFunction({ name_hint = "module", evidence = { evidence } })
local worker = builder:reserveFunction({ name_hint = "worker", lexical_parent = root, is_variadic = isVariadic, evidence = { evidence } })
builder:setEntryFunction(root)
local rootBlock = builder:reserveBlock(root, { evidence = { evidence } })
builder:setFunctionEntry(root, rootBlock)
local entry = builder:reserveBlock(worker, { name_hint = "register_entry", evidence = { evidence } })
builder:setFunctionEntry(worker, entry)
local places: { [number]: number } = {}
local placed: { number } = handoff.registers
if version2 then
    -- v2: a place only for a register that some instruction reads, in ascending order; the
    -- backend refuses a declared local place that nothing reads.
    local read: { [number]: boolean } = {}
    placed = {}
    for _, instruction in handoff.instructions do
        for _, reg in instruction.reads do
            if not read[reg] then
                read[reg] = true
                table.insert(placed, reg)
            end
        end
    end
    table.sort(placed)
end
for _, reg in placed do
    places[reg] = builder:addLocalPlace(worker, IR.Types.dynamic(), `r{reg}`, { evidence })
end
for reg = 0, handoff.parameter_count - 1 do
    local parameter = builder:addParameter(worker, IR.Types.dynamic(), `argument_{reg}`)
    if places[reg] ~= nil then
        builder:addInstruction(entry, IR.Operation.placeWrite(places[reg], parameter), {}, { effects = IR.Effects.placeWrite(), evidence = { evidence } })
    end
end
if isVariadic then
    -- The source frontend's rule (luau/ast_frontend.luau:961-962): a variadic function owns its vararg pack.
    builder:addVarargPack(worker, { evidence })
end
local blocks = {}
for index, instruction in handoff.instructions do
    local lineEvidence = builder:addEvidence("decoded_record", `compiler-listing:{handoff.function_index}:line:{instruction.line_number}`, handoff.listing_sha256)
    local cited = { lineEvidence }
    if instruction.kind == "namecall" then
        -- The fused NAMECALL + CALL pair is one block; it also cites the CALL line's record.
        table.insert(cited, builder:addEvidence("decoded_record", `compiler-listing:{handoff.function_index}:line:{instruction.line_numbers[2]}`, handoff.listing_sha256))
    end
    blocks[index] = builder:reserveBlock(worker, { name_hint = `instruction_{index}`, evidence = cited })
end
builder:finalizeBlock(entry, IR.Terminator.jump(IR.Edge(blocks[1])))
for index, instruction in handoff.instructions do
    assert(table.find({ "constant", "move", "binary", "unary", "concat", "jump", "branch", "return", "environment_get", "environment_set", "call", "namecall" }, instruction.kind) ~= nil,
        "unsupported handoff instruction kind")
    local block = blocks[index]
    local blockEvidence = builder.program.blocks[block + 1].evidence
    local function value(operation: any, resultType: any, effects: any): number
        local _, results = builder:addInstruction(block, operation, { { type = resultType } }, { effects = effects, evidence = blockEvidence })
        return results[1]
    end
    local reads = {}
    for slot, reg in instruction.reads do
        reads[slot] = value(IR.Operation.placeRead(places[reg]), IR.Types.dynamic(), IR.Effects.placeRead())
    end
    local result: number? = nil
    local results: { number }? = nil
    if instruction.kind == "constant" then
        local literal: any = instruction.value
        local kind: any
        if literal.number ~= nil then
            kind = IR.Types.number()
        elseif literal.boolean ~= nil then
            kind = IR.Types.boolean()
        elseif literal.nil_value ~= nil then
            kind = IR.Types.nilValue()
        elseif type(literal.string) == "string" then
            kind = IR.Types.string()
            literal = IR.Literal.string(literal.string)
        else
            error("unsupported handoff constant")
        end
        result = value(IR.Operation.constant(literal), kind, IR.Effects.pure())
    elseif instruction.kind == "move" then
        result = reads[1]
    elseif instruction.kind == "binary" then
        result = value(IR.Operation.binary(instruction.operator, reads[1], reads[2]), IR.Types.dynamic(), IR.Effects.dynamicCall())
    elseif instruction.kind == "unary" then
        local resultType = if instruction.operator == "logical_not" then IR.Types.boolean() else IR.Types.dynamic()
        result = value(IR.Operation.unary(instruction.operator, reads[1]), resultType, IR.Effects.dynamicCall())
    elseif instruction.kind == "concat" then
        -- Luau `..` is right-associative: R(b) .. (R(b+1) .. (... .. R(c))), one dynamic call per step.
        local folded = reads[#reads]
        for slot = #reads - 1, 1, -1 do
            folded = value(IR.Operation.binary("concat", reads[slot], folded), IR.Types.dynamic(), IR.Effects.dynamicCall())
        end
        result = folded
    elseif instruction.kind == "environment_get" then
        -- An ambient global in semantic mode, the construct the source frontend emits (luau/ast_frontend_expressions.luau:810-822).
        result = value(IR.Operation.environmentGet(IR.EnvironmentTarget.ambient(), instruction.name), IR.Types.dynamic(), IR.Effects.semanticTableRead())
    elseif instruction.kind == "environment_set" then
        -- A global assignment has no result; its value is the per-instruction place read of the source register.
        builder:addInstruction(block, IR.Operation.environmentSet(IR.EnvironmentTarget.ambient(), instruction.name, reads[1]), {}, { effects = IR.Effects.semanticTableWrite(), evidence = blockEvidence })
    elseif instruction.kind == "call" or instruction.kind == "namecall" then
        -- A call whose callee the frontend cannot see: fixed(m) dynamic results, effects
        -- dynamicCall (namecall: IR.Effects.namecall(), the same set), no obligations. reads[1] is the callee R(a)
        -- (namecall: the receiver R(b)); the remaining reads are the arguments.
        local arguments: { number } = {}
        for slot = 2, #reads do
            table.insert(arguments, reads[slot])
        end
        local resultSpecs = {}
        for _ = 1, instruction.result_count do
            table.insert(resultSpecs, { type = IR.Types.dynamic() })
        end
        local arity = IR.ResultArity.fixed(instruction.result_count)
        local operation = if instruction.kind == "namecall"
            then IR.Operation.namecall(reads[1], instruction.method, arguments, arity)
            else IR.Operation.call(reads[1], arguments, arity)
        local effects = if instruction.kind == "namecall" then IR.Effects.namecall() else IR.Effects.dynamicCall()
        local _, values = builder:addInstruction(block, operation, resultSpecs, { effects = effects, evidence = blockEvidence })
        results = values
    end
    if result ~= nil and places[instruction.writes[1]] ~= nil then
        builder:addInstruction(block, IR.Operation.placeWrite(places[instruction.writes[1]], result), {}, { effects = IR.Effects.placeWrite(), evidence = blockEvidence })
    end
    if results ~= nil then
        -- call and namecall: result i goes to writes[i], only where that register has a place.
        for slot, reg in instruction.writes do
            if places[reg] ~= nil then
                builder:addInstruction(block, IR.Operation.placeWrite(places[reg], results[slot]), {}, { effects = IR.Effects.placeWrite(), evidence = blockEvidence })
            end
        end
    end
    if instruction.kind == "return" then
        builder:finalizeBlock(block, IR.Terminator.returnValues(reads))
    elseif instruction.kind == "jump" then
        builder:finalizeBlock(block, IR.Terminator.jump(IR.Edge(blocks[instruction.target + 1])))
    elseif instruction.kind == "branch" then
        local condition = reads[1]
        if instruction.operator ~= nil then
            condition = value(IR.Operation.binary(instruction.operator, reads[1], reads[2]), IR.Types.boolean(), IR.Effects.dynamicCall())
        end
        local target = IR.Edge(blocks[instruction.target + 1])
        local fallthrough = IR.Edge(blocks[index + 1])
        builder:finalizeBlock(block, IR.Terminator.branch(condition,
            if instruction.inverted then fallthrough else target,
            if instruction.inverted then target else fallthrough))
    elseif instruction.kind == "constant" and instruction.successors[1] ~= index then
        -- A LOADB skip: the adapter resolved the labelled skip target (0-based) into the successors.
        builder:finalizeBlock(block, IR.Terminator.jump(IR.Edge(blocks[instruction.successors[1] + 1])))
    else
        builder:finalizeBlock(block, IR.Terminator.jump(IR.Edge(blocks[index + 1])))
    end
end
builder:finalizeFunction(worker)
local _, closure = builder:addInstruction(rootBlock, IR.Operation.makeClosure(worker, {}), { { type = IR.Types.functionValue() } }, { effects = IR.Effects.pure(), evidence = { evidence } })
builder:finalizeBlock(rootBlock, IR.Terminator.returnValues(closure))
builder:finalizeFunction(root)
fs.writeFile(process.args[2], IR.encodeJson(builder:finish(), true) .. "\n")
