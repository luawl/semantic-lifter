--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")
local IR = require("../luau/lifter_ir")

local handoff: any = serde.decode("json", fs.readFile(process.args[1]))
assert(handoff.schema_version == "compiler_disassembly_handoff_v1")
local builder = IR.Builder.new(process.args[3] or "compiler-disassembly")
local evidence = builder:addEvidence("decoded_record", `compiler-listing:{handoff.function_index}`, handoff.listing_sha256)
local root = builder:reserveFunction({ name_hint = "module", evidence = { evidence } })
local worker = builder:reserveFunction({ name_hint = "worker", lexical_parent = root, evidence = { evidence } })
builder:setEntryFunction(root)
local rootBlock = builder:reserveBlock(root, { evidence = { evidence } })
builder:setFunctionEntry(root, rootBlock)
local entry = builder:reserveBlock(worker, { name_hint = "register_entry", evidence = { evidence } })
builder:setFunctionEntry(worker, entry)
local places: { [number]: number } = {}
for _, reg in handoff.registers do
    places[reg] = builder:addLocalPlace(worker, IR.Types.dynamic(), `r{reg}`, { evidence })
end
for reg = 0, handoff.parameter_count - 1 do
    local parameter = builder:addParameter(worker, IR.Types.dynamic(), `argument_{reg}`)
    builder:addInstruction(entry, IR.Operation.placeWrite(places[reg], parameter), {}, { effects = IR.Effects.placeWrite(), evidence = { evidence } })
end
local blocks = {}
for index, instruction in handoff.instructions do
    local lineEvidence = builder:addEvidence("decoded_record", `compiler-listing:{handoff.function_index}:line:{instruction.line_number}`, handoff.listing_sha256)
    blocks[index] = builder:reserveBlock(worker, { name_hint = `instruction_{index}`, evidence = { lineEvidence } })
end
builder:finalizeBlock(entry, IR.Terminator.jump(IR.Edge(blocks[1])))
for index, instruction in handoff.instructions do
    assert(table.find({ "constant", "move", "binary", "unary", "jump", "branch", "return" }, instruction.kind) ~= nil,
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
    if instruction.kind == "constant" then
        local kind = if instruction.value.number ~= nil then IR.Types.number()
            elseif instruction.value.boolean ~= nil then IR.Types.boolean() else IR.Types.nilValue()
        result = value(IR.Operation.constant(instruction.value), kind, IR.Effects.pure())
    elseif instruction.kind == "move" then
        result = reads[1]
    elseif instruction.kind == "binary" then
        result = value(IR.Operation.binary(instruction.operator, reads[1], reads[2]), IR.Types.dynamic(), IR.Effects.dynamicCall())
    elseif instruction.kind == "unary" then
        local resultType = if instruction.operator == "logical_not" then IR.Types.boolean() else IR.Types.dynamic()
        result = value(IR.Operation.unary(instruction.operator, reads[1]), resultType, IR.Effects.dynamicCall())
    end
    if result ~= nil then
        builder:addInstruction(block, IR.Operation.placeWrite(places[instruction.writes[1]], result), {}, { effects = IR.Effects.placeWrite(), evidence = blockEvidence })
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
    else
        builder:finalizeBlock(block, IR.Terminator.jump(IR.Edge(blocks[index + 1])))
    end
end
builder:finalizeFunction(worker)
local _, closure = builder:addInstruction(rootBlock, IR.Operation.makeClosure(worker, {}), { { type = IR.Types.functionValue() } }, { effects = IR.Effects.pure(), evidence = { evidence } })
builder:finalizeBlock(rootBlock, IR.Terminator.returnValues(closure))
builder:finalizeFunction(root)
fs.writeFile(process.args[2], IR.encodeJson(builder:finish(), true) .. "\n")
