--!strict

local fs = require("@lune/fs")
local process = require("@lune/process")
local serde = require("@lune/serde")
local IR = require("../../luau/lifter_ir")

local handoff: any = serde.decode("json", fs.readFile(process.args[1]))
-- v3 is v2 plus `functions`, the caller-declared nested functions of the selected function.
local version3 = handoff.schema_version == "compiler_disassembly_handoff_v3"
local version2 = version3 or handoff.schema_version == "compiler_disassembly_handoff_v2"
assert(version2 or handoff.schema_version == "compiler_disassembly_handoff_v1")
local isVariadic = version2 and handoff.is_variadic == true
local builder = IR.Builder.new(process.args[3] or "compiler-disassembly")
local evidence = builder:addEvidence("decoded_record", `compiler-listing:{handoff.function_index}`, handoff.listing_sha256)
local root = builder:reserveFunction({ name_hint = "module", evidence = { evidence } })
local worker = builder:reserveFunction({ name_hint = "worker", lexical_parent = root, is_variadic = isVariadic, evidence = { evidence } })
builder:setEntryFunction(root)
local rootBlock = builder:reserveBlock(root, { evidence = { evidence } })
builder:setFunctionEntry(root, rootBlock)
-- Nested functions (v3), parents before children (the handoff lists them in pre-order): one IR
-- function each, whose lexical parent is the IR function of its creating function. Their captures are the source
-- frontend's forms, in upvalue order: a value capture is an immutable value of
-- the child, a place capture a shared place of the child; each cites its CAPTURE line in the creating function.
local nested: { any } = if version3 then handoff.functions else {}
local irFunctionOf: { [number]: number } = { [handoff.function_index] = worker }
local evidenceOf: { [number]: number } = { [handoff.function_index] = evidence }
for _, fn in nested do
    local fnEvidence = builder:addEvidence("decoded_record", `compiler-listing:{fn.function_index}`, handoff.listing_sha256)
    evidenceOf[fn.function_index] = fnEvidence
    irFunctionOf[fn.function_index] = builder:reserveFunction({
        name_hint = `closure_{fn.function_index}`,
        lexical_parent = irFunctionOf[fn.parent_index],
        is_variadic = fn.is_variadic == true,
        evidence = { fnEvidence },
    })
end
local capturesOf: { [number]: { any } } = { [handoff.function_index] = {} }
for _, fn in nested do
    local list = {}
    for slot, upvalue in fn.upvalues do
        local cited = { builder:addEvidence("decoded_record", `compiler-listing:{fn.parent_index}:line:{upvalue.line_number}`, handoff.listing_sha256) }
        local irFunction = irFunctionOf[fn.function_index]
        if upvalue.class == "value" then
            local valueId = builder:addValueCapture(irFunction, IR.Types.dynamic(), `upvalue_{slot - 1}`, cited)
            list[slot] = { class = "value", value = valueId }
        else
            assert(upvalue.class == "place", "unknown upvalue class")
            local placeId = builder:addPlaceCapture(irFunction, IR.Types.dynamic(), `upvalue_{slot - 1}`, cited)
            list[slot] = { class = "place", place = placeId }
        end
    end
    capturesOf[fn.function_index] = list
end

-- The lowering of one function: the selected function (the worker) or a nested function of a v3 handoff.
local function liftFunction(fnHandoff: any, irFunction: number, fnIndex: number, fnEvidence: number)
    local entry = builder:reserveBlock(irFunction, { name_hint = "register_entry", evidence = { fnEvidence } })
    builder:setFunctionEntry(irFunction, entry)
    local places: { [number]: number } = {}
    local placed: { number } = fnHandoff.registers
    if version2 then
        -- v2: a place only for a register that some instruction reads, in ascending order; the
        -- backend refuses a declared local place that nothing reads. A by-reference capture (v3) binds the register's
        -- place, so it counts as a read.
        local read: { [number]: boolean } = {}
        placed = {}
        for _, instruction in fnHandoff.instructions do
            local used = table.clone(instruction.reads)
            for _, reg in instruction.references or {} do
                table.insert(used, reg)
            end
            for _, reg in used do
                if not read[reg] then
                    read[reg] = true
                    table.insert(placed, reg)
                end
            end
        end
        table.sort(placed)
    end
    for _, reg in placed do
        places[reg] = builder:addLocalPlace(irFunction, IR.Types.dynamic(), `r{reg}`, { fnEvidence })
    end
    for reg = 0, fnHandoff.parameter_count - 1 do
        local parameter = builder:addParameter(irFunction, IR.Types.dynamic(), `argument_{reg}`)
        if places[reg] ~= nil then
            builder:addInstruction(entry, IR.Operation.placeWrite(places[reg], parameter), {}, { effects = IR.Effects.placeWrite(), evidence = { fnEvidence } })
        end
    end
    local varargPack: number? = nil
    if version2 and fnHandoff.is_variadic == true then
        -- The source frontend's rule (luau/ast_frontend.luau:961-962): a variadic function owns its vararg pack.
        varargPack = builder:addVarargPack(irFunction, { fnEvidence })
    end
    -- This function's own captures (v3), in upvalue order; the worker captures nothing.
    local ownCaptures = capturesOf[fnIndex]
    local blocks = {}
    for index, instruction in fnHandoff.instructions do
        local lineEvidence = builder:addEvidence("decoded_record", `compiler-listing:{fnIndex}:line:{instruction.line_number}`, handoff.listing_sha256)
        local cited = { lineEvidence }
        if instruction.kind == "namecall" then
            -- The fused NAMECALL + CALL pair is one block; it also cites the CALL line's record.
            table.insert(cited, builder:addEvidence("decoded_record", `compiler-listing:{fnIndex}:line:{instruction.line_numbers[2]}`, handoff.listing_sha256))
        elseif instruction.kind == "closure" then
            -- The fused NEWCLOSURE + CAPTURE lines are one block; it also cites every CAPTURE line's record.
            for slot = 2, #instruction.line_numbers do
                table.insert(cited, builder:addEvidence("decoded_record", `compiler-listing:{fnIndex}:line:{instruction.line_numbers[slot]}`, handoff.listing_sha256))
            end
        end
        blocks[index] = builder:reserveBlock(irFunction, { name_hint = `instruction_{index}`, evidence = cited })
    end
    builder:finalizeBlock(entry, IR.Terminator.jump(IR.Edge(blocks[1])))
    -- Iteration regions: each region gets the source frontend's native form
    -- (luau/ast_frontend_iteration.luau): a header with the four state parameters and exactly one transition, and a body
    -- entry whose parameters are the loop variables. Keyed by the 0-based index of the region's prepare instruction.
    local loops: { [number]: any } = {}
    for index, instruction in fnHandoff.instructions do
        if instruction.kind == "iteration_prepare" then
            local loop = instruction.loop
            local numeric = loop.iteration == "numeric"
            local cited = builder.program.blocks[blocks[index] + 1].evidence
            local header = builder:reserveBlock(irFunction, { name_hint = if numeric then "numeric_for_header" else "generic_for_header", evidence = cited })
            local body = builder:reserveBlock(irFunction, { name_hint = if numeric then "numeric_for_body" else "generic_for_body", evidence = cited })
            local state = {}
            for _, name in (if numeric then { "numeric_control", "numeric_limit", "numeric_step" } else { "generic_iterator", "generic_state", "generic_control" }) do
                table.insert(state, builder:addBlockParameter(header, IR.Types.dynamic(), name))
            end
            table.insert(state, builder:addBlockParameter(header, IR.Types.boolean(), if numeric then "numeric_initial_transition" else "generic_initial_transition"))
            local variables = {}
            for _, reg in loop.variables do
                table.insert(variables, builder:addBlockParameter(body, if numeric then IR.Types.number() else IR.Types.dynamic(), `r{reg}`))
            end
            loops[loop.prepare] = { loop = loop, numeric = numeric, header = header, body = body, state = state, variables = variables, evidence = cited }
        end
    end
    -- The adjacent-only open protocol: the pack of an open producer (a call or namecall with
    -- variadic results, or open varargs) is pending from the producer's block to the next block only, whose instruction
    -- consumes it; packs never cross a label, so no block parameter is needed.
    local pendingPack: number? = nil
    -- Constructor windows, keyed by the 0-based index of their NEWTABLE: an
    -- ordered window carries its make_table value (`table`) through the window; a literal window collects its fields in
    -- store order (`fields`) and its tail pack (`tail`) for the completing member.
    local windows: { [number]: any } = {}
    for index, instruction in fnHandoff.instructions do
        assert(table.find({ "constant", "move", "binary", "unary", "concat", "jump", "branch", "return", "environment_get", "environment_set", "call", "namecall", "varargs", "new_table", "table_get", "table_set", "set_list", "iteration_prepare", "iteration_loop", "logical", "closure", "upvalue_get", "upvalue_set", "close_upvalues" }, instruction.kind) ~= nil,
            "unsupported handoff instruction kind")
        -- close_upvalues is transparent to the open protocol: a pending pack passes through its empty block to the
        -- next instruction (the adapter refuses a label on such a close).
        local transparent = instruction.kind == "close_upvalues"
        if not transparent then
            assert((pendingPack ~= nil) == (instruction.consumes_pack_from ~= nil), "open pack not adjacent to its consumer")
        end
        local consumed: number? = if transparent then nil else pendingPack
        if not transparent then
            pendingPack = nil
        end
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
        elseif instruction.kind == "logical" then
            -- AND/OR: R(a) = R(b) when R(b) is falsy, else R(c) (`or`: the reverse). The source
            -- frontend's short-circuit form (luau/ast_frontend_control.luau:144-194): a branch on R(b) into logical_right (edge
            -- argument R(c)) or logical_short (edge argument R(b)), joined by logical_join, whose one parameter is the result.
            -- The join becomes this instruction's block, so the tail below writes R(a) there and jumps to the next instruction's
            -- block. The helper blocks carry this instruction's decoded_record evidence.
            local isAnd = instruction.operator == "and"
            local right = builder:reserveBlock(irFunction, { name_hint = "logical_right", evidence = blockEvidence })
            local short = builder:reserveBlock(irFunction, { name_hint = "logical_short", evidence = blockEvidence })
            local join = builder:reserveBlock(irFunction, { name_hint = "logical_join", evidence = blockEvidence })
            local joined = builder:addBlockParameter(join, IR.Types.dynamic(), "logical_result")
            builder:finalizeBlock(block, IR.Terminator.branch(reads[1],
                IR.Edge(if isAnd then right else short), IR.Edge(if isAnd then short else right)))
            builder:finalizeBlock(right, IR.Terminator.jump(IR.Edge(join, { reads[2] })))
            builder:finalizeBlock(short, IR.Terminator.jump(IR.Edge(join, { reads[1] })))
            block = join
            result = joined
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
            local effects = if instruction.kind == "namecall" then IR.Effects.namecall() else IR.Effects.dynamicCall()
            if instruction.produces_pack_at ~= nil then
                -- Open results: variadic result arity and an open pack, which the builder gives the
                -- producer block's evidence (an unevidenced pack is refused); a consumed pack is
                -- the argument pack. The new pack is pending for the next block.
                local options = { effects = effects, evidence = blockEvidence }
                local _, pack
                if instruction.kind == "namecall" then
                    _, pack = builder:addOpenNamecall(block, reads[1], instruction.method, arguments, options, consumed)
                else
                    _, pack = builder:addOpenCall(block, reads[1], arguments, options, consumed)
                end
                pendingPack = pack
            else
                local resultSpecs = {}
                for _ = 1, instruction.result_count do
                    table.insert(resultSpecs, { type = IR.Types.dynamic() })
                end
                local arity = IR.ResultArity.fixed(instruction.result_count)
                local operation = if instruction.kind == "namecall"
                    then IR.Operation.namecall(reads[1], instruction.method, arguments, arity, consumed)
                    else IR.Operation.call(reads[1], arguments, arity, consumed)
                local _, values = builder:addInstruction(block, operation, resultSpecs, { effects = effects, evidence = blockEvidence })
                results = values
            end
        elseif instruction.kind == "varargs" then
            -- GETVARARGS reads the worker's vararg pack: open, that pack becomes the pending pack
            -- without an instruction; fixed, adjust_pack takes its first `count` values (dynamic results, effects pure).
            assert(varargPack ~= nil, "varargs outside a variadic worker")
            if instruction.produces_pack_at ~= nil then
                pendingPack = varargPack
            else
                local resultSpecs = {}
                for _ = 1, instruction.count do
                    table.insert(resultSpecs, { type = IR.Types.dynamic() })
                end
                local _, values = builder:addInstruction(block, IR.Operation.adjustPack(varargPack), resultSpecs, { effects = IR.Effects.pure(), evidence = blockEvidence })
                results = values
            end
        elseif instruction.kind == "new_table" then
            -- The source frontend's table constructs (luau/ast_frontend_tables.luau). A literal window emits nothing at its
            -- NEWTABLE (lowerLiteral, :145-191); a plain NEWTABLE, or the NEWTABLE of an ordered window (lowerOrdered,
            -- :87-143), is make_table, typed table, with tableConstructor effects.
            local window = instruction.constructor
            if window ~= nil and window.mode == "literal" then
                windows[window.create] = { fields = {} }
            else
                assert(window == nil or window.mode == "ordered", "unknown constructor window mode")
                result = value(IR.Operation.makeTable(), IR.Types.table(), IR.Effects.tableConstructor())
                if window ~= nil then
                    windows[window.create] = { table = result }
                end
            end
        elseif instruction.kind == "table_get" then
            -- A semantic read (never the raw form): reads[1] is the table, the key is reads[2]
            -- or a KS key's string constant (pure).
            local key = if instruction.key_constant ~= nil
                then value(IR.Operation.constant(IR.Literal.string(instruction.key_constant.string)), IR.Types.string(), IR.Effects.pure())
                else reads[2]
            result = value(IR.Operation.tableGet(reads[1], key), IR.Types.dynamic(), IR.Effects.semanticTableRead())
        elseif instruction.kind == "table_set" then
            -- A semantic write. A plain store reads the table first; a window member reads only its key and value registers
            -- and stores into the window: a keyed field of a literal window, or a table_set on the carried make_table value.
            local window = instruction.constructor
            local state = if window ~= nil then windows[window.create] else nil
            local key = if instruction.key_constant ~= nil
                then value(IR.Operation.constant(IR.Literal.string(instruction.key_constant.string)), IR.Types.string(), IR.Effects.pure())
                else reads[if window ~= nil then 1 else 2]
            local stored = reads[#reads]
            if window ~= nil and window.mode == "literal" then
                table.insert(state.fields, IR.TableConstructorField.keyed(key, stored))
            else
                local tableValue = if state ~= nil then state.table else reads[1]
                builder:addInstruction(block, IR.Operation.tableSet(tableValue, key, stored), {}, { effects = IR.Effects.semanticTableWrite(), evidence = blockEvidence })
            end
        elseif instruction.kind == "set_list" then
            -- SETLIST is always a window member (the adapter refuses it elsewhere); reads are its values in index order. A
            -- literal window takes them as list fields and the consumed pack as its tail; an ordered window writes each on
            -- its integer key and the consumed pack with table_set_pack (rawTableWrite, as lowerOrdered does).
            local window = instruction.constructor
            local state = windows[window.create]
            if window.mode == "literal" then
                for _, item in reads do
                    table.insert(state.fields, IR.TableConstructorField.list(item))
                end
                state.tail = consumed
            else
                for slot, item in reads do
                    local key = value(IR.Operation.constant(IR.Literal.integer(tostring(instruction.first_index + slot - 1))), IR.Types.integer(), IR.Effects.pure())
                    builder:addInstruction(block, IR.Operation.tableSet(state.table, key, item), {}, { effects = IR.Effects.semanticTableWrite(), evidence = blockEvidence })
                end
                if consumed ~= nil then
                    builder:addInstruction(block, IR.Operation.tableSetPack(state.table, instruction.first_index + #reads, consumed), {}, { effects = IR.Effects.rawTableWrite(), evidence = blockEvidence })
                end
            end
        elseif instruction.kind == "closure" then
            -- NEWCLOSURE + CAPTURE: the source frontend's make_closure of the created function, pure,
            -- with one binding per capture in upvalue order: VAL the value read of the register at the closure (reads are
            -- the VAL registers in capture order), REF the register's place, UPVAL this function's own capture, and self a
            -- place of its own (closure_self_<i>) written with the new closure.
            local bindings = {}
            local valueSlot = 0
            local selfPlace: number? = nil
            for _, capture in instruction.captures do
                if capture.mode == "value" then
                    valueSlot += 1
                    table.insert(bindings, IR.CaptureBinding.value(reads[valueSlot]))
                elseif capture.mode == "reference" then
                    table.insert(bindings, IR.CaptureBinding.place(places[capture.register]))
                elseif capture.mode == "self" then
                    if selfPlace == nil then
                        selfPlace = builder:addLocalPlace(irFunction, IR.Types.dynamic(), `closure_self_{index}`, blockEvidence)
                    end
                    table.insert(bindings, IR.CaptureBinding.place(selfPlace :: number))
                else
                    assert(capture.mode == "upvalue", "unknown capture mode")
                    local own = ownCaptures[capture.upvalue + 1]
                    table.insert(bindings, if own.class == "value" then IR.CaptureBinding.value(own.value) else IR.CaptureBinding.place(own.place))
                end
            end
            result = value(IR.Operation.makeClosure(irFunctionOf[instruction["function"]], bindings), IR.Types.functionValue(), IR.Effects.pure())
            if selfPlace ~= nil then
                builder:addInstruction(block, IR.Operation.placeWrite(selfPlace, result :: number), {}, { effects = IR.Effects.placeWrite(), evidence = blockEvidence })
            end
        elseif instruction.kind == "upvalue_get" then
            -- GETUPVAL: a value capture is the captured value itself; a place capture is read.
            local own = ownCaptures[instruction.upvalue + 1]
            if own.class == "value" then
                result = own.value
            else
                result = value(IR.Operation.placeRead(own.place), IR.Types.dynamic(), IR.Effects.placeRead())
            end
        elseif instruction.kind == "upvalue_set" then
            -- SETUPVAL writes a place capture (the adapter refuses it on a value capture).
            local own = ownCaptures[instruction.upvalue + 1]
            assert(own.class == "place", "SETUPVAL on a value capture")
            builder:addInstruction(block, IR.Operation.placeWrite(own.place, reads[1]), {}, { effects = IR.Effects.placeWrite(), evidence = blockEvidence })
        end
        -- close_upvalues lowers to nothing: the adapter refuses every later access of a register it detaches.
        if instruction.complete and instruction.constructor.mode == "literal" then
            -- The completing member of a literal window builds the constructor from its fields in store order and the tail
            -- pack, with tableConstructor effects, and writes R(t) there (only where R(t) has a place).
            local state = windows[instruction.constructor.create]
            local constructed = value(IR.Operation.makeTableLiteral(state.fields, state.tail), IR.Types.table(), IR.Effects.tableConstructor())
            if places[instruction.table] ~= nil then
                builder:addInstruction(block, IR.Operation.placeWrite(places[instruction.table], constructed), {}, { effects = IR.Effects.placeWrite(), evidence = blockEvidence })
            end
        end
        if result ~= nil and places[instruction.writes[1]] ~= nil then
            builder:addInstruction(block, IR.Operation.placeWrite(places[instruction.writes[1]], result), {}, { effects = IR.Effects.placeWrite(), evidence = blockEvidence })
        end
        if results ~= nil then
            -- call, namecall and fixed varargs: result i goes to writes[i], only where that register has a place.
            for slot, reg in instruction.writes do
                if places[reg] ~= nil then
                    builder:addInstruction(block, IR.Operation.placeWrite(places[reg], results[slot]), {}, { effects = IR.Effects.placeWrite(), evidence = blockEvidence })
                end
            end
        end
        if instruction.kind == "iteration_prepare" then
            -- The prepare block reads the initial state (reads are already in header order) and enters the header
            -- with the initial transition flag `true`; the later flag `false` is made here too, as the source frontend does.
            local state = loops[index - 1]
            local first = value(IR.Operation.constant(IR.Literal.boolean(true)), IR.Types.boolean(), IR.Effects.pure())
            state.later = value(IR.Operation.constant(IR.Literal.boolean(false)), IR.Types.boolean(), IR.Effects.pure())
            builder:finalizeBlock(block, IR.Terminator.jump(IR.Edge(state.header, { reads[1], reads[2], reads[3], first })))
            -- The header: exactly one transition, branching on has_value to the body entry or the region's exit.
            local p = state.state
            local resultSpecs
            local operation
            if state.numeric then
                operation = IR.Operation.numericForNext(p[1], p[2], p[3], p[4])
                resultSpecs = { { type = IR.Types.boolean() }, { type = IR.Types.number() }, { type = IR.Types.number() }, { type = IR.Types.number() } }
            else
                operation = IR.Operation.genericForNext(p[1], p[2], p[3], p[4], #state.variables)
                resultSpecs = { { type = IR.Types.boolean() }, { type = IR.Types.dynamic() }, { type = IR.Types.dynamic() } }
                for _ = 1, #state.variables do
                    table.insert(resultSpecs, { type = IR.Types.dynamic() })
                end
            end
            local effects = if state.numeric then IR.Effects.numericForNext() else IR.Effects.genericForNext()
            local _, transition = builder:addInstruction(state.header, operation, resultSpecs, { effects = effects, evidence = state.evidence })
            state.transition = transition
            local bodyArguments = {}
            for slot = 1, #state.variables do
                table.insert(bodyArguments, transition[3 + slot])
            end
            builder:finalizeBlock(state.header, IR.Terminator.branch(transition[1],
                IR.Edge(state.body, bodyArguments), IR.Edge(blocks[state.loop.exit + 1])))
            -- The body entry writes each loop variable to its register's place (only where a place exists).
            for slot, reg in state.loop.variables do
                if places[reg] ~= nil then
                    builder:addInstruction(state.body, IR.Operation.placeWrite(places[reg], state.variables[slot]), {}, { effects = IR.Effects.placeWrite(), evidence = state.evidence })
                end
            end
            builder:finalizeBlock(state.body, IR.Terminator.jump(IR.Edge(blocks[index + 1])))
        elseif instruction.kind == "iteration_loop" then
            -- The latch re-enters the header with the transition's own state and the later flag:
            -- numeric [control, limit, step] = results 4, 2, 3; generic [iterator, state, control] = results 2, 3, 4.
            local state = loops[instruction.loop.prepare]
            local t = state.transition
            local arguments = if state.numeric then { t[4], t[2], t[3], state.later } else { t[2], t[3], t[4], state.later }
            builder:finalizeBlock(block, IR.Terminator.jump(IR.Edge(state.header, arguments)))
        elseif instruction.kind == "return" then
            -- An open return returns its prefix reads and then the consumed pack.
            if consumed == nil then
                builder:finalizeBlock(block, IR.Terminator.returnValues(reads))
            elseif #reads == 0 then
                builder:finalizeBlock(block, IR.Terminator.returnPack(consumed))
            else
                builder:finalizeBlock(block, IR.Terminator.returnExpanded(reads, consumed))
            end
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
    builder:finalizeFunction(irFunction)
end

liftFunction(handoff, worker, handoff.function_index, evidence)
for _, fn in nested do
    liftFunction(fn, irFunctionOf[fn.function_index], fn.function_index, evidenceOf[fn.function_index])
end
local _, closure = builder:addInstruction(rootBlock, IR.Operation.makeClosure(worker, {}), { { type = IR.Types.functionValue() } }, { effects = IR.Effects.pure(), evidence = { evidence } })
builder:finalizeBlock(rootBlock, IR.Terminator.returnValues(closure))
builder:finalizeFunction(root)
fs.writeFile(process.args[2], IR.encodeJson(builder:finish(), true) .. "\n")
