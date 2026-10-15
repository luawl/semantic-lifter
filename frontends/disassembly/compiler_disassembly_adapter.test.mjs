import assert from 'node:assert/strict';
import test from 'node:test';
import { parseDisassembly } from './compiler_disassembly_adapter.mjs';

const listing = `Function 0 (worker):
K0: 0
K1: 1
LOADK R2 K0 [0]
L0: JUMPIFNOTLT R2 R1 L1
LOADK R3 K1 [1]
ADD R2 R2 R3
JUMPBACK L0
L1: RETURN R2 1
`;

test('disassembly preserves register data and inverted branch polarity', () => {
  const result = parseDisassembly(listing);
  assert.deepEqual(result.registers, [0, 1, 2, 3]);
  assert.equal(result.instructions[1].operator, 'less');
  assert.equal(result.instructions[1].inverted, true);
  assert.equal(result.instructions[1].target, 5);
  assert.deepEqual(result.instructions[5].reads, [2]);
});

test('unsupported operations cannot silently become no-ops', () => {
  assert.throws(() => parseDisassembly(listing.replace('ADD R2 R2 R3', 'GETUPVAL R2 0')), /unsupported opcode GETUPVAL/);
  assert.throws(() => parseDisassembly(listing.replace('ADD R2 R2 R3', 'FORGPREP_NEXT R2 L1')), /unsupported opcode FORGPREP_NEXT/);
});

test('missing constants, labels, and open return protocols are rejected', () => {
  assert.throws(() => parseDisassembly(listing.replace('LOADK R2 K0', 'LOADK R2 K9')), /constant is absent/);
  assert.throws(() => parseDisassembly(listing.replace('R2 R1 L1', 'R2 R1 L9')), /unknown label/);
  assert.throws(() => parseDisassembly(listing.replace('RETURN R2 1', 'RETURN R2 -1')), /open return/);
});

test('definite assignment rejects a value initialized on only one branch', () => {
  assert.throws(() => parseDisassembly(`Function 0 (worker):
JUMPIF R0 L1
LOADN R2 1
L1: RETURN R2 1
`), /uninitialized R2/);
});

test('entry back edges cannot invent initial register values', () => {
  assert.throws(() => parseDisassembly(`Function 0 (worker):
L0: ADD R2 R2 R0
JUMPIF R1 L0
RETURN R2 1
`), /uninitialized R2/);
});

test('format changes and invalid register ranges fail closed', () => {
  assert.throws(() => parseDisassembly(listing.replace('R3 K1', 'R256 K1')), /register range/);
  assert.throws(() => parseDisassembly(listing.replace('K1: 1', 'K1: nan')), /unsupported constant/);
  assert.throws(() => parseDisassembly(listing + 'LOADN R2 1\n'), /falls off end/);
  assert.throws(() => parseDisassembly('Function 1 (worker):\nRETURN R0 1\n'), /selected function is absent/);
});

// Task T2.1 (T2-ADAPTER step 1). Each excerpt is `Function 0 (??):` plus verbatim -O0 listing lines of the
// author-owned diagnosis programs (p07, p09, p10, p11, p16 and the skeptic's s01_loadb_skip), joined with `\n`.
const excerpt = (...lines) => ['Function 0 (??):', ...lines].join('\n') + '\n';

test('string constants decode exactly', () => {
  const cases = [
    [["K1: 'it's \"quoted\"'", "LOADK R3 K1 ['it's \"quoted\"']", 'RETURN R3 1'], 'it\'s "quoted"', 3],
    [["K5: 'K9: 1'", "LOADK R7 K5 ['K9: 1']", 'RETURN R7 1'], 'K9: 1', 7],
    [["K6: ''", "LOADK R8 K6 ['']", 'RETURN R8 1'], '', 8],
    [["K0: 'thirty-one bytes long string!!!'", "LOADK R2 K0 ['thirty-one bytes long string!!!']", 'RETURN R2 1'],
      'thirty-one bytes long string!!!', 2],
    [["K3: 'br]acket'", "LOADK R5 K3 ['br]acket']", 'RETURN R5 1'], 'br]acket', 5],
  ];
  for (const [lines, body, target] of cases) {
    const [instruction] = parseDisassembly(excerpt(...lines)).instructions;
    assert.equal(instruction.kind, 'constant');
    assert.deepEqual(instruction.value, { string: body });
    assert.deepEqual(instruction.writes, [target]);
  }
});

test('undecodable strings refuse with a reason', () => {
  assert.throws(() => parseDisassembly(excerpt("K5: 'exactly thirty-two bytes long!!!'...",
    "LOADK R7 K5 ['exactly thirty-two bytes long!!!'...]", 'RETURN R7 1')),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'unsupported_constant' && /truncated/.test(error.message));
  assert.throws(() => parseDisassembly(excerpt("K1: 'line\\x0Abreak'", "LOADK R3 K1 ['line\\x0Abreak']", 'RETURN R3 1')),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'unsupported_constant' && /escape/.test(error.message));
  assert.throws(() => parseDisassembly(excerpt("K2: '\\'", "LOADK R4 K2 ['\\']", 'RETURN R4 1')),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'unsupported_constant' && /escape/.test(error.message));
  assert.throws(() => parseDisassembly(excerpt("K0: 'caf�'", "LOADK R2 K0 ['caf�']", 'RETURN R2 1')),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'unsupported_constant' && /not exact UTF-8/.test(error.message));
});

test('constants decode where they are used', () => {
  const result = parseDisassembly(excerpt('K3: {...}', 'K4: 1', 'LOADK R2 K4 [1]', 'RETURN R2 1'));
  assert.deepEqual(result.instructions[0].value, { number: 1 });
});

test('LOADB, LENGTH and CONCAT lower to constant, unary and concat', () => {
  const { instructions } = parseDisassembly(excerpt("K0: 'x'", 'K1: 1', 'LOADB R2 1', "LOADK R4 K0 ['x']", 'MOVE R5 R0',
    'CONCAT R3 R4 R5', 'LENGTH R4 R3', 'JUMPIFNOT R2 L0', 'JUMPIFEQ R0 R1 L0', 'LOADK R6 K1 [1]', 'ADD R5 R4 R6',
    'RETURN R5 1', 'L0: RETURN R4 1'));
  const fields = (instruction, keys) => Object.fromEntries(keys.map((key) => [key, instruction[key]]));
  assert.deepEqual(fields(instructions[0], ['op', 'kind', 'value', 'reads', 'writes']),
    { op: 'LOADB', kind: 'constant', value: { boolean: true }, reads: [], writes: [2] });
  assert.deepEqual(fields(instructions[3], ['op', 'kind', 'reads', 'writes']),
    { op: 'CONCAT', kind: 'concat', reads: [4, 5], writes: [3] });
  assert.deepEqual(fields(instructions[4], ['op', 'kind', 'operator', 'reads', 'writes']),
    { op: 'LENGTH', kind: 'unary', operator: 'length', reads: [3], writes: [4] });
});

test('a LOADB skip resolves to its labelled target', () => {
  const skip = ['JUMPIFLT R1 R0 L0', 'LOADB R2 0 +1', 'L0: LOADB R2 1', 'L1: RETURN R2 1'];
  const { instructions } = parseDisassembly(excerpt(...skip));
  assert.deepEqual(instructions[1].value, { boolean: false });
  assert.deepEqual(instructions[1].writes, [2]);
  assert.deepEqual(instructions[1].successors, [3]);
  assert.deepEqual(instructions[2].value, { boolean: true });
  assert.deepEqual(instructions[2].successors, [3]);
  assert.throws(() => parseDisassembly(excerpt(...skip.slice(0, 3), 'RETURN R2 1')),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'relative_skip_unsupported');
  assert.throws(() => parseDisassembly(excerpt(skip[0], 'LOADB R2 0 +2', ...skip.slice(2))),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'relative_skip_unsupported');
});

test('refusals are typed and keep their messages', () => {
  assert.throws(() => parseDisassembly(listing.replace('ADD R2 R2 R3', 'FORNPREP R2 L1')),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'iteration_pair_mismatch' && error.opcode === 'FORNPREP'
      && error.line_number === 7 && /FORNPREP R2 has no matching loop instruction at disassembly line 7/.test(error.message));
  assert.throws(() => parseDisassembly(listing.replace('LOADK R2 K0', 'LOADK R2 K9')),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'operand_form' && error.line_number === 4
      && /constant is absent/.test(error.message));
  assert.throws(() => parseDisassembly(listing.replace('R2 R1 L1', 'R2 R1 L9')),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'listing_structure' && error.line_number === 5
      && /unknown label L9/.test(error.message));
  assert.throws(() => parseDisassembly(listing.replace('RETURN R2 1', 'RETURN R2 -1')),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'open_consumer_without_producer' && error.line_number === 9
      && /open return/.test(error.message));
  assert.throws(() => parseDisassembly(`Function 0 (worker):
JUMPIF R0 L1
LOADN R2 1
L1: RETURN R2 1
`), (error) => error.name === 'DisassemblyRefusal' && error.code === 'uninitialized_register'
    && /uninitialized R2 at disassembly line 4/.test(error.message));
  assert.throws(() => parseDisassembly(listing, { parameter_count: -1 }),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'invalid_options');
});

test('the handoff is v2 with a caller-declared is_variadic', () => {
  assert.equal(parseDisassembly(listing).schema_version, 'compiler_disassembly_handoff_v2');
  const handoff = parseDisassembly(listing);
  assert.equal(handoff.is_variadic, false);
  assert.equal(handoff.signature_origin, 'caller-declared; text disassembly does not encode arity');
  assert.equal(handoff.scope, 'selected capture-free function; remaining compiled functions are not lifted');
  assert.equal(parseDisassembly(listing, { is_variadic: true }).is_variadic, true);
  assert.throws(() => parseDisassembly(listing, { is_variadic: 'yes' }),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'invalid_options');
});

// Task T2.2 (T2-ADAPTER step 2). Excerpts are verbatim listing lines of the author-owned diagnosis programs:
// p01_globals at -O0 (Function 0) and p02_import at -O1 (lines 1-4 and 8, plus a return) for the GETIMPORT pin.
test('globals lower to named environment accesses', () => {
  const { instructions } = parseDisassembly(excerpt("K0: 'counter'", 'ADD R2 R0 R1', "SETGLOBAL R2 K0 ['counter']",
    "GETGLOBAL R2 K0 ['counter']", 'RETURN R2 1'));
  const fields = (instruction) => Object.fromEntries(['op', 'kind', 'name', 'reads', 'writes']
    .map((key) => [key, instruction[key]]));
  assert.deepEqual(fields(instructions[1]), { op: 'SETGLOBAL', kind: 'environment_set', name: 'counter', reads: [2], writes: [] });
  assert.deepEqual(fields(instructions[2]), { op: 'GETGLOBAL', kind: 'environment_get', name: 'counter', reads: [], writes: [2] });
});

test('global names must be identifier string constants', () => {
  assert.throws(() => parseDisassembly(listing.replace('ADD R2 R2 R3', 'GETGLOBAL R2 K1')),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'constant_kind_mismatch'
      && /GETGLOBAL: K1 is not a string/.test(error.message));
  assert.throws(() => parseDisassembly(excerpt("K0: 'my-name'", "GETGLOBAL R2 K0 ['my-name']", 'RETURN R2 1')),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'non_identifier_name'
      && /GETGLOBAL: K0 is not an identifier/.test(error.message));
});

test('imports stay refused at the pinned level', () => {
  assert.throws(() => parseDisassembly(excerpt("K0: 'math'", "K1: 'floor'", 'K2: math.floor', 'GETIMPORT R2 2 [math.floor]',
    'RETURN R2 1')),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'unsupported_opcode' && error.opcode === 'GETIMPORT'
      && /unsupported opcode GETIMPORT at disassembly line 5/.test(error.message));
});

// Task T2.3 (T2-ADAPTER step 3). Excerpts are verbatim -O0 listing lines of the author-owned diagnosis programs
// p03_call_fixed (lines 4, 12-14 and 19) and p05_namecall (lines 4-5 and 15-17); the declared parameter_count makes
// the registers the full listing initialises elsewhere parameters of the excerpt.
const project = (instruction, expected) => Object.fromEntries(Object.keys(expected).map((key) => [key, instruction[key]]));
const callExcerpt = ["K2: 'tostring'", "GETGLOBAL R3 K2 ['tostring']", 'MOVE R4 R2', 'CALL R3 1 0', 'RETURN R2 1'];
const namecallExcerpt = ['K2: 2', "K3: 'rep'", 'LOADK R7 K2 [2]', "NAMECALL R5 R5 K3 ['rep']", 'CALL R5 2 1', 'RETURN R5 1'];

test('fixed calls name callee, arguments and results', () => {
  const statement = { op: 'CALL', kind: 'call', callee: 3, arguments: [4], result_count: 0, reads: [3, 4], writes: [],
    clobbers_from: 3 };
  const { instructions } = parseDisassembly(excerpt(...callExcerpt), { parameter_count: 3 });
  assert.deepEqual(project(instructions[2], statement), statement);
  const results = { kind: 'call', callee: 3, arguments: [4], result_count: 2, reads: [3, 4], writes: [3, 4], clobbers_from: 5 };
  const [call] = parseDisassembly(excerpt('CALL R3 1 2', 'RETURN R3 2'), { parameter_count: 5 }).instructions;
  assert.deepEqual(project(call, results), results);
});

test('a call clobbers its frame', () => {
  const lines = [...callExcerpt.slice(0, 4), 'MOVE R9 R4', ...callExcerpt.slice(4)];
  assert.throws(() => parseDisassembly(excerpt(...lines), { parameter_count: 3 }),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'uninitialized_register'
      && /uninitialized R4 at disassembly line 6/.test(error.message));
});

test('NAMECALL fuses with its CALL', () => {
  const { instructions } = parseDisassembly(excerpt(...namecallExcerpt), { parameter_count: 6 });
  assert.equal(instructions.length, 3);
  const fused = { op: 'NAMECALL', kind: 'namecall', receiver: 5, method: 'rep', arguments: [7], result_count: 1,
    reads: [5, 7], writes: [5], clobbers_from: 6, line_number: 5, line_numbers: [5, 6] };
  assert.deepEqual(project(instructions[1], fused), fused);
  const refused = (code) => (error) => error.name === 'DisassemblyRefusal' && error.code === code;
  assert.throws(() => parseDisassembly(excerpt(...namecallExcerpt.slice(0, 4), 'MOVE R9 R0', ...namecallExcerpt.slice(4)),
    { parameter_count: 6 }), refused('namecall_without_call'));
  assert.throws(() => parseDisassembly(excerpt(...namecallExcerpt.map((line) => (line === 'CALL R5 2 1' ? 'L0: CALL R5 2 1' : line))),
    { parameter_count: 6 }), refused('label_inside_namecall'));
  assert.throws(() => parseDisassembly(excerpt(...namecallExcerpt.map((line) => line.replaceAll("'rep'", "'r p'"))),
    { parameter_count: 6 }), refused('non_identifier_name'));
});

// Task T2.4 (T2-ADAPTER step 4). Excerpts are verbatim -O0 listing lines of the author-owned diagnosis programs
// p04_call_open (lines 15-16 and 24-25), open_result_return (lines 7-8 and 18-23), p16_edges (lines 10 and 24-26, plus a
// fixed return) and varargs_select_sum (Function 0, lines 1-26); the declared parameter_count makes the registers the
// full listing initialises elsewhere parameters of the excerpt.
const openCallExcerpt = ['CALL R2 1 -1', 'RETURN R2 -1'];
const varargsSelectSum = ["K0: 'select'", "K1: '#'", 'K2: 0', 'K3: 1', "GETGLOBAL R0 K0 ['select']", "LOADK R1 K1 ['#']",
  'GETVARARGS R2 -1', 'CALL R0 -1 1', 'GETVARARGS R1 2', 'LOADK R3 K2 [0]', 'LOADK R4 K3 [1]', 'L0: JUMPIFNOTLE R4 R0 L1',
  "GETGLOBAL R5 K0 ['select']", 'MOVE R6 R4', 'GETVARARGS R7 -1', 'CALL R5 -1 1', 'ADD R3 R3 R5', 'LOADK R5 K3 [1]',
  'ADD R4 R4 R5', 'JUMPBACK L0', 'L1: MOVE R5 R0', 'MOVE R6 R3', 'MOVE R7 R1', 'MOVE R8 R2', 'RETURN R5 4'];
const refusedAs = (code) => (error) => error.name === 'DisassemblyRefusal' && error.code === code;
const assertFields = (instructions, expected) => {
  for (const [index, fields] of Object.entries(expected)) assert.deepEqual(project(instructions[index], fields), fields);
};

test('open results flow to the adjacent consumer', () => {
  assertFields(parseDisassembly(excerpt(...openCallExcerpt), { parameter_count: 4 }).instructions, {
    0: { kind: 'call', callee: 2, arguments: [3], result_count: null, produces_pack_at: 2, reads: [2, 3], writes: [],
      clobbers_from: 2 },
    1: { kind: 'return', reads: [], consumes_pack_from: 2 },
  });
  assertFields(parseDisassembly(excerpt('CALL R3 1 -1', 'RETURN R2 -1'), { parameter_count: 5 }).instructions, {
    1: { kind: 'return', reads: [2], consumes_pack_from: 3 },
  });
  assertFields(parseDisassembly(excerpt("K5: 'select'", "K6: '#'", "GETGLOBAL R5 K5 ['select']", "LOADK R6 K6 ['#']",
    'GETVARARGS R7 -1', 'CALL R5 -1 -1', 'CALL R2 -1 -1', 'RETURN R1 -1'), { parameter_count: 5, is_variadic: true }).instructions, {
    2: { kind: 'varargs', count: null, produces_pack_at: 7 },
    3: { kind: 'call', callee: 5, arguments: [6], consumes_pack_from: 7, result_count: null, produces_pack_at: 5 },
    4: { kind: 'call', callee: 2, arguments: [3, 4], consumes_pack_from: 5, result_count: null, produces_pack_at: 2 },
    5: { kind: 'return', reads: [1], consumes_pack_from: 2 },
  });
  assertFields(parseDisassembly(excerpt("K8: 'rep'", 'CALL R10 1 -1', "NAMECALL R8 R6 K8 ['rep']", 'CALL R8 -1 1', 'RETURN R8 1'),
    { parameter_count: 12 }).instructions, {
    0: { kind: 'call', callee: 10, arguments: [11], produces_pack_at: 10 },
    1: { kind: 'namecall', receiver: 6, method: 'rep', arguments: [], consumes_pack_from: 10, result_count: 1, writes: [8],
      clobbers_from: 9 },
  });
});

test('varargs need a declared variadic signature', () => {
  assertFields(parseDisassembly(excerpt(...varargsSelectSum), { parameter_count: 0, is_variadic: true }).instructions, {
    2: { op: 'GETVARARGS', kind: 'varargs', count: null, produces_pack_at: 2, writes: [], clobbers_from: 2 },
    3: { op: 'CALL', kind: 'call', callee: 0, arguments: [1], consumes_pack_from: 2, result_count: 1, writes: [0],
      clobbers_from: 1 },
    4: { op: 'GETVARARGS', kind: 'varargs', count: 2, writes: [1, 2] },
  });
  assert.throws(() => parseDisassembly(excerpt(...varargsSelectSum), { parameter_count: 0 }),
    refusedAs('varargs_in_non_variadic_function'));
});

test('an open pack must be consumed immediately', () => {
  assert.throws(() => parseDisassembly(excerpt(openCallExcerpt[0], 'MOVE R9 R0', openCallExcerpt[1]), { parameter_count: 4 }),
    refusedAs('open_pack_not_consumed'));
  assert.throws(() => parseDisassembly(excerpt(openCallExcerpt[0], `L0: ${openCallExcerpt[1]}`), { parameter_count: 4 }),
    refusedAs('open_pack_crosses_label'));
  assert.throws(() => parseDisassembly(listing.replace('RETURN R2 1', 'RETURN R2 -1')),
    (error) => refusedAs('open_consumer_without_producer')(error) && /open return/.test(error.message));
});

// Task T2.5 (T2-ADAPTER step 5). The three program listings are verbatim -O0 Function 0 listings (REMARK lines
// included) of the author-owned diagnosis programs p06_table_access (lines 1-27), p13_long_list (lines 1-57) and
// p17_ctor_order (lines 1-37). The ordered probe is the author-owned program written for this plan,
// research/fixtures/disassembly/ordered_constructor_probe.luau (`local t = {[selector] = 1, budget}`), Function 0
// listing lines 1-10. The template excerpt is p07_table_ctor lines 5 and 18 plus a return.
const p06TableAccess = `Function 0 (??):
K0: 1
K1: 'b'
K2: 2
K3: 300
K4: 7
REMARK allocation: table hash 0
NEWTABLE R2 0 0
LOADK R3 K0 [1]
SETTABLE R0 R2 R3
SETTABLEKS R1 R2 K1 ['b']
LOADK R3 K2 [2]
ADD R4 R0 R1
SETTABLE R4 R2 R3
LOADK R4 K3 [300]
LOADK R5 K4 [7]
SETTABLE R5 R2 R4
LOADK R8 K0 [1]
GETTABLE R7 R2 R8
GETTABLEKS R8 R2 K1 ['b']
ADD R6 R7 R8
GETTABLE R7 R2 R3
ADD R5 R6 R7
LOADK R7 K3 [300]
GETTABLE R6 R2 R7
ADD R4 R5 R6
RETURN R4 1
`;
const p13LongList = `Function 0 (??):
K0: 1
K1: 2
K2: 3
K3: 4
K4: 5
K5: 6
K6: 7
K7: 8
K8: 9
K9: 10
K10: 11
K11: 12
K12: 13
K13: 14
K14: 15
K15: 16
K16: 17
K17: 18
K18: 19
K19: 20
REMARK allocation: table array 22
NEWTABLE R2 0 22
LOADK R3 K0 [1]
LOADK R4 K1 [2]
LOADK R5 K2 [3]
LOADK R6 K3 [4]
LOADK R7 K4 [5]
LOADK R8 K5 [6]
LOADK R9 K6 [7]
LOADK R10 K7 [8]
LOADK R11 K8 [9]
LOADK R12 K9 [10]
LOADK R13 K10 [11]
LOADK R14 K11 [12]
LOADK R15 K12 [13]
LOADK R16 K13 [14]
LOADK R17 K14 [15]
LOADK R18 K15 [16]
SETLIST R2 R3 16 [1]
LOADK R3 K16 [17]
LOADK R4 K17 [18]
LOADK R5 K18 [19]
LOADK R6 K19 [20]
MOVE R7 R0
MOVE R8 R1
SETLIST R2 R3 6 [17]
REMARK allocation: table array 2
NEWTABLE R3 0 2
MOVE R4 R0
MOVE R5 R1
GETVARARGS R6 -1
SETLIST R3 R4 -1 [1]
LENGTH R5 R2
LENGTH R6 R3
ADD R4 R5 R6
RETURN R4 1
`;
const p17CtorOrder = `Function 0 (??):
K0: 'b'
K1: 'math'
K2: 'abs'
K3: 'max'
K4: 1
K5: 'c'
K6: 7
K7: 2
REMARK allocation: table hash 2 array 2
NEWTABLE R2 2 2
LOADK R5 K0 ['b']
GETGLOBAL R6 K1 ['math']
GETTABLEKS R6 R6 K2 ['abs']
MOVE R7 R1
CALL R6 1 1
SETTABLE R6 R2 R5
GETGLOBAL R3 K1 ['math']
GETTABLEKS R3 R3 K3 ['max']
MOVE R4 R0
LOADK R5 K4 [1]
CALL R3 2 1
SETLIST R2 R3 1 [1]
LOADK R5 K5 ['c']
SETTABLE R0 R2 R5
LOADK R3 K6 [7]
SETLIST R2 R3 1 [2]
LOADK R7 K4 [1]
GETTABLE R6 R2 R7
LOADK R8 K7 [2]
GETTABLE R7 R2 R8
ADD R5 R6 R7
GETTABLEKS R6 R2 K0 ['b']
ADD R4 R5 R6
GETTABLEKS R5 R2 K5 ['c']
ADD R3 R4 R5
RETURN R3 1
`;
const orderedConstructorProbe = `Function 0 (??):
K0: 1
REMARK allocation: table hash 1 array 1
NEWTABLE R2 1 1
LOADK R4 K0 [1]
SETTABLE R4 R2 R0
MOVE R3 R1
SETLIST R2 R3 1 [1]
LENGTH R3 R2
RETURN R3 1
`;
// Every object inherits `constructor`, so window membership is tested as an own property.
const windowMembers = (instructions) => instructions.flatMap((instruction, index) =>
  (Object.hasOwn(instruction, 'constructor') ? [index] : []));

test('tables without SETLIST lower to new_table and ordered stores', () => {
  const { instructions } = parseDisassembly(p06TableAccess);
  assertFields(instructions, {
    0: { op: 'NEWTABLE', kind: 'new_table', writes: [2] },
    2: { op: 'SETTABLE', kind: 'table_set', table: 2, key: 3, value: 0, reads: [2, 3, 0], writes: [] },
    3: { op: 'SETTABLEKS', kind: 'table_set', table: 2, key_constant: { string: 'b' }, value: 1, reads: [2, 1] },
    11: { op: 'GETTABLE', kind: 'table_get', table: 2, key: 8, reads: [2, 8], writes: [7] },
    12: { op: 'GETTABLEKS', kind: 'table_get', table: 2, key_constant: { string: 'b' }, reads: [2], writes: [8] },
  });
  assert.equal(Object.hasOwn(instructions[0], 'constructor'), false);
  assert.deepEqual(windowMembers(instructions), []);
});

test('SETLIST rebuilds the list constructor', () => {
  const { instructions } = parseDisassembly(p13LongList, { parameter_count: 2, is_variadic: true });
  assertFields(instructions, {
    17: { op: 'SETLIST', kind: 'set_list', table: 2, values: [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18],
      first_index: 1, constructor: { create: 0, mode: 'literal' } },
    24: { op: 'SETLIST', values: [3, 4, 5, 6, 7, 8], first_index: 17, constructor: { create: 0, mode: 'literal' },
      complete: true },
    29: { op: 'SETLIST', table: 3, values: [4, 5], first_index: 1, consumes_pack_from: 6,
      constructor: { create: 25, mode: 'literal' }, complete: true },
  });
  assert.equal(Object.hasOwn(instructions[17], 'complete'), false);
});

test('constructor windows keep source order and choose their mode', () => {
  const { instructions } = parseDisassembly(p17CtorOrder);
  // The NEWTABLE and its members in store order: b, the first list item, c, the second list item.
  assert.deepEqual(windowMembers(instructions), [0, 6, 12, 14, 16]);
  assertFields(instructions, {
    6: { op: 'SETTABLE', kind: 'table_set', table: 2, key_constant: { string: 'b' }, value: 6, reads: [6],
      constructor: { create: 0, mode: 'literal' } },
    12: { op: 'SETLIST', values: [3], first_index: 1, constructor: { create: 0, mode: 'literal' } },
    14: { op: 'SETTABLE', key_constant: { string: 'c' }, value: 0, reads: [0], constructor: { create: 0, mode: 'literal' } },
    16: { op: 'SETLIST', values: [3], first_index: 2, complete: true, constructor: { create: 0, mode: 'literal' } },
  });
  assert.equal(Object.hasOwn(instructions[6], 'key'), false);
  assert.equal(Object.hasOwn(instructions[14], 'key'), false);
  // The probe's key R0 is not definitely valid and its member is not the last, so the window is ordered.
  assertFields(parseDisassembly(orderedConstructorProbe).instructions, {
    2: { op: 'SETTABLE', kind: 'table_set', table: 2, key: 0, value: 4, constructor: { create: 0, mode: 'ordered' } },
    4: { op: 'SETLIST', kind: 'set_list', values: [3], first_index: 1, constructor: { create: 0, mode: 'ordered' },
      complete: true },
  });
});

test('SETLIST outside a recognisable constructor is refused', () => {
  const gap = p17CtorOrder.replace('SETLIST R2 R3 1 [2]', 'SETLIST R2 R3 1 [3]');
  assert.notEqual(gap, p17CtorOrder);
  assert.throws(() => parseDisassembly(gap), refusedAs('setlist_index_gap'));
  // The label ends the window before the c store and the second SETLIST.
  const labelled = p17CtorOrder.replace("LOADK R5 K5 ['c']", "L9: LOADK R5 K5 ['c']");
  assert.notEqual(labelled, p17CtorOrder);
  assert.throws(() => parseDisassembly(labelled), refusedAs('constructor_window_unsupported'));
});

test('record templates stay refused', () => {
  assert.throws(() => parseDisassembly(excerpt('K3: {...}', 'DUPTABLE R3 3', 'RETURN R3 1')),
    (error) => refusedAs('table_template_opaque')(error) && error.opcode === 'DUPTABLE' && error.line_number === 3);
});

// Task T4.4 (T4-ADAPTER-ITERATION). Each excerpt is the verbatim Function 0 of the -O0 -g0 listing of an author-owned
// program research/fixtures/disassembly/<name>.luau, from its `Function 0 (??):` line, CRLF removed, so listing line
// numbers are unchanged. A spliced variant applies exactly the listed `from -> to` replacements; the measured codes and
// lines are those of the T4-ADAPTER-ITERATION prototype. The supported level is -O0 -g0 (decision D3).
const it01NumericStep = `Function 0 (??):
K0: 0
K1: 2
LOADK R2 K0 [0]
MOVE R5 R0
MOVE R3 R1
LOADK R4 K1 [2]
FORNPREP R3 L1
L0: ADD R2 R2 R5
FORNLOOP R3 L0
L1: RETURN R2 1
`;
const it02NumericWritten = `Function 0 (??):
K0: 0
K1: 1
LOADK R2 K0 [0]
MOVE R5 R1
LOADK R3 K1 [1]
LOADK R7 K1 [1]
MINUS R4 R7
FORNPREP R3 L1
L0: MOVE R6 R5
MUL R6 R6 R0
ADD R2 R2 R6
FORNLOOP R3 L0
L1: RETURN R2 1
`;
const it03Pairs = `Function 0 (??):
K0: 0
K1: 'pairs'
REMARK allocation: table array 3
NEWTABLE R2 0 3
MOVE R3 R0
MOVE R4 R1
ADD R5 R0 R1
SETLIST R2 R3 3 [1]
LOADK R3 K0 [0]
GETGLOBAL R4 K1 ['pairs']
MOVE R5 R2
CALL R4 1 3
FORGPREP R4 L1
L0: MUL R9 R7 R8
ADD R3 R3 R9
L1: FORGLOOP R4 L0 2
RETURN R3 1
`;
const it04Ipairs = `Function 0 (??):
K0: 7
K1: 0
K2: 'ipairs'
REMARK allocation: table array 3
NEWTABLE R2 0 3
MOVE R3 R0
MOVE R4 R1
LOADK R5 K0 [7]
SETLIST R2 R3 3 [1]
LOADK R3 K1 [0]
GETGLOBAL R4 K2 ['ipairs']
MOVE R5 R2
CALL R4 1 3
FORGPREP R4 L1
L0: MUL R9 R7 R8
ADD R3 R3 R9
L1: FORGLOOP R4 L0 2
RETURN R3 1
`;
const it05BreakContinue = `Function 0 (??):
K0: 0
K1: 1
K2: 5
LOADK R2 K0 [0]
LOADK R5 K1 [1]
MOVE R3 R1
LOADN R4 1
FORNPREP R3 L2
L0: JUMPIFEQ R5 R0 L1
LOADK R6 K2 [5]
JUMPIFLT R6 R5 L2
ADD R2 R2 R5
L1: FORNLOOP R3 L0
L2: RETURN R2 1
`;
const it06GenericBreakContinue = `Function 0 (??):
K0: 3
K1: 4
K2: 0
K3: 'ipairs'
REMARK allocation: table array 4
NEWTABLE R2 0 4
LOADK R3 K0 [3]
MOVE R4 R0
MOVE R5 R1
LOADK R6 K1 [4]
SETLIST R2 R3 4 [1]
LOADK R3 K2 [0]
GETGLOBAL R4 K3 ['ipairs']
MOVE R5 R2
CALL R4 1 3
FORGPREP R4 L1
L0: LOADK R9 K2 [0]
JUMPIFEQ R8 R9 L1
LOADK R9 K1 [4]
JUMPIFEQ R7 R9 L2
ADD R3 R3 R8
L1: FORGLOOP R4 L0 2
L2: RETURN R3 1
`;
const it07GeneralizedNext = `Function 0 (??):
K0: 0
K1: 'next'
REMARK allocation: table array 2
NEWTABLE R2 0 2
MOVE R3 R0
MOVE R4 R1
SETLIST R2 R3 2 [1]
LOADK R3 K0 [0]
MOVE R4 R2
LOADNIL R5
LOADNIL R6
FORGPREP R4 L1
L0: ADD R9 R3 R7
ADD R3 R9 R8
L1: FORGLOOP R4 L0 2
GETGLOBAL R4 K1 ['next']
MOVE R5 R2
LOADNIL R6
FORGPREP R4 L3
L2: ADD R3 R3 R7
L3: FORGLOOP R4 L2 1
RETURN R3 1
`;
const it08Nested = `Function 0 (??):
K0: 5
K1: 0
K2: 'ipairs'
K3: 1
K4: 2
REMARK allocation: table array 3
NEWTABLE R2 0 3
MOVE R3 R0
MOVE R4 R1
LOADK R5 K0 [5]
SETLIST R2 R3 3 [1]
LOADK R3 K1 [0]
GETGLOBAL R4 K2 ['ipairs']
MOVE R5 R2
CALL R4 1 3
FORGPREP R4 L2
L0: LOADK R11 K3 [1]
MOVE R9 R8
LOADK R10 K4 [2]
FORNPREP R9 L2
L1: JUMPIFEQ R11 R0 L2
MUL R12 R7 R11
ADD R3 R3 R12
FORNLOOP R9 L1
L2: FORGLOOP R4 L0 2
RETURN R3 1
`;
const it09ReturnInside = `Function 0 (??):
K0: 0
K1: 1
LOADK R2 K0 [0]
LOADK R5 K1 [1]
MOVE R3 R1
LOADN R4 1
FORNPREP R3 L2
L0: JUMPIFNOTEQ R5 R0 L1
MOVE R6 R2
MOVE R7 R5
RETURN R6 2
L1: ADD R2 R2 R5
FORNLOOP R3 L0
L2: MOVE R3 R2
MOVE R4 R1
RETURN R3 2
`;
const iterationOptions = { function_index: 0, parameter_count: 2 };
const splice = (text, from, to) => {
  assert.ok(text.includes(from), `splice source absent: ${from}`);
  return text.replace(from, to);
};
const loopsOf = (instructions) => instructions.filter((instruction) => instruction.kind === 'iteration_prepare')
  .map((instruction) => instruction.loop);
const bounds = ({ prepare, latch, exit }) => ({ prepare, latch, exit });

test('numeric for lowers to an iteration region', () => {
  const loop = { iteration: 'numeric', base: 3, prepare: 4, latch: 6, exit: 7, variables: [5] };
  assertFields(parseDisassembly(it01NumericStep, iterationOptions).instructions, {
    4: { op: 'FORNPREP', kind: 'iteration_prepare', iteration: 'numeric', base: 3, reads: [5, 3, 4], writes: [],
      successors: [7, 5], loop },
    6: { op: 'FORNLOOP', kind: 'iteration_loop', variable_count: 1, reads: [], writes: [], successors: [5, 7], loop },
  });
  // The body copy `L0: MOVE R6 R5` reads the loop variable that the body edge defines.
  const written = parseDisassembly(it02NumericWritten, iterationOptions).instructions;
  assert.deepEqual(written[5].loop, { iteration: 'numeric', base: 3, prepare: 5, latch: 9, exit: 10, variables: [5] });
  assertFields(written, { 6: { op: 'MOVE', reads: [5], writes: [6] } });
});

test('generic for over pairs, ipairs and next lowers to an iteration region', () => {
  const loop = { iteration: 'generic', base: 4, prepare: 9, latch: 12, exit: 13, variables: [7, 8] };
  const region = {
    9: { op: 'FORGPREP', kind: 'iteration_prepare', iteration: 'generic', base: 4, reads: [4, 5, 6], successors: [12], loop },
    12: { op: 'FORGLOOP', kind: 'iteration_loop', variable_count: 2, reads: [], successors: [10, 13] },
  };
  assertFields(parseDisassembly(it03Pairs, iterationOptions).instructions, region);
  assertFields(parseDisassembly(it04Ipairs, iterationOptions).instructions, region);
  const next = parseDisassembly(it07GeneralizedNext, iterationOptions).instructions;
  assert.deepEqual(loopsOf(next), [
    { iteration: 'generic', base: 4, prepare: 8, latch: 11, exit: 12, variables: [7, 8] },
    { iteration: 'generic', base: 4, prepare: 15, latch: 17, exit: 18, variables: [7] },
  ]);
  assert.equal(next[17].variable_count, 1);
});

test('continue, break, nesting and return stay inside one region', () => {
  // it05: `continue` branches to the latch, `break` to the exit.
  const breakContinue = parseDisassembly(it05BreakContinue, iterationOptions).instructions;
  assert.deepEqual(loopsOf(breakContinue).map(bounds), [{ prepare: 4, latch: 9, exit: 10 }]);
  assertFields(breakContinue, {
    5: { op: 'JUMPIFEQ', line_number: 10, target: 9 },
    7: { op: 'JUMPIFLT', line_number: 12, target: 10 },
  });
  assert.deepEqual(loopsOf(parseDisassembly(it06GenericBreakContinue, iterationOptions).instructions).map(bounds),
    [{ prepare: 10, latch: 16, exit: 17 }]);
  // it08: the inner numeric loop lies inside the outer generic region and exits to the outer latch.
  const nested = loopsOf(parseDisassembly(it08Nested, iterationOptions).instructions);
  assert.deepEqual(nested, [
    { iteration: 'generic', base: 4, prepare: 9, latch: 18, exit: 19, variables: [7, 8] },
    { iteration: 'numeric', base: 9, prepare: 13, latch: 17, exit: 18, variables: [11] },
  ]);
  assert.equal(nested[1].exit, nested[0].latch);
  assert.deepEqual(loopsOf(parseDisassembly(it09ReturnInside, iterationOptions).instructions).map(bounds),
    [{ prepare: 4, latch: 10, exit: 11 }]);
});

test('loop registers are dead after the loop; the body edge defines only the loop variables', () => {
  const uninitialized = (message) => (error) => error.name === 'DisassemblyRefusal'
    && error.code === 'uninitialized_register' && error.message === message;
  const afterLoop = splice(it01NumericStep, 'L1: RETURN R2 1', 'L1: RETURN R5 1');
  assert.throws(() => parseDisassembly(afterLoop, iterationOptions), uninitialized('uninitialized R5 at disassembly line 11'));
  const previousIteration = splice(splice(it01NumericStep, 'L0: ADD R2 R2 R5', 'L0: ADD R2 R2 R6'),
    'FORNLOOP R3 L0', 'LOADN R6 1\nFORNLOOP R3 L0');
  assert.throws(() => parseDisassembly(previousIteration, iterationOptions),
    uninitialized('uninitialized R6 at disassembly line 9'));
  const secondRegister = splice(it07GeneralizedNext, 'L2: ADD R3 R3 R7', 'L2: ADD R3 R3 R8');
  assert.throws(() => parseDisassembly(secondRegister, iterationOptions),
    uninitialized('uninitialized R8 at disassembly line 21'));
});

test('iteration shapes the compiler never emits are typed refusals', () => {
  // [variant, code, line_number, opcode where pinned]
  const cases = [
    // numeric hidden write; numeric hidden read (limit)
    [splice(it01NumericStep, 'L0: ADD R2 R2 R5', 'L0: ADD R5 R2 R5'), 'iteration_state_written', 9],
    [splice(it01NumericStep, 'L0: ADD R2 R2 R5', 'L0: ADD R2 R2 R3'), 'iteration_state_read', 9],
    // numeric base mismatch; loop without prepare
    [splice(it01NumericStep, 'FORNLOOP R3 L0', 'FORNLOOP R4 L0'), 'iteration_pair_mismatch', 8, 'FORNPREP'],
    [splice(it01NumericStep, 'FORNPREP R3 L1', 'JUMPIF R0 L1'), 'iteration_pair_mismatch', 10, 'FORNLOOP'],
    // jump into the body; jump out of the body (not to the exit)
    [splice(it01NumericStep, 'FORNPREP R3 L1', 'JUMPIF R0 L0\nFORNPREP R3 L1'), 'iteration_region_entry', 8],
    [splice(splice(it01NumericStep, 'MOVE R3 R1', 'L2: MOVE R3 R1'), 'L0: ADD R2 R2 R5', 'L0: JUMPIF R0 L2\nADD R2 R2 R5'),
      'iteration_region_exit', 9],
    // generic hidden read (control); generic call frame over the state; generic zero variables
    [splice(it03Pairs, 'L0: MUL R9 R7 R8', 'L0: MUL R9 R6 R8'), 'iteration_state_read', 15],
    [splice(it03Pairs, 'L0: MUL R9 R7 R8', 'L0: CALL R5 0 1'), 'iteration_state_written', 15],
    [splice(it03Pairs, 'L1: FORGLOOP R4 L0 2', 'L1: FORGLOOP R4 L0 0'), 'operand_form', 17],
    // the -O1 fast paths: the ipairs marker, FORGPREP_NEXT and FORGPREP_INEXT
    [splice(it04Ipairs, 'L1: FORGLOOP R4 L0 2', 'L1: FORGLOOP R4 L0 2 [inext]'), 'iteration_fast_path_unsupported', 18],
    [splice(it03Pairs, 'FORGPREP R4 L1', 'FORGPREP_NEXT R4 L1'), 'unsupported_opcode', 14, 'FORGPREP_NEXT'],
    [splice(it04Ipairs, 'FORGPREP R4 L1', 'FORGPREP_INEXT R4 L1'), 'unsupported_opcode', 15, 'FORGPREP_INEXT'],
  ];
  for (const [variant, code, line_number, opcode] of cases) {
    assert.throws(() => parseDisassembly(variant, iterationOptions), (error) => error.name === 'DisassemblyRefusal'
      && error.code === code && error.line_number === line_number && (opcode === undefined || error.opcode === opcode));
  }
});

// Task T4.5 (T4-ADAPTER-ANDOR-IMPORT-DUPTABLE). Excerpts are verbatim -O0 -g0 listing lines of author-owned programs,
// CRLF removed: the Function 0 of research/fixtures/disassembly/p18_logic.O0.txt (lines 1-10), `AND R2 R2 R3` (the
// diagnosis program andor_probe at -O0, line 25 without its label: the target is the left operand), the -O1 constant
// forms of andor_probe (O1 listing lines 2-3 and 10-11, each plus a return) and the Function 0 of
// research/fixtures/disassembly/table_record_fields.O0.txt (lines 1-39). The supported level is -O0 -g0 (decision D3).
const p18Logic = `Function 0 (??):
K0: 0
AND R2 R0 R1
OR R3 R0 R1
LOADK R5 K0 [0]
JUMPIFNOTLT R5 R0 L0
MOVE R4 R1
JUMPIF R4 L1
L0: MINUS R4 R1
L1: RETURN R2 3
`;
const tableRecordFields = `Function 0 (??):
K0: 'count'
K1: 'total'
K2: {...}
K3: 0
K4: 1
K5: 'done'
K6: 'label'
K7: 'missing'
REMARK allocation: table template 2
DUPTABLE R2 2
LOADK R3 K0 ['count']
LOADK R4 K3 [0]
SETTABLE R4 R2 R3
LOADK R3 K1 ['total']
SETTABLE R0 R2 R3
L0: GETTABLEKS R3 R2 K0 ['count']
JUMPIFNOTLT R3 R1 L1
GETTABLEKS R4 R2 K1 ['total']
GETTABLEKS R5 R2 K0 ['count']
ADD R3 R4 R5
SETTABLEKS R3 R2 K1 ['total']
GETTABLEKS R4 R2 K0 ['count']
LOADK R5 K4 [1]
ADD R3 R4 R5
SETTABLEKS R3 R2 K0 ['count']
JUMPBACK L0
L1: LOADK R3 K5 ['done']
SETTABLEKS R3 R2 K6 ['label']
GETTABLEKS R3 R2 K0 ['count']
GETTABLEKS R4 R2 K1 ['total']
GETTABLEKS R6 R2 K6 ['label']
LENGTH R5 R6
GETTABLEKS R7 R2 K7 ['missing']
LOADNIL R8
JUMPIFEQ R7 R8 L2
LOADB R6 0 +1
L2: LOADB R6 1
L3: RETURN R3 4
`;

test('AND and OR lower to logical conditional moves', () => {
  assertFields(parseDisassembly(p18Logic, { parameter_count: 2 }).instructions, {
    0: { op: 'AND', kind: 'logical', operator: 'and', reads: [0, 1], writes: [2] },
    1: { op: 'OR', kind: 'logical', operator: 'or', reads: [0, 1], writes: [3] },
  });
  assertFields(parseDisassembly(excerpt('AND R2 R2 R3', 'RETURN R2 1'), { parameter_count: 4 }).instructions, {
    0: { reads: [2, 3], writes: [2] },
  });
});

test('constant-operand AND/OR stay refused at the pinned level', () => {
  // ANDK and ORK need a constant right operand, which only -O1 constant folding supplies; like GETIMPORT
  // (`imports stay refused at the pinned level`), they are not in the opcode table.
  assert.throws(() => parseDisassembly(excerpt('K0: 7', 'ANDK R4 R0 K0 [7]', 'RETURN R4 1'), { parameter_count: 2 }),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'unsupported_opcode' && error.opcode === 'ANDK'
      && /unsupported opcode ANDK at disassembly line 3/.test(error.message));
  assert.throws(() => parseDisassembly(excerpt('K1: false', 'ORK R5 R1 K1 [false]', 'RETURN R5 1'), { parameter_count: 2 }),
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'unsupported_opcode' && error.opcode === 'ORK'
      && /unsupported opcode ORK at disassembly line 3/.test(error.message));
});

test('a -O0 record template stays refused with its remark and its stores', () => {
  // Decision D1: DUPTABLE stays refused even where the -O0 listing shows its remark and its key stores; the reason is
  // recorded at the adapter's refusal.
  assert.throws(() => parseDisassembly(tableRecordFields),
    (error) => refusedAs('table_template_opaque')(error) && error.opcode === 'DUPTABLE' && error.line_number === 11);
});
