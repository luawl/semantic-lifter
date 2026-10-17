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
  assert.throws(() => parseDisassembly(listing.replace('ADD R2 R2 R3', 'DUPCLOSURE R2 K0')), /unsupported opcode DUPCLOSURE/);
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

test('without a declared level a record template stays refused', () => {
  // PLAN-T4 decision D1, kept for a listing whose level is not declared (PLAN-T6 Task T6.8): DUPTABLE stays refused even
  // where the -O0 listing shows its remark and its key stores; the reason is recorded at the adapter's refusal.
  assert.throws(() => parseDisassembly(tableRecordFields),
    (error) => refusedAs('table_template_opaque')(error) && error.opcode === 'DUPTABLE' && error.line_number === 11);
});

// Task T4.6 (T4-ADAPTER-CLOSURES). Each listing is the whole -O0 -g0 listing of an author-owned program, embedded verbatim
// with CRLF removed: c1-c15 from the diagnosis directory tmp/build-phase2/diag/T4-ADAPTER-CLOSURES/listings/, the skeptic's
// dead-function probes k1, k4 and k5 from its skeptic/probes/, and research/fixtures/disassembly/closure_loop_reference.O0.txt.
// The caller declares every nested function to lift (decision D1: the function tree is never recovered from the post-order
// numbering); the supported level is -O0 -g0 (decision D3), where no DUPCLOSURE is emitted.
const c1CounterRef = `Function 0 (??):
GETUPVAL R2 0
ADD R1 R2 R0
SETUPVAL R1 0
GETUPVAL R1 0
RETURN R1 1

Function 1 (??):
K0: 1
MOVE R2 R0
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R3 P0
CAPTURE REF R2
MOVE R4 R3
MOVE R5 R1
CALL R4 1 0
MOVE R4 R3
LOADK R5 K0 [1]
CALL R4 1 0
CLOSEUPVALS R2
RETURN R2 1

Function 2 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const c2ParamValue = `Function 0 (??):
GETUPVAL R3 0
MUL R2 R0 R3
GETUPVAL R3 1
ADD R1 R2 R3
RETURN R1 1

Function 1 (??):
K0: 2
K1: 3
REMARK allocation: closure with 2 upvalues
NEWCLOSURE R2 P0
CAPTURE VAL R0
CAPTURE VAL R1
MOVE R4 R2
LOADK R5 K0 [2]
CALL R4 1 1
MOVE R5 R2
LOADK R6 K1 [3]
CALL R5 1 1
ADD R3 R4 R5
RETURN R3 1

Function 2 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const c3ReturnedClosure = `Function 0 (??):
GETUPVAL R2 0
ADD R1 R2 R0
RETURN R1 1

Function 1 (??):
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R1 P0
CAPTURE VAL R0
RETURN R1 1

Function 2 (??):
GETUPVAL R2 0
MOVE R3 R0
CALL R2 1 1
MOVE R3 R2
MOVE R4 R1
CALL R3 1 -1
RETURN R3 -1

Function 3 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R1 P1
CAPTURE VAL R0
RETURN R1 1

`;
const c4LoopClose = `Function 0 (??):
GETUPVAL R1 0
GETUPVAL R2 1
ADD R0 R1 R2
SETUPVAL R0 0
RETURN R0 0

Function 1 (??):
K0: 0
K1: 1
LOADK R2 K0 [0]
LOADK R3 K0 [0]
L0: JUMPIFNOTLT R3 R1 L1
LOADK R4 K1 [1]
ADD R3 R3 R4
MOVE R4 R3
REMARK allocation: closure with 2 upvalues
NEWCLOSURE R5 P0
CAPTURE REF R4
CAPTURE VAL R0
MOVE R6 R5
CALL R6 0 0
ADD R2 R2 R4
CLOSEUPVALS R4
JUMPBACK L0
L1: RETURN R2 1

Function 2 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const c5UpvalueChain = `Function 0 (??):
GETUPVAL R3 0
GETUPVAL R4 1
ADD R2 R3 R4
ADD R1 R2 R0
RETURN R1 1

Function 1 (??):
REMARK allocation: closure with 2 upvalues
NEWCLOSURE R1 P0
CAPTURE UPVAL U0
CAPTURE VAL R0
MOVE R2 R1
GETUPVAL R3 1
CALL R2 1 -1
RETURN R2 -1

Function 2 (??):
K0: 1
REMARK allocation: closure with 2 upvalues
NEWCLOSURE R2 P0
CAPTURE VAL R0
CAPTURE VAL R1
MOVE R3 R2
LOADK R4 K0 [1]
CALL R3 1 -1
RETURN R3 -1

Function 3 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const c6RecursiveLocal = `Function 0 (??):
K0: 1
LOADK R1 K0 [1]
JUMPIFNOTLT R0 R1 L0
GETUPVAL R1 0
RETURN R1 1
L0: GETUPVAL R2 1
LOADK R4 K0 [1]
SUB R3 R0 R4
CALL R2 1 1
LOADK R3 K0 [1]
ADD R1 R2 R3
RETURN R1 1

Function 1 (??):
REMARK allocation: closure with 2 upvalues
NEWCLOSURE R2 P0
CAPTURE VAL R0
CAPTURE VAL R2
MOVE R3 R2
MOVE R4 R1
CALL R3 1 -1
RETURN R3 -1

Function 2 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const c8Siblings = `Function 0 (??):
GETUPVAL R2 0
ADD R1 R0 R2
RETURN R1 1

Function 1 (??):
GETUPVAL R2 0
MUL R1 R0 R2
RETURN R1 1

Function 2 (??):
K0: 1
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R1 P0
CAPTURE UPVAL U0
MOVE R3 R1
MOVE R4 R0
CALL R3 1 1
LOADK R4 K0 [1]
SUB R2 R3 R4
RETURN R2 1

Function 3 (??):
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R2 P0
CAPTURE VAL R0
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R3 P1
CAPTURE VAL R1
MOVE R5 R3
MOVE R6 R2
MOVE R7 R1
CALL R6 1 -1
CALL R5 -1 1
MOVE R6 R2
MOVE R7 R0
CALL R6 1 1
ADD R4 R5 R6
RETURN R4 1

Function 4 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const c10DoBlockReuse = `Function 0 (??):
K0: 1
GETUPVAL R1 0
LOADK R2 K0 [1]
ADD R0 R1 R2
SETUPVAL R0 0
GETUPVAL R0 0
RETURN R0 1

Function 1 (??):
LOADNIL R2
MOVE R3 R0
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R2 P0
CAPTURE REF R3
CLOSEUPVALS R3
MOVE R3 R1
MOVE R4 R2
CALL R4 0 0
MOVE R5 R2
CALL R5 0 1
ADD R4 R5 R3
RETURN R4 1

Function 2 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const c12TreeOrder = `Function 0 (??):
K0: 1
LOADK R2 K0 [1]
ADD R1 R0 R2
RETURN R1 1

Function 1 (??):
K0: 2
LOADK R2 K0 [2]
MUL R1 R0 R2
RETURN R1 1

Function 2 (??):
K0: 3
LOADK R2 K0 [3]
SUB R1 R0 R2
RETURN R1 1

Function 3 (??):
GETUPVAL R2 0
ADD R1 R0 R2
RETURN R1 1

Function 4 (??):
GETUPVAL R2 0
SUB R1 R0 R2
RETURN R1 1

Function 5 (??):
MOVE R2 R0
MOVE R3 R1
CALL R2 1 -1
RETURN R2 -1

Function 6 (??):
GETUPVAL R2 0
MUL R1 R0 R2
RETURN R1 1

Function 7 (??):
K0: 'key'
K1: 1
K2: 2
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R2 P0
REMARK allocation: table hash 1 array 1
NEWTABLE R3 1 1
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R4 P1
SETLIST R3 R4 1 [1]
LOADK R5 K0 ['key']
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R6 P2
SETTABLE R6 R3 R5
JUMPIFNOTLT R1 R0 L0
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R4 P3
CAPTURE VAL R0
JUMP L1
REMARK allocation: closure with 1 upvalues
L0: NEWCLOSURE R4 P4
CAPTURE VAL R1
L1: MOVE R8 R2
MOVE R9 R0
CALL R8 1 1
LOADK R10 K1 [1]
GETTABLE R9 R3 R10
MOVE R10 R1
CALL R9 1 1
ADD R7 R8 R9
GETTABLEKS R8 R3 K0 ['key']
MOVE R9 R0
CALL R8 1 1
ADD R6 R7 R8
MOVE R7 R4
MOVE R8 R1
CALL R7 1 1
ADD R5 R6 R7
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R6 P5
MOVE R7 R6
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R8 P6
CAPTURE VAL R1
LOADK R9 K2 [2]
CALL R7 2 1
ADD R5 R5 R7
RETURN R5 1

Function 8 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const c13RecursiveInLoop = `Function 0 (??):
K0: 1
LOADK R1 K0 [1]
JUMPIFNOTLT R0 R1 L0
GETUPVAL R1 0
RETURN R1 1
L0: GETUPVAL R2 1
LOADK R4 K0 [1]
SUB R3 R0 R4
CALL R2 1 1
LOADK R3 K0 [1]
ADD R1 R2 R3
RETURN R1 1

Function 1 (??):
K0: 0
K1: 1
REMARK allocation: table hash 0
NEWTABLE R2 0 0
LOADK R3 K0 [0]
L0: JUMPIFNOTLT R3 R1 L1
LOADK R4 K1 [1]
ADD R3 R3 R4
MOVE R4 R3
REMARK allocation: closure with 2 upvalues
NEWCLOSURE R5 P0
CAPTURE VAL R4
CAPTURE VAL R5
SETTABLE R5 R2 R3
JUMPBACK L0
L1: LOADK R4 K0 [0]
LOADK R5 K0 [0]
L2: JUMPIFNOTLT R5 R1 L3
LOADK R6 K1 [1]
ADD R5 R5 R6
GETTABLE R6 R2 R5
MOVE R7 R0
CALL R6 1 1
ADD R4 R4 R6
JUMPBACK L2
L3: RETURN R4 1

Function 2 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const c15OpenReturnClose = `Function 0 (??):
GETUPVAL R2 0
ADD R1 R2 R0
SETUPVAL R1 0
GETUPVAL R1 0
RETURN R1 1

Function 1 (??):
K0: 1
MOVE R2 R0
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R3 P0
CAPTURE REF R2
MOVE R4 R3
LOADK R5 K0 [1]
CALL R4 1 0
MOVE R4 R3
MOVE R5 R1
CALL R4 1 -1
CLOSEUPVALS R2
RETURN R4 -1

Function 2 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const k1DeadAfterDoReturn = `Function 0 (??):
GETUPVAL R0 0
RETURN R0 1

Function 1 (??):
K0: 100
GETUPVAL R1 0
LOADK R2 K0 [100]
MUL R0 R1 R2
RETURN R0 1

Function 2 (??):
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R2 P0
CAPTURE VAL R0
MOVE R4 R2
CALL R4 0 1
ADD R3 R4 R1
RETURN R3 1

Function 3 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const k4DeadBetweenSiblings = `Function 0 (??):
GETUPVAL R0 0
RETURN R0 1

Function 1 (??):
K0: 100
GETUPVAL R1 0
LOADK R2 K0 [100]
MUL R0 R1 R2
RETURN R0 1

Function 2 (??):
GETUPVAL R0 0
RETURN R0 1

Function 3 (??):
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R2 P0
CAPTURE VAL R0
JUMPIFNOTLT R1 R0 L0
MOVE R4 R2
CALL R4 0 1
SUB R3 R4 R1
RETURN R3 1
REMARK allocation: closure with 1 upvalues
L0: NEWCLOSURE R3 P1
CAPTURE VAL R1
MOVE R5 R2
CALL R5 0 1
MOVE R6 R3
CALL R6 0 1
ADD R4 R5 R6
RETURN R4 1

Function 4 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const k5DeadAfterIfElseReturn = `Function 0 (??):
GETUPVAL R0 0
RETURN R0 1

Function 1 (??):
K0: 100
GETUPVAL R1 0
LOADK R2 K0 [100]
MUL R0 R1 R2
RETURN R0 1

Function 2 (??):
REMARK allocation: closure with 1 upvalues
NEWCLOSURE R2 P0
CAPTURE VAL R0
JUMPIFNOTLT R1 R0 L0
MOVE R4 R2
CALL R4 0 1
SUB R3 R4 R1
RETURN R3 1
L0: MOVE R4 R2
CALL R4 0 1
ADD R3 R4 R1
RETURN R3 1

Function 3 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;
const closureLoopReference = `Function 0 (??):
GETUPVAL R1 0
GETUPVAL R2 1
ADD R0 R1 R2
SETUPVAL R0 0
GETUPVAL R0 0
RETURN R0 1

Function 1 (??):
K0: 1
K1: 0
REMARK allocation: table hash 0
NEWTABLE R2 0 0
LOADK R5 K0 [1]
MOVE R3 R1
LOADN R4 1
FORNPREP R3 L1
L0: MOVE R6 R5
REMARK allocation: closure with 2 upvalues
NEWCLOSURE R7 P0
CAPTURE REF R6
CAPTURE VAL R0
SETTABLE R7 R2 R5
CLOSEUPVALS R6
FORNLOOP R3 L0
L1: LOADK R3 K1 [0]
LOADK R6 K0 [1]
LENGTH R4 R2
LOADN R5 1
FORNPREP R4 L3
L2: GETTABLE R8 R2 R6
CALL R8 0 1
ADD R7 R3 R8
GETTABLE R8 R2 R6
CALL R8 0 1
ADD R3 R7 R8
FORNLOOP R4 L2
L3: RETURN R3 1

Function 2 (??):
REMARK allocation: closure with 0 upvalues
NEWCLOSURE R0 P0
RETURN R0 1

`;

const one = (pc) => ({ 0: { parent: 1, prototype: 0, parameter_count: pc } });
const closureOf = (fn) => fn.instructions.find((instruction) => instruction.kind === 'closure');

test('closures fuse NEWCLOSURE with its CAPTURE lines and lift nested functions', () => {
  const handoff = parseDisassembly(c1CounterRef, { function_index: 1, parameter_count: 2, nested: one(1) });
  assert.equal(handoff.schema_version, 'compiler_disassembly_handoff_v3');
  assertFields(handoff.instructions, {
    1: { op: 'NEWCLOSURE', kind: 'closure', function: 0,
      captures: [{ mode: 'reference', register: 2, class: 'place', line_number: 13 }],
      reads: [], references: [2], writes: [3], line_numbers: [12, 13] },
    8: { kind: 'close_upvalues', from: 2 },
  });
  assertFields(handoff.functions, {
    0: { function_index: 0, parent_index: 1, parameter_count: 1, is_variadic: false,
      upvalues: [{ class: 'place', line_number: 13 }] },
  });
  assertFields(handoff.functions[0].instructions, {
    0: { kind: 'upvalue_get', upvalue: 0, writes: [2] },
    2: { kind: 'upvalue_set', upvalue: 0, reads: [1] },
  });
});

test('capture classes come from the creating closure', () => {
  const values = closureOf(parseDisassembly(c2ParamValue, { function_index: 1, parameter_count: 2, nested: one(1) }));
  assert.deepEqual(values.captures, [{ mode: 'value', register: 0, class: 'value', line_number: 13 },
    { mode: 'value', register: 1, class: 'value', line_number: 14 }]);
  assert.deepEqual(values.reads, [0, 1]);
  const recursive = closureOf(parseDisassembly(c6RecursiveLocal, { function_index: 1, parameter_count: 2, nested: one(1) }));
  assert.deepEqual(recursive.captures, [{ mode: 'value', register: 0, class: 'value', line_number: 18 },
    { mode: 'self', register: 2, class: 'place', line_number: 19 }]);
  assert.deepEqual(recursive.reads, [0]);
  const chain = parseDisassembly(c5UpvalueChain, { function_index: 2, parameter_count: 2, nested: {
    1: { parent: 2, prototype: 0, parameter_count: 1 }, 0: { parent: 1, prototype: 0, parameter_count: 1 } } });
  assert.equal(chain.functions[0].function_index, 1);
  assert.deepEqual(chain.functions[0].upvalues.map((upvalue) => upvalue.class), ['value', 'value']);
  assert.deepEqual(closureOf(chain.functions[0]).captures[0], { mode: 'upvalue', upvalue: 0, class: 'value', line_number: 11 });
});

test('the declared function tree is checked against the NEWCLOSURE lines', () => {
  const tree = (handoff) => handoff.functions.map((f) => [f.function_index, f.parent_index]);
  const siblings = { 0: { parent: 3, prototype: 0, parameter_count: 1 }, 2: { parent: 3, prototype: 1, parameter_count: 1 },
    1: { parent: 2, prototype: 0, parameter_count: 1 } };
  assert.deepEqual(tree(parseDisassembly(c8Siblings, { function_index: 3, parameter_count: 2, nested: siblings })),
    [[0, 3], [2, 3], [1, 2]]);
  const order = Object.fromEntries([1, 1, 1, 1, 1, 2, 1].map((pc, k) => [k, { parent: 7, prototype: k, parameter_count: pc }]));
  assert.deepEqual(tree(parseDisassembly(c12TreeOrder, { function_index: 7, parameter_count: 2, nested: order })),
    [[0, 7], [1, 7], [2, 7], [3, 7], [4, 7], [5, 7], [6, 7]]);
  const withoutGrandchild = Object.fromEntries(Object.entries(siblings).filter(([index]) => index !== '1'));
  assert.throws(() => parseDisassembly(c8Siblings, { function_index: 3, parameter_count: 2, nested: withoutGrandchild }),
    refusedAs('nested_function_undeclared'));
  assert.throws(() => parseDisassembly(c8Siblings, { function_index: 3, parameter_count: 2,
    nested: { ...siblings, 1: { parent: 2, prototype: 1, parameter_count: 1 } } }), refusedAs('nested_map_mismatch'));
});

test('closure refusals are typed', () => {
  // [listing, options, code, line_number where pinned]: the splices and options of
  // tmp/build-phase2/diag/T4-ADAPTER-CLOSURES/u4_refusals.mjs, with the declared maps of decision D1.
  const cases = [
    [c3ReturnedClosure, { function_index: 2, parameter_count: 2 }, 'selected_function_captures', 13],
    [c10DoBlockReuse, { function_index: 1, parameter_count: 2, nested: one(0) }, 'captured_register_reused_after_close', 17],
    [c4LoopClose, { function_index: 1, parameter_count: 2, nested: one(0) }, 'captured_register_reused_after_close', 14],
    [c13RecursiveInLoop, { function_index: 1, parameter_count: 2, nested: one(1) }, 'self_capture_in_loop', 26],
    [c1CounterRef, { function_index: 1, parameter_count: 2 }, 'nested_function_undeclared'],
    [splice(c1CounterRef, 'CAPTURE REF R2\n', ''), { function_index: 1, parameter_count: 2, nested: one(1) },
      'capture_count_mismatch'],
    [splice(c1CounterRef, 'CAPTURE REF R2', 'L9: CAPTURE REF R2'), { function_index: 1, parameter_count: 2, nested: one(1) },
      'label_inside_closure'],
    ['Function 0 (??):\nCAPTURE VAL R0\nRETURN R0 1\n', {}, 'capture_without_closure'],
    [splice(c2ParamValue, 'ADD R1 R2 R3\n', 'ADD R1 R2 R3\nSETUPVAL R1 0\n'),
      { function_index: 1, parameter_count: 2, nested: one(1) }, 'setupval_on_value_capture'],
    ['Function 0 (??):\nK0: 0\nDUPCLOSURE R0 K0\nRETURN R0 1\n', {}, 'unsupported_opcode'],
  ];
  for (const [text, options, code, line_number] of cases) {
    assert.throws(() => parseDisassembly(text, options), (error) => error.name === 'DisassemblyRefusal' && error.code === code
      && (line_number === undefined || error.line_number === line_number));
  }
});

test('an open pack passes through CLOSEUPVALS', () => {
  const options = { function_index: 1, parameter_count: 2, nested: one(1) };
  const { instructions } = parseDisassembly(c15OpenReturnClose, options);
  const call = instructions.findIndex((instruction) => instruction.line_number === 19);
  assert.ok(call >= 0, 'the CALL at line 19 is an instruction');
  assertFields(instructions, {
    [call]: { op: 'CALL', produces_pack_at: 4 },
    [call + 1]: { kind: 'close_upvalues', from: 2 },
    [call + 2]: { op: 'RETURN', line_number: 21, consumes_pack_from: 4, reads: [] },
  });
  assert.throws(() => parseDisassembly(splice(c15OpenReturnClose, 'CLOSEUPVALS R2', 'L9: CLOSEUPVALS R2'), options),
    refusedAs('open_pack_crosses_label'));
});

test('closure trees with an uninstantiated function are refused', () => {
  // Skeptic objection A: a function after an always-terminating statement keeps its post-order slot but no NEWCLOSURE
  // line. The census runs first: 4 functions and 2 NEWCLOSURE lines in k1 and k5, 5 and 3 in k4.
  const cases = [
    [k1DeadAfterDoReturn, { function_index: 2, parameter_count: 2,
      nested: { 0: { parent: 2, prototype: 0, parameter_count: 0 } } }],
    [k1DeadAfterDoReturn, { function_index: 2, parameter_count: 2,
      nested: { 0: { parent: 2, prototype: 0, parameter_count: 0 }, 1: { parent: 2, prototype: 1, parameter_count: 0 } } }],
    [k4DeadBetweenSiblings, { function_index: 3, parameter_count: 2,
      nested: { 0: { parent: 3, prototype: 0, parameter_count: 0 }, 2: { parent: 3, prototype: 1, parameter_count: 0 } } }],
    [k5DeadAfterIfElseReturn, { function_index: 2, parameter_count: 2,
      nested: { 0: { parent: 2, prototype: 0, parameter_count: 0 } } }],
  ];
  for (const [text, options] of cases) {
    assert.throws(() => parseDisassembly(text, options), refusedAs('uninstantiated_function'));
  }
});

test('a by-reference capture inside a numeric for loop is refused', () => {
  assert.throws(() => parseDisassembly(closureLoopReference, { function_index: 1, parameter_count: 2, nested: one(0) }),
    refusedAs('captured_register_reused_after_close'));
});

// Task T6.8 (T6-DUPTABLE-LOWERING, Steps A and B): at a caller-declared -O0 (`optimization_level: 0`) a DUPTABLE record
// template and its N record stores lower to a literal constructor window whose members carry their LOADK'd keys, so the
// bridge builds one make_table_literal with constant identifier keys, which the backend prints as a record that Luau
// recompiles to a DUPTABLE of the same template. Without the declaration the template stays refused (the pin above).
// duptableControlflow is the verbatim Function 0 of the -O0 -g0 listing of the author-owned program
// tmp/build-phase2/diag/T4-ADAPTER-ANDOR-IMPORT-DUPTABLE/programs/duptable_controlflow.luau, CRLF removed.
const duptableControlflow = `Function 0 (??):
K0: 'positive'
K1: 'scaled'
K2: {...}
K3: 0
REMARK allocation: table template 2
DUPTABLE R2 2
LOADK R3 K0 ['positive']
LOADK R5 K3 [0]
JUMPIFLT R5 R0 L0
LOADB R4 0 +1
L0: LOADB R4 1
L1: SETTABLE R4 R2 R3
LOADK R3 K1 ['scaled']
SETTABLE R1 R2 R3
GETTABLEKS R3 R2 K0 ['positive']
GETTABLEKS R4 R2 K1 ['scaled']
RETURN R3 2
`;
const declaredO0 = { optimization_level: 0 };
const refusedWithMessage = (code, message) => (error) => refusedAs(code)(error) && message.test(error.message);
const replaceExactlyOnce = (text, from, to) => {
  assert.equal(text.split(from).length - 1, 1, `not exactly once: ${from}`);
  return text.replace(from, () => to);
};
const pickFields = (instruction, fields) => Object.fromEntries(fields.map((field) => [field, instruction[field]]));

test('a record template at a declared -O0 lowers to a literal window with record keys', () => {
  const handoff = parseDisassembly(tableRecordFields, declaredO0);
  assert.deepEqual(Object.keys(handoff), ['schema_version', 'listing_sha256', 'function_index', 'parameter_count', 'is_variadic',
    'registers', 'instructions', 'signature_origin', 'scope']);
  const { instructions } = handoff;
  assert.deepEqual(pickFields(instructions[0], ['op', 'kind', 'template_size', 'writes', 'constructor']),
    { op: 'DUPTABLE', kind: 'new_table', template_size: 2, writes: [2], constructor: { create: 0, mode: 'literal' } });
  assert.deepEqual(pickFields(instructions[3], ['op', 'kind', 'table', 'value', 'key_constant', 'reads', 'constructor']),
    { op: 'SETTABLE', kind: 'table_set', table: 2, value: 4, key_constant: { string: 'count' }, reads: [4], constructor: { create: 0, mode: 'literal' } });
  assert.deepEqual(pickFields(instructions[5], ['op', 'value', 'key_constant', 'reads', 'complete']),
    { op: 'SETTABLE', value: 0, key_constant: { string: 'total' }, reads: [0], complete: true });
  assert.equal(Object.hasOwn(instructions[3], 'key'), false);
  assert.equal(Object.hasOwn(instructions[5], 'key'), false);
  assert.deepEqual(instructions.flatMap((instruction, index) => (Object.hasOwn(instruction, 'constructor') ? [index] : [])), [0, 3, 5]);
});

test('record templates outside the -O0 record shape are typed refusals', () => {
  assert.throws(() => parseDisassembly(tableRecordFields, { optimization_level: 1 }),
    refusedWithMessage('invalid_options', /^optimization_level must be 0 or omitted$/));
  assert.throws(() => parseDisassembly(replaceExactlyOnce(tableRecordFields, 'REMARK allocation: table template 2\n', ''), declaredO0),
    refusedWithMessage('table_template_opaque', /no table template remark/));
  assert.throws(() => parseDisassembly(replaceExactlyOnce(tableRecordFields, "K0: 'count'", "K0: 'end'"), declaredO0),
    refusedWithMessage('non_identifier_name', /DUPTABLE member key is not a record name at disassembly line 14/));
  assert.throws(() => parseDisassembly(replaceExactlyOnce(tableRecordFields, "SETTABLE R4 R2 R3\nLOADK R3 K1",
    "SETTABLE R4 R2 R3\nGETTABLEKS R5 R2 K0 ['count']\nLOADK R3 K1"), declaredO0),
  refusedWithMessage('constructor_window_unsupported', /template of 2 fields has 1 stores/));
  assert.throws(() => parseDisassembly(replaceExactlyOnce(tableRecordFields, "LOADK R3 K1 ['total']\nSETTABLE R0 R2 R3",
    "SETTABLEKS R0 R2 K1 ['total']"), declaredO0),
  refusedWithMessage('constructor_window_unsupported', /DUPTABLE member is not a record field store at disassembly line 15/));
  assert.throws(() => parseDisassembly(replaceExactlyOnce(tableRecordFields, 'table template 2', 'table template 3'), declaredO0),
    refusedWithMessage('constructor_window_unsupported', /template of 3 fields has 2 stores/));
});

test('a record template window may hold control flow that stays inside it', () => {
  const { instructions } = parseDisassembly(duptableControlflow, declaredO0);
  const members = instructions.flatMap((instruction, index) => (Object.hasOwn(instruction, 'constructor') ? [index] : []));
  assert.deepEqual(members.map((index) => instructions[index].op), ['DUPTABLE', 'SETTABLE', 'SETTABLE']);
  assert.deepEqual(members.slice(1).map((index) => instructions[index].key_constant), [{ string: 'positive' }, { string: 'scaled' }]);
  assert.equal(instructions[members[2]].complete, true);
});

test('control flow that enters, leaves or bypasses a record template window is refused', () => {
  assert.throws(() => parseDisassembly(replaceExactlyOnce(duptableControlflow, "GETTABLEKS R4 R2 K1 ['scaled']\n",
    "GETTABLEKS R4 R2 K1 ['scaled']\nJUMPIF R3 L0\n"), declaredO0),
  refusedWithMessage('constructor_window_unsupported', /transfer enters a DUPTABLE window/));
  assert.throws(() => parseDisassembly(replaceExactlyOnce(replaceExactlyOnce(duptableControlflow, 'JUMPIFLT R5 R0 L0', 'JUMPIFLT R5 R0 L2'),
    "LOADK R3 K1 ['scaled']", "L2: LOADK R3 K1 ['scaled']"), declaredO0),
  refusedWithMessage('constructor_window_unsupported', /transfer leaves the DUPTABLE window or passes a member/));
  assert.throws(() => parseDisassembly(replaceExactlyOnce(duptableControlflow, "L1: SETTABLE R4 R2 R3\nLOADK R3 K1 ['scaled']\nSETTABLE R1 R2 R3",
    "L1: SETTABLE R4 R2 R3\nJUMPIF R1 L2\nLOADK R3 K1 ['scaled']\nL2: SETTABLE R1 R2 R3"), declaredO0),
  refusedWithMessage('constructor_window_unsupported', /transfer passes the key load of a DUPTABLE member/));
});
