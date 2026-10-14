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
  assert.throws(() => parseDisassembly(listing.replace('ADD R2 R2 R3', 'FORNPREP R2 L1')), /unsupported opcode FORNPREP/);
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
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'unsupported_opcode' && error.opcode === 'FORNPREP'
      && error.line_number === 7 && /unsupported opcode FORNPREP at disassembly line 7/.test(error.message));
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
