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

// Basic listings. Each excerpt is `Function 0 (??):` plus verbatim -O0 listing lines of the
// author-owned test programs (five small programs and a LOADB skip program), joined with `\n`.
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
    (error) => error.name === 'DisassemblyRefusal' && error.code === 'open_protocol_unsupported' && error.line_number === 9
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

// Globals. Excerpts are verbatim listing lines of author-owned programs:
// a globals program at -O0 (Function 0) and an import program at -O1 (lines 1-4 and 8, plus a return) for the GETIMPORT pin.
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
