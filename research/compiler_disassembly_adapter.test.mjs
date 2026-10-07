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
  assert.throws(() => parseDisassembly(listing.replace('ADD R2 R2 R3', 'GETGLOBAL R2 K1')), /unsupported opcode GETGLOBAL/);
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
