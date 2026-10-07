import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';

const BINARY = {
  ADD: 'add', SUB: 'subtract', MUL: 'multiply', DIV: 'divide',
  IDIV: 'floor_divide', MOD: 'modulo', POW: 'power',
};
const COMPARE = {
  EQ: 'equal', LT: 'less', LE: 'less_equal',
};

function register(text) {
  assert.match(text ?? '', /^R\d+$/, 'invalid register operand');
  const value = Number(text.slice(1));
  assert.ok(value < 255, 'register outside Luau register range');
  return value;
}

function literal(text) {
  if (text === 'nil') return { nil_value: {} };
  if (text === 'true' || text === 'false') return { boolean: text === 'true' };
  assert.match(text, /^-?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$/, 'unsupported constant');
  const value = Number(text);
  assert.ok(Number.isFinite(value) && !Object.is(value, -0), 'unsupported numeric constant');
  return { number: value };
}

// The compiler owns bytecode decoding. This adapter accepts its pinned text
// format, not arbitrary binary bytecode or original source ASTs.
export function parseDisassembly(text, { function_index = 0, parameter_count = 2 } = {}) {
  assert.ok(Number.isInteger(function_index) && function_index >= 0);
  assert.ok(Number.isInteger(parameter_count) && parameter_count >= 0 && parameter_count < 255);
  const functions = new Map();
  let current = null;
  for (const [index, raw] of text.split(/\r?\n/).entries()) {
    const line = raw.trim();
    const header = /^Function (\d+) \(.*\):$/.exec(line);
    if (header) {
      const id = Number(header[1]);
      assert.ok(!functions.has(id), 'duplicate function header');
      current = [];
      functions.set(id, current);
    } else if (line) {
      assert.ok(current, 'text before function header');
      current.push({ line, line_number: index + 1 });
    }
  }
  assert.ok(functions.has(function_index), 'selected function is absent');
  const constants = new Map();
  const labels = new Map();
  const instructions = [];
  for (const record of functions.get(function_index)) {
    let { line } = record;
    if (line.startsWith('REMARK ')) continue;
    const constant = /^K(\d+): (.+)$/.exec(line);
    if (constant) {
      const key = Number(constant[1]);
      assert.ok(!constants.has(key), 'duplicate constant');
      constants.set(key, literal(constant[2]));
      continue;
    }
    const label = /^(L\d+):\s*(.*)$/.exec(line);
    if (label) {
      assert.ok(!labels.has(label[1]), 'duplicate label');
      labels.set(label[1], instructions.length);
      line = label[2];
      if (!line) continue;
    }
    const match = /^([A-Z][A-Z0-9]*)(?:\s+(.*))?$/.exec(line);
    assert.ok(match, `unrecognized disassembly at line ${record.line_number}`);
    const op = match[1];
    const args = (match[2] ?? '').replace(/\s+\[[^\]]*\]$/, '').split(/\s+/).filter(Boolean);
    const instruction = { op, args, line_number: record.line_number, reads: [], writes: [] };
    const count = (expected) => assert.equal(args.length, expected, `${op}: operand count`);
    if (op === 'LOADK') {
      count(2);
      assert.match(args[1], /^K\d+$/, 'invalid constant operand');
      const key = Number(args[1].slice(1));
      assert.ok(constants.has(key), 'constant is absent');
      instruction.kind = 'constant';
      instruction.value = constants.get(key);
      instruction.writes = [register(args[0])];
    } else if (op === 'LOADN') {
      count(2);
      instruction.kind = 'constant';
      instruction.value = literal(args[1]);
      instruction.writes = [register(args[0])];
    } else if (op === 'LOADNIL') {
      count(1);
      instruction.kind = 'constant';
      instruction.value = { nil_value: {} };
      instruction.writes = [register(args[0])];
    } else if (op === 'MOVE') {
      count(2);
      instruction.kind = 'move';
      instruction.writes = [register(args[0])];
      instruction.reads = [register(args[1])];
    } else if (BINARY[op]) {
      count(3);
      instruction.kind = 'binary';
      instruction.operator = BINARY[op];
      instruction.writes = [register(args[0])];
      instruction.reads = [register(args[1]), register(args[2])];
    } else if (op === 'MINUS' || op === 'NOT') {
      count(2);
      instruction.kind = 'unary';
      instruction.operator = op === 'MINUS' ? 'negate' : 'logical_not';
      instruction.writes = [register(args[0])];
      instruction.reads = [register(args[1])];
    } else if (op === 'JUMP' || op === 'JUMPBACK') {
      count(1);
      instruction.kind = 'jump';
      instruction.label = args[0];
    } else if (op === 'JUMPIF' || op === 'JUMPIFNOT') {
      count(2);
      instruction.kind = 'branch';
      instruction.reads = [register(args[0])];
      instruction.inverted = op === 'JUMPIFNOT';
      instruction.label = args[1];
    } else if (/^JUMPIF(?:NOT)?(?:EQ|LT|LE)$/.test(op)) {
      count(3);
      instruction.kind = 'branch';
      instruction.operator = COMPARE[op.slice(-2)];
      instruction.reads = [register(args[0]), register(args[1])];
      instruction.inverted = op.startsWith('JUMPIFNOT');
      instruction.label = args[2];
    } else if (op === 'RETURN') {
      count(2);
      assert.match(args[1], /^\d+$/, 'open return protocol is unsupported');
      const first = register(args[0]);
      const results = Number(args[1]);
      assert.ok(results <= 255 && first + results <= 255, 'invalid return range');
      instruction.kind = 'return';
      instruction.reads = Array.from({ length: results }, (_, i) => first + i);
    } else {
      throw new Error(`unsupported opcode ${op} at disassembly line ${record.line_number}`);
    }
    instructions.push(instruction);
  }
  assert.ok(instructions.length > 0, 'empty selected function');
  for (const [index, instruction] of instructions.entries()) {
    if (instruction.label !== undefined) {
      assert.ok(labels.has(instruction.label), `unknown label ${instruction.label}`);
      instruction.target = labels.get(instruction.label);
      assert.ok(instruction.target < instructions.length, 'jump past function');
    }
    instruction.successors = instruction.kind === 'return' ? []
      : instruction.kind === 'jump' ? [instruction.target]
        : instruction.kind === 'branch' ? [instruction.target, index + 1] : [index + 1];
    assert.ok(instruction.successors.every((target) => target < instructions.length), 'function falls off end');
  }
  const registers = [...new Set([
    ...Array.from({ length: parameter_count }, (_, i) => i),
    ...instructions.flatMap((instruction) => [...instruction.reads, ...instruction.writes]),
  ])].sort((a, b) => a - b);
  const reachable = new Set();
  const pending = [0];
  while (pending.length) {
    const index = pending.pop();
    if (reachable.has(index)) continue;
    reachable.add(index);
    pending.push(...instructions[index].successors);
  }
  // Reject reads not initialized on every incoming path, including back edges.
  const predecessors = instructions.map(() => []);
  for (const index of reachable) {
    for (const target of instructions[index].successors) predecessors[target].push(index);
  }
  const initial = new Set(Array.from({ length: parameter_count }, (_, i) => i));
  const incoming = instructions.map(() => new Set(registers));
  const outgoing = instructions.map(() => new Set(registers));
  let changed = true;
  while (changed) {
    changed = false;
    for (const index of reachable) {
      const sources = predecessors[index].map((parent) => outgoing[parent]);
      if (index === 0) sources.push(initial);
      const next = new Set(registers.filter((reg) => sources.every((source) => source.has(reg))));
      const after = new Set([...next, ...instructions[index].writes]);
      if (next.size !== incoming[index].size || after.size !== outgoing[index].size) changed = true;
      incoming[index] = next;
      outgoing[index] = after;
    }
  }
  for (const index of reachable) {
    for (const reg of instructions[index].reads) {
      assert.ok(incoming[index].has(reg), `uninitialized R${reg} at disassembly line ${instructions[index].line_number}`);
    }
  }
  return {
    schema_version: 'compiler_disassembly_handoff_v1',
    listing_sha256: createHash('sha256').update(text).digest('hex'),
    function_index, parameter_count, registers, instructions,
    signature_origin: 'caller-declared; text disassembly does not encode arity',
    scope: 'selected capture-free function; remaining compiled functions are not lifted',
  };
}
