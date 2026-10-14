import { createHash } from 'node:crypto';

// Supported input (decision D4): the text listing of `luau-compile --text --dump-constants -O0 -g0` from
// Luau 0.720, the pinned compiler. Other optimization levels, binary bytecode and original source ASTs are not
// inputs. Everything this adapter cannot represent faithfully is refused with a typed DisassemblyRefusal.

const BINARY = {
  ADD: 'add', SUB: 'subtract', MUL: 'multiply', DIV: 'divide',
  IDIV: 'floor_divide', MOD: 'modulo', POW: 'power',
};
const COMPARE = {
  EQ: 'equal', LT: 'less', LE: 'less_equal',
};
const UNARY = {
  MINUS: 'negate', NOT: 'logical_not', LENGTH: 'length',
};
// Operand counts per accepted opcode; LOADB takes an optional third operand, its relative skip.
const OPERAND_COUNTS = new Map([
  ['LOADK', [2]], ['LOADN', [2]], ['LOADNIL', [1]], ['LOADB', [3, 2]], ['MOVE', [2]],
  ['MINUS', [2]], ['NOT', [2]], ['LENGTH', [2]], ['CONCAT', [3]],
  ['JUMP', [1]], ['JUMPBACK', [1]], ['JUMPIF', [2]], ['JUMPIFNOT', [2]], ['RETURN', [2]],
  ...Object.keys(BINARY).map((op) => [op, [3]]),
  ...['', 'NOT'].flatMap((not) => Object.keys(COMPARE).map((test) => [`JUMPIF${not}${test}`, [3]])),
]);

export class DisassemblyRefusal extends Error {
  constructor(code, message, line_number = null, opcode = null) {
    super(message);
    this.name = 'DisassemblyRefusal';
    this.code = code;
    this.line_number = line_number;
    this.opcode = opcode;
  }
}

function refuse(code, message, line_number = null, opcode = null) {
  throw new DisassemblyRefusal(code, message, line_number, opcode);
}

// A site is the instruction being read ({ line_number, op }); its refusals name the listing line.
function refuseAt(site, code, message) {
  refuse(code, `${message} at disassembly line ${site.line_number}`, site.line_number, site.op);
}

function register(text, site) {
  if (!/^R\d+$/.test(text ?? '')) refuseAt(site, 'operand_form', 'invalid register operand');
  const value = Number(text.slice(1));
  if (!(value < 255)) refuseAt(site, 'operand_form', 'register outside Luau register range');
  return value;
}

// Nil, boolean and finite numeric literals; anything else is reported, not decoded.
function literal(text) {
  if (text === 'nil') return { value: { nil_value: {} } };
  if (text === 'true' || text === 'false') return { value: { boolean: text === 'true' } };
  if (!/^-?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$/.test(text)) return { problem: 'unsupported constant' };
  const value = Number(text);
  if (!(Number.isFinite(value) && !Object.is(value, -0))) return { problem: 'unsupported numeric constant' };
  return { value: { number: value } };
}

// A K line is decoded only where an instruction references it (T2-ADAPTER.md section 3.4): a string body is
// everything between the first `'` after `K<n>: ` and the final `'`. The compiler cuts strings of 32 or more
// bytes and marks them `'...`, prints control bytes as `\xNN` without escaping a literal backslash, and the
// listing text holds U+FFFD for bytes that are not UTF-8, so a body is exact only when the line ends in `'`
// and the body has no `\` and no U+FFFD. Templates (`{...}`), imports and every other form are refused.
function constantValue(key, text, site) {
  const fail = (reason) => refuseAt(site, 'unsupported_constant', `unsupported constant K${key}: ${reason}`);
  if (text.startsWith("'")) {
    if (text.length >= 5 && text.endsWith("'...")) fail('truncated string');
    if (text.length < 2 || !text.endsWith("'")) fail('unsupported constant form');
    const body = text.slice(1, -1);
    if (body.includes('\\')) fail('escape sequence in string');
    if (body.includes('�')) fail('not exact UTF-8');
    return { string: body };
  }
  return literal(text).value ?? fail('unsupported constant form');
}

// The opcode's operands are matched first (whitespace-separated tokens, none starting with `[`); the rest of
// the line must be empty or one bracketed comment ` [...]` (anything up to the final `]`), which is ignored.
function operands(text, counts) {
  for (const count of counts) {
    const match = new RegExp(`^([^\\s\\[]\\S*(?:\\s+[^\\s\\[]\\S*){${count - 1}})(?:\\s+\\[.*\\])?$`).exec(text);
    if (match) return match[1].split(/\s+/);
  }
  return null;
}

// The compiler owns bytecode decoding. This adapter accepts its pinned text
// format, not arbitrary binary bytecode or original source ASTs.
export function parseDisassembly(text, { function_index = 0, parameter_count = 2, is_variadic = false } = {}) {
  if (!(Number.isInteger(function_index) && function_index >= 0)) {
    refuse('invalid_options', 'function_index must be a non-negative integer');
  }
  if (!(Number.isInteger(parameter_count) && parameter_count >= 0 && parameter_count < 255)) {
    refuse('invalid_options', 'parameter_count must be an integer from 0 to 254');
  }
  if (typeof is_variadic !== 'boolean') refuse('invalid_options', 'is_variadic must be a boolean');
  const functions = new Map();
  let current = null;
  for (const [index, raw] of text.split(/\r?\n/).entries()) {
    const line = raw.trim();
    const site = { line_number: index + 1, op: null };
    const header = /^Function (\d+) \(.*\):$/.exec(line);
    if (header) {
      const id = Number(header[1]);
      if (functions.has(id)) refuseAt(site, 'listing_structure', 'duplicate function header');
      current = [];
      functions.set(id, current);
    } else if (line) {
      if (!current) refuseAt(site, 'listing_structure', 'text before function header');
      current.push({ line, line_number: index + 1 });
    }
  }
  if (!functions.has(function_index)) refuse('listing_structure', 'selected function is absent');
  const constants = new Map();
  const labels = new Map();
  const instructions = [];
  for (const record of functions.get(function_index)) {
    let { line } = record;
    if (line.startsWith('REMARK ')) continue;
    const constant = /^K(\d+): (.+)$/.exec(line);
    if (constant) {
      const key = Number(constant[1]);
      if (constants.has(key)) refuseAt({ line_number: record.line_number, op: null }, 'listing_structure', 'duplicate constant');
      constants.set(key, constant[2]);
      continue;
    }
    const label = /^(L\d+):\s*(.*)$/.exec(line);
    if (label) {
      if (labels.has(label[1])) refuseAt({ line_number: record.line_number, op: null }, 'listing_structure', 'duplicate label');
      labels.set(label[1], instructions.length);
      line = label[2];
      if (!line) continue;
    }
    const match = /^([A-Z][A-Z0-9]*)(?:\s+(.*))?$/.exec(line);
    if (!match) refuse('listing_structure', `unrecognized disassembly at line ${record.line_number}`, record.line_number);
    const op = match[1];
    const site = { line_number: record.line_number, op };
    const counts = OPERAND_COUNTS.get(op);
    if (!counts) refuse('unsupported_opcode', `unsupported opcode ${op} at disassembly line ${record.line_number}`, record.line_number, op);
    const args = operands(match[2] ?? '', counts) ?? refuseAt(site, 'operand_form', `${op}: operand count`);
    const instruction = { op, args, line_number: record.line_number, reads: [], writes: [] };
    if (op === 'LOADK') {
      if (!/^K\d+$/.test(args[1])) refuseAt(site, 'operand_form', 'invalid constant operand');
      const key = Number(args[1].slice(1));
      if (!constants.has(key)) refuseAt(site, 'operand_form', 'constant is absent');
      instruction.kind = 'constant';
      instruction.value = constantValue(key, constants.get(key), site);
      instruction.writes = [register(args[0], site)];
    } else if (op === 'LOADN') {
      instruction.kind = 'constant';
      const { value, problem } = literal(args[1]);
      if (problem) refuseAt(site, 'operand_form', problem);
      instruction.value = value;
      instruction.writes = [register(args[0], site)];
    } else if (op === 'LOADNIL') {
      instruction.kind = 'constant';
      instruction.value = { nil_value: {} };
      instruction.writes = [register(args[0], site)];
    } else if (op === 'LOADB') {
      if (args[1] !== '0' && args[1] !== '1') refuseAt(site, 'operand_form', 'invalid boolean operand');
      instruction.kind = 'constant';
      instruction.value = { boolean: args[1] === '1' };
      instruction.writes = [register(args[0], site)];
    } else if (op === 'MOVE') {
      instruction.kind = 'move';
      instruction.writes = [register(args[0], site)];
      instruction.reads = [register(args[1], site)];
    } else if (BINARY[op]) {
      instruction.kind = 'binary';
      instruction.operator = BINARY[op];
      instruction.writes = [register(args[0], site)];
      instruction.reads = [register(args[1], site), register(args[2], site)];
    } else if (UNARY[op]) {
      instruction.kind = 'unary';
      instruction.operator = UNARY[op];
      instruction.writes = [register(args[0], site)];
      instruction.reads = [register(args[1], site)];
    } else if (op === 'CONCAT') {
      instruction.kind = 'concat';
      instruction.writes = [register(args[0], site)];
      const first = register(args[1], site);
      const last = register(args[2], site);
      if (first > last) refuseAt(site, 'operand_form', 'invalid concat range');
      instruction.reads = Array.from({ length: last - first + 1 }, (_, i) => first + i);
    } else if (op === 'JUMP' || op === 'JUMPBACK') {
      instruction.kind = 'jump';
      instruction.label = args[0];
    } else if (op === 'JUMPIF' || op === 'JUMPIFNOT') {
      instruction.kind = 'branch';
      instruction.reads = [register(args[0], site)];
      instruction.inverted = op === 'JUMPIFNOT';
      instruction.label = args[1];
    } else if (/^JUMPIF(?:NOT)?(?:EQ|LT|LE)$/.test(op)) {
      instruction.kind = 'branch';
      instruction.operator = COMPARE[op.slice(-2)];
      instruction.reads = [register(args[0], site), register(args[1], site)];
      instruction.inverted = op.startsWith('JUMPIFNOT');
      instruction.label = args[2];
    } else if (op === 'RETURN') {
      if (!/^\d+$/.test(args[1])) refuseAt(site, 'open_protocol_unsupported', 'open return protocol is unsupported');
      const first = register(args[0], site);
      const results = Number(args[1]);
      if (!(results <= 255 && first + results <= 255)) refuseAt(site, 'operand_form', 'invalid return range');
      instruction.kind = 'return';
      instruction.reads = Array.from({ length: results }, (_, i) => first + i);
    } else {
      refuse('unsupported_opcode', `unsupported opcode ${op} at disassembly line ${record.line_number}`, record.line_number, op);
    }
    instructions.push(instruction);
  }
  if (instructions.length === 0) refuse('listing_structure', 'empty selected function');
  const labelled = new Set(labels.values());
  for (const [index, instruction] of instructions.entries()) {
    if (instruction.label !== undefined) {
      if (!labels.has(instruction.label)) refuseAt(instruction, 'listing_structure', `unknown label ${instruction.label}`);
      instruction.target = labels.get(instruction.label);
      if (!(instruction.target < instructions.length)) refuseAt(instruction, 'listing_structure', 'jump past function');
    }
    // `LOADB R<a> <b> +1` skips the next instruction. The compiler labels the skip target, so the skip is
    // accepted only over a following LOADB onto a labelled instruction (T2-ADAPTER.skeptic.md D5).
    const skip = instruction.op === 'LOADB' && instruction.args.length === 3;
    if (skip && !(instruction.args[2] === '+1' && instructions[index + 1]?.op === 'LOADB' && labelled.has(index + 2))) {
      refuseAt(instruction, 'relative_skip_unsupported', `relative skip ${instruction.args[2]} is unsupported`);
    }
    instruction.successors = instruction.kind === 'return' ? []
      : instruction.kind === 'jump' ? [instruction.target]
        : instruction.kind === 'branch' ? [instruction.target, index + 1]
          : skip ? [index + 2] : [index + 1];
    if (!instruction.successors.every((target) => target < instructions.length)) {
      refuseAt(instruction, 'listing_structure', 'function falls off end');
    }
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
      if (!incoming[index].has(reg)) {
        refuse('uninitialized_register', `uninitialized R${reg} at disassembly line ${instructions[index].line_number}`,
          instructions[index].line_number, instructions[index].op);
      }
    }
  }
  return {
    schema_version: 'compiler_disassembly_handoff_v2',
    listing_sha256: createHash('sha256').update(text).digest('hex'),
    function_index, parameter_count, is_variadic, registers, instructions,
    signature_origin: 'caller-declared; text disassembly does not encode arity',
    scope: 'selected capture-free function; remaining compiled functions are not lifted',
  };
}
