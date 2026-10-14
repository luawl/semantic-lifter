import { createHash } from 'node:crypto';

// Supported input: the text listing of `luau-compile --text --dump-constants -O0 -g0` from
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
// Operand counts per accepted opcode; LOADB takes an optional third operand, its relative skip. SETLIST's fourth
// operand is its bracketed start index, parsed by its own pattern (it is never a comment).
const OPERAND_COUNTS = new Map([
  ['LOADK', [2]], ['LOADN', [2]], ['LOADNIL', [1]], ['LOADB', [3, 2]], ['MOVE', [2]],
  ['MINUS', [2]], ['NOT', [2]], ['LENGTH', [2]], ['CONCAT', [3]],
  ['JUMP', [1]], ['JUMPBACK', [1]], ['JUMPIF', [2]], ['JUMPIFNOT', [2]], ['RETURN', [2]],
  ['GETGLOBAL', [2]], ['SETGLOBAL', [2]],
  ['CALL', [3]], ['NAMECALL', [3]], ['GETVARARGS', [2]],
  ['NEWTABLE', [3]], ['GETTABLE', [3]], ['SETTABLE', [3]], ['GETTABLEKS', [3]], ['SETTABLEKS', [3]], ['SETLIST', [4]],
  ['DUPTABLE', [2]],
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

// A K line is decoded only where an instruction references it: a string body is
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

// `CALL R<a> <n> <m>` prints B-1 and C-1: n arguments R<a+1..a+n> after the callee R<a> and m
// results written from R<a>. A count of -1 is the open protocol, returned as null: n = -1 takes
// the arguments up to the pack the previous instruction left, m = -1 leaves the results as a pack at R<a>.
function callCounts(args, site) {
  const base = register(args[0], site);
  const [count, results] = args.slice(1).map((text) => {
    if (text === '-1') return null;
    if (!/^\d+$/.test(text)) refuseAt(site, 'operand_form', 'invalid call count');
    return Number(text);
  });
  if (!(base + (count ?? 0) < 255 && base + (results ?? 0) <= 255)) refuseAt(site, 'operand_form', 'invalid call range');
  return { base, count, results };
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
  const records = functions.get(function_index);
  // The adjacent-only open protocol: an open producer leaves its values as a pack at R<p> and
  // kills R<p..>; only the next instruction may consume that pack, and only when no label sits on it (packs never
  // cross a label). `openPack` is the pack of the instruction just read ({ at: p, site }).
  let openPack = null;
  // An open consumer reads R<..p-1> as places and the pack at R<p>, which must lie at or above R<first>.
  const consume = (site, first, message) => {
    if (!(openPack && openPack.at >= first)) refuseAt(site, 'open_consumer_without_producer', message);
    if ([...labels.values()].includes(instructions.length)) refuseAt(site, 'open_pack_crosses_label', 'open pack crosses a label');
    const { at } = openPack;
    openPack = null;
    return at;
  };
  for (let position = 0; position < records.length; position += 1) {
    const record = records[position];
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
    // `SETLIST R<a> R<b> <c> [<s>]`: the bracket is the start-index operand, kept as args[3].
    const args = (op === 'SETLIST' ? /^(\S+)\s+(\S+)\s+(\S+)\s+\[([^\]]*)\]$/.exec(match[2] ?? '')?.slice(1)
      : operands(match[2] ?? '', counts)) ?? refuseAt(site, 'operand_form', `${op}: operand count`);
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
    } else if (op === 'RETURN' && args[1] === '-1') {
      // `RETURN R<a> -1` returns R<a..p-1> and then the pack the previous instruction left at R<p>.
      const first = register(args[0], site);
      const pack = consume(site, first, 'open return protocol is unsupported');
      instruction.kind = 'return';
      instruction.reads = Array.from({ length: pack - first }, (_, i) => first + i);
      instruction.consumes_pack_from = pack;
    } else if (op === 'RETURN') {
      if (!/^\d+$/.test(args[1])) refuseAt(site, 'open_protocol_unsupported', 'open return protocol is unsupported');
      const first = register(args[0], site);
      const results = Number(args[1]);
      if (!(results <= 255 && first + results <= 255)) refuseAt(site, 'operand_form', 'invalid return range');
      instruction.kind = 'return';
      instruction.reads = Array.from({ length: results }, (_, i) => first + i);
    } else if (op === 'GETGLOBAL' || op === 'SETGLOBAL') {
      // A named environment access: the name is an identifier string constant read through
      // the lazy decoder; GETGLOBAL writes R<a>, SETGLOBAL reads its source R<a>.
      if (!/^K\d+$/.test(args[1])) refuseAt(site, 'operand_form', 'invalid constant operand');
      const key = Number(args[1].slice(1));
      if (!constants.has(key)) refuseAt(site, 'operand_form', 'constant is absent');
      const { string: name } = constantValue(key, constants.get(key), site);
      if (typeof name !== 'string') refuseAt(site, 'constant_kind_mismatch', `${op}: K${key} is not a string`);
      if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name)) refuseAt(site, 'non_identifier_name', `${op}: K${key} is not an identifier`);
      instruction.kind = op === 'GETGLOBAL' ? 'environment_get' : 'environment_set';
      instruction.name = name;
      if (op === 'GETGLOBAL') instruction.writes = [register(args[0], site)];
      else instruction.reads = [register(args[0], site)];
    } else if (op === 'CALL') {
      // A call with fixed counts: it reads the callee R<a> and the arguments R<a+1..a+n>,
      // writes the results R<a..a+m-1> and kills its frame from R<a+m> up (clobbers_from). Open counts:
      // n = -1 reads the arguments R<a+1..p-1> and passes the pending pack; m = -1 writes nothing and leaves its
      // results as a pack at R<a> (produces_pack_at), killing R<a..>.
      const { base, count, results } = callCounts(args, site);
      instruction.kind = 'call';
      instruction.callee = base;
      if (count === null) {
        const pack = consume(site, base + 1, 'open call arguments have no adjacent producer');
        instruction.arguments = Array.from({ length: pack - base - 1 }, (_, i) => base + 1 + i);
        instruction.consumes_pack_from = pack;
      } else {
        instruction.arguments = Array.from({ length: count }, (_, i) => base + 1 + i);
      }
      instruction.result_count = results;
      instruction.reads = [base, ...instruction.arguments];
      instruction.writes = Array.from({ length: results ?? 0 }, (_, i) => base + i);
      if (results === null) instruction.produces_pack_at = base;
      instruction.clobbers_from = base + (results ?? 0);
    } else if (op === 'NAMECALL') {
      // A method call: `NAMECALL R<a> R<b> K<k>` sets R<a+1> = R<b> and R<a> = R<b>[K<k>] for
      // the `CALL R<a> <n> <m>` on the next line (n counts self). The pair is ONE namecall instruction that reads
      // the receiver R<b> and the arguments R<a+2..a+n>; R<a> and R<a+1> are never materialised.
      const base = register(args[0], site);
      const receiver = register(args[1], site);
      if (!/^K\d+$/.test(args[2])) refuseAt(site, 'operand_form', 'invalid constant operand');
      const key = Number(args[2].slice(1));
      if (!constants.has(key)) refuseAt(site, 'operand_form', 'constant is absent');
      const { string: method } = constantValue(key, constants.get(key), site);
      if (typeof method !== 'string') refuseAt(site, 'constant_kind_mismatch', `${op}: K${key} is not a string`);
      if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(method)) refuseAt(site, 'non_identifier_name', `${op}: K${key} is not an identifier`);
      const next = records[position + 1];
      const call = /^(?:(L\d+):\s*)?CALL(?:\s+(.*))?$/.exec(next?.line ?? '');
      const callArgs = call && operands(call[2] ?? '', OPERAND_COUNTS.get('CALL'));
      if (!callArgs || callArgs[0] !== args[0]) refuseAt(site, 'namecall_without_call', `NAMECALL is not followed by CALL ${args[0]}`);
      const callSite = { line_number: next.line_number, op: 'CALL' };
      if (call[1]) refuseAt(callSite, 'label_inside_namecall', `label ${call[1]} inside NAMECALL`);
      const { count, results } = callCounts(callArgs, callSite);
      if (count !== null && count < 1) refuseAt(callSite, 'operand_form', 'NAMECALL: CALL argument count must include self');
      instruction.kind = 'namecall';
      instruction.receiver = receiver;
      instruction.method = method;
      // Open counts as for CALL: the open arguments are R<a+2..p-1> (self is R<a+1>, so p >= a+2).
      if (count === null) {
        const pack = consume(site, base + 2, 'open call arguments have no adjacent producer');
        instruction.arguments = Array.from({ length: pack - base - 2 }, (_, i) => base + 2 + i);
        instruction.consumes_pack_from = pack;
      } else {
        instruction.arguments = Array.from({ length: count - 1 }, (_, i) => base + 2 + i);
      }
      instruction.result_count = results;
      instruction.reads = [receiver, ...instruction.arguments];
      instruction.writes = Array.from({ length: results ?? 0 }, (_, i) => base + i);
      if (results === null) instruction.produces_pack_at = base;
      instruction.clobbers_from = base + (results ?? 0);
      instruction.line_numbers = [record.line_number, next.line_number];
      position += 1;
    } else if (op === 'GETVARARGS') {
      // `GETVARARGS R<a> <n>` copies n of the function's varargs into R<a..a+n-1>; n = -1 leaves
      // them all as a pack at R<a> (an open producer that kills R<a..>). Only a declared variadic function has them.
      if (!is_variadic) refuseAt(site, 'varargs_in_non_variadic_function', 'GETVARARGS in a function not declared variadic');
      const base = register(args[0], site);
      instruction.kind = 'varargs';
      if (args[1] === '-1') {
        instruction.count = null;
        instruction.produces_pack_at = base;
        instruction.clobbers_from = base;
      } else {
        if (!/^[1-9]\d*$/.test(args[1])) refuseAt(site, 'operand_form', 'invalid varargs count');
        const count = Number(args[1]);
        if (!(base + count <= 255)) refuseAt(site, 'operand_form', 'invalid varargs range');
        instruction.count = count;
        instruction.writes = Array.from({ length: count }, (_, i) => base + i);
      }
    } else if (op === 'NEWTABLE') {
      // `NEWTABLE R<a> <h> <n>`: a fresh table in R<a>; the hash and array size hints are not kept.
      if (!/^\d+$/.test(args[1]) || !/^\d+$/.test(args[2])) refuseAt(site, 'operand_form', 'invalid table size hint');
      instruction.kind = 'new_table';
      instruction.writes = [register(args[0], site)];
    } else if (op === 'GETTABLE' || op === 'SETTABLE') {
      // Keyed access; operand roles differ: `GETTABLE R<a> R<b> R<c>` is R<a> = R<b>[R<c>], `SETTABLE R<a> R<b> R<c>`
      // is R<b>[R<c>] = R<a> (value, table, key).
      const target = register(args[0], site);
      instruction.table = register(args[1], site);
      instruction.key = register(args[2], site);
      if (op === 'GETTABLE') {
        instruction.kind = 'table_get';
        instruction.reads = [instruction.table, instruction.key];
        instruction.writes = [target];
      } else {
        instruction.kind = 'table_set';
        instruction.value = target;
        instruction.reads = [instruction.table, instruction.key, target];
      }
    } else if (op === 'GETTABLEKS' || op === 'SETTABLEKS') {
      // Named access: the key is the string constant K<k>, read through the lazy decoder; the roles are as for
      // GETTABLE/SETTABLE (SETTABLEKS reads its source R<a>).
      if (!/^K\d+$/.test(args[2])) refuseAt(site, 'operand_form', 'invalid constant operand');
      const key = Number(args[2].slice(1));
      if (!constants.has(key)) refuseAt(site, 'operand_form', 'constant is absent');
      const { string: name } = constantValue(key, constants.get(key), site);
      if (typeof name !== 'string') refuseAt(site, 'constant_kind_mismatch', `${op}: K${key} is not a string`);
      const target = register(args[0], site);
      instruction.table = register(args[1], site);
      instruction.key_constant = { string: name };
      if (op === 'GETTABLEKS') {
        instruction.kind = 'table_get';
        instruction.reads = [instruction.table];
        instruction.writes = [target];
      } else {
        instruction.kind = 'table_set';
        instruction.value = target;
        instruction.reads = [instruction.table, target];
      }
    } else if (op === 'SETLIST') {
      // `SETLIST R<a> R<b> <c> [<s>]` stores R<b..b+c-1> at R<a>[s..]; c = -1 is an open consumer that stores
      // R<b..p-1> and then the pack the previous instruction left at R<p>. A SETLIST is accepted only as a member of a
      // constructor window (below).
      const table = register(args[0], site);
      const first = register(args[1], site);
      if (!/^[1-9]\d*$/.test(args[3])) refuseAt(site, 'operand_form', 'invalid SETLIST start index');
      instruction.kind = 'set_list';
      instruction.table = table;
      if (args[2] === '-1') {
        const pack = consume(site, first, 'open SETLIST has no adjacent producer');
        instruction.values = Array.from({ length: pack - first }, (_, i) => first + i);
        instruction.consumes_pack_from = pack;
      } else {
        if (!/^\d+$/.test(args[2])) refuseAt(site, 'operand_form', 'invalid SETLIST count');
        const count = Number(args[2]);
        if (!(first + count <= 255)) refuseAt(site, 'operand_form', 'invalid SETLIST range');
        instruction.values = Array.from({ length: count }, (_, i) => first + i);
      }
      instruction.first_index = Number(args[3]);
      instruction.reads = [table, ...instruction.values];
    } else if (op === 'DUPTABLE') {
      // DUPTABLE: the template constant prints as `{...}`, so its keys are not in the listing.
      refuseAt(site, 'table_template_opaque', 'DUPTABLE template keys are not in the listing');
    } else {
      refuse('unsupported_opcode', `unsupported opcode ${op} at disassembly line ${record.line_number}`, record.line_number, op);
    }
    // A pack still pending here was not consumed by this instruction, the one right after its producer.
    if (openPack) refuseAt(openPack.site, 'open_pack_not_consumed', 'open pack is not consumed by the next instruction');
    if (instruction.produces_pack_at !== undefined) openPack = { at: instruction.produces_pack_at, site };
    instructions.push(instruction);
  }
  if (openPack) refuseAt(openPack.site, 'open_pack_not_consumed', 'open pack is not consumed by the next instruction');
  if (instructions.length === 0) refuse('listing_structure', 'empty selected function');
  const labelled = new Set(labels.values());
  for (const [index, instruction] of instructions.entries()) {
    if (instruction.label !== undefined) {
      if (!labels.has(instruction.label)) refuseAt(instruction, 'listing_structure', `unknown label ${instruction.label}`);
      instruction.target = labels.get(instruction.label);
      if (!(instruction.target < instructions.length)) refuseAt(instruction, 'listing_structure', 'jump past function');
    }
    // `LOADB R<a> <b> +1` skips the next instruction. The compiler labels the skip target, so the skip is
    // accepted only over a following LOADB onto a labelled instruction.
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
  // Constructor windows. A `NEWTABLE R<t>` opens a window when a `SETLIST R<t>` follows: the
  // window runs to the last store into R<t> (SETLIST, SETTABLE/SETTABLEKS with table R<t>) before the first instruction
  // that reads or writes R<t> in any other way (a call frame that kills R<t> included), carries a label, or jumps,
  // branches or returns (a LOADB skip included). The NEWTABLE and every member carry `constructor`, the last member also
  // `complete`; a member reads only its key and value registers, never R<t>. Field order is the listing's store order,
  // which at -O0 is source order.
  const storeRegisters = (store) => (store.kind === 'set_list' ? store.values
    : [...(store.key === undefined ? [] : [store.key]), store.value]);
  for (const [create, table] of instructions.entries()) {
    if (table.kind !== 'new_table') continue;
    const [t] = table.writes;
    const members = [];
    for (let index = create + 1; index < instructions.length; index += 1) {
      const instruction = instructions[index];
      const transfers = ['jump', 'branch', 'return'].includes(instruction.kind) || instruction.successors[0] !== index + 1;
      if (labelled.has(index) || transfers) break;
      const store = (instruction.kind === 'set_list' || instruction.kind === 'table_set') && instruction.table === t;
      const touched = store ? storeRegisters(instruction) : [...instruction.reads, ...instruction.writes];
      if (touched.includes(t) || (instruction.clobbers_from ?? Infinity) <= t) break;
      if (store) members.push(index);
    }
    if (!members.some((index) => instructions[index].kind === 'set_list')) continue;
    const last = members[members.length - 1];
    // List items continue from 1 (`[1]`, then the previous start plus the previous count); an open tail is last.
    let next = 1;
    for (const index of members) {
      const member = instructions[index];
      if (member.kind !== 'set_list') continue;
      if (member.first_index !== next) {
        refuseAt(member, 'setlist_index_gap', `SETLIST start index ${member.first_index} does not continue the list at ${next}`);
      }
      if (member.consumes_pack_from !== undefined && index !== last) {
        refuseAt(member, 'constructor_window_unsupported', 'open SETLIST is not the last member of its constructor');
      }
      next = member.first_index + member.values.length;
    }
    // `literal` when every keyed member except the last has a definitely valid key: a SETTABLEKS, or a key register
    // last written inside the window by LOADK of a string or non-NaN number or by LOADB; mirroring
    // requiresOrderedWrites (luau/ast_frontend_tables.luau:56-67). Otherwise `ordered`.
    const definitelyValidKey = (index) => {
      const { key } = instructions[index];
      if (key === undefined) return true;
      for (let at = index - 1; at > create; at -= 1) {
        const writer = instructions[at];
        if (writer.writes.includes(key) || (writer.clobbers_from ?? Infinity) <= key) {
          return writer.op === 'LOADB'
            || (writer.op === 'LOADK' && (typeof writer.value.string === 'string' || Number.isFinite(writer.value.number)));
        }
      }
      return false;
    };
    const mode = members.every((index) => index === last || instructions[index].kind !== 'table_set'
      || definitelyValidKey(index)) ? 'literal' : 'ordered';
    table.constructor = { create, mode };
    for (const index of members) {
      instructions[index].constructor = { create, mode };
      instructions[index].reads = storeRegisters(instructions[index]);
    }
    instructions[last].complete = true;
  }
  for (const instruction of instructions) {
    if (instruction.kind === 'set_list' && !Object.hasOwn(instruction, 'constructor')) {
      refuseAt(instruction, 'constructor_window_unsupported', 'SETLIST outside a constructor window');
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
      // A call kills its frame: outgoing = (incoming - {r >= clobbers_from}) + writes.
      const clobbers = instructions[index].clobbers_from ?? Infinity;
      const after = new Set([...[...next].filter((reg) => reg < clobbers), ...instructions[index].writes]);
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
