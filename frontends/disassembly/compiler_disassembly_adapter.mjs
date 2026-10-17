import { createHash } from 'node:crypto';

// Supported input (decision D4): the text listing of `luau-compile --text --dump-constants -O0 -g0` from
// Luau 0.720, the pinned compiler. Other optimization levels, binary bytecode and original source ASTs are not
// inputs. Everything this adapter cannot represent faithfully is refused with a typed DisassemblyRefusal.
// A caller may declare that level (`optimization_level: 0`); only then is a DUPTABLE record template lifted, from its
// `REMARK allocation: table template N` line and its N record stores (PLAN-T6 Task T6.8).
// Iteration (T4-ADAPTER-ITERATION), at that -O0 -g0 level only: FORNPREP/FORGPREP become `iteration_prepare` and
// FORNLOOP/FORGLOOP `iteration_loop` records that share one `loop` region (iteration, base, prepare, latch, exit,
// variables). A loop shape outside that region form is refused as iteration_pair_mismatch, iteration_state_written,
// iteration_state_read, iteration_region_entry or iteration_region_exit; the -O1 fast paths stay refused: the ipairs
// marker `[inext]` as iteration_fast_path_unsupported, FORGPREP_NEXT and FORGPREP_INEXT as unsupported_opcode.
// Closures (T4-ADAPTER-CLOSURES), at that -O0 -g0 level only: `NEWCLOSURE R<a> P<k>` and the CAPTURE lines that follow
// it become one `closure` record, GETUPVAL `upvalue_get`, SETUPVAL `upvalue_set` and CLOSEUPVALS `close_upvalues`. The
// listing prints no function tree (P<k> indexes the creating function's own child list) and no arity, so the caller
// declares every nested function to lift in the option `nested: { "<function index>": { parent, prototype,
// parameter_count, is_variadic } }` (default {}; is_variadic default false): its creating function (`parent`: the
// selected function or another declared nested function) and the k of the creator's `NEWCLOSURE R<a> P<k>` line
// (`prototype`), declared as parameter_count and is_variadic are for the selected function (decision D1: the tree is
// never recovered from the post-order function numbering). A selected function without closure opcodes yields the v2
// handoff unchanged; otherwise the handoff is compiler_disassembly_handoff_v3: the v2 fields plus `functions`, the
// declared tree in pre-order (children by prototype), each { function_index, parent_index, parameter_count,
// is_variadic, upvalues: [{ class, line_number }], registers, instructions }. Typed refusals, in this order:
// invalid_options (the map's shape); uninstantiated_function (the listing-wide census: a function after an
// always-terminating statement keeps its number but gets no NEWCLOSURE line, and the text cannot tell which);
// selected_function_captures; nested_map_mismatch; nested_function_undeclared; then, while parsing,
// capture_count_mismatch, label_inside_closure, capture_without_closure, setupval_on_value_capture,
// open_pack_crosses_label and DUPCLOSURE (an -O1 form) as unsupported_opcode; then captured_register_reused_after_close
// and self_capture_in_loop.

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
  // The -O0 iteration pair (T4-ADAPTER-ITERATION). FORGLOOP is parsed by its own exact pattern below.
  ['FORNPREP', [2]], ['FORNLOOP', [2]], ['FORGPREP', [2]], ['FORGLOOP', [3]],
  // The -O0 conditional moves (T4-ADAPTER-ANDOR-IMPORT-DUPTABLE). ANDK, ORK and GETIMPORT, -O1 forms, stay out of the table.
  ['AND', [3]], ['OR', [3]],
  // Closures (T4-ADAPTER-CLOSURES). CAPTURE is read only by the NEWCLOSURE case it follows; a CAPTURE anywhere else is
  // refused. DUPCLOSURE, an -O1 form, stays out of the table.
  ['GETUPVAL', [2]], ['SETUPVAL', [2]], ['NEWCLOSURE', [2]], ['CLOSEUPVALS', [1]], ['CAPTURE', [2]],
  ...Object.keys(BINARY).map((op) => [op, [3]]),
  ...['', 'NOT'].flatMap((not) => Object.keys(COMPARE).map((test) => [`JUMPIF${not}${test}`, [3]])),
]);
// A selected function with one of these opcodes takes the closure path (handoff v3).
const CLOSURE_OPCODES = new Set(['NEWCLOSURE', 'DUPCLOSURE', 'CAPTURE', 'GETUPVAL', 'SETUPVAL', 'CLOSEUPVALS']);

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

// `CALL R<a> <n> <m>` prints B-1 and C-1 (T2-ADAPTER step 3): n arguments R<a+1..a+n> after the callee R<a> and m
// results written from R<a>. A count of -1 is the open protocol (T2-ADAPTER step 4), returned as null: n = -1 takes
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

// `GETUPVAL R<a> <u>`, `SETUPVAL R<a> <u>` and `CAPTURE UPVAL U<u>` name upvalue u; a Luau function has at most 200.
function upvalueIndex(text, site) {
  if (!/^\d+$/.test(text ?? '')) refuseAt(site, 'operand_form', 'invalid upvalue operand');
  const value = Number(text);
  if (!(value < 200)) refuseAt(site, 'operand_form', 'upvalue outside Luau upvalue range');
  return value;
}

// The opcode, operand text and site of a listing record, its label removed; null for a constant or a label alone.
function instructionOf(record) {
  const match = /^(?:L\d+:\s*)?([A-Z][A-Z0-9_]*)(?:\s+(.*))?$/.exec(record.line);
  return match ? { op: match[1], rest: match[2] ?? '', site: { line_number: record.line_number, op: match[1] } } : null;
}

// The well-formed `NEWCLOSURE R<a> P<k>` lines of a function body with their k (`prototype`); a malformed one is left
// to the parse, which refuses it.
function closureSites(records) {
  return records.map(instructionOf).filter((entry) => entry?.op === 'NEWCLOSURE').flatMap(({ rest, site }) => {
    const args = operands(rest, OPERAND_COUNTS.get('NEWCLOSURE'));
    return args && /^P\d+$/.test(args[1]) ? [{ ...site, prototype: Number(args[1].slice(1)) }] : [];
  });
}

// One function body: the selected function or a declared nested function. `upvalues` lists the classes ('value' |
// 'place') of the function's upvalues, as its creating closure record decided them; `childIds` maps the k of each
// `NEWCLOSURE R<a> P<k>` line of the body to the caller-declared index of the function it creates.
function parseFunction(records, { parameter_count, is_variadic, upvalues, childIds, optimization_level = null }) {
  const constants = new Map();
  const labels = new Map();
  const instructions = [];
  const usedUpvalues = new Set();
  // The adjacent-only open protocol (T2-ADAPTER step 4): an open producer leaves its values as a pack at R<p> and
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
  // An upvalue use names one of the upvalues the creating closure captured; its class is the closure's.
  const useUpvalue = (index, site) => {
    if (!(index < upvalues.length)) refuseAt(site, 'capture_count_mismatch', `upvalue ${index} is not captured by the creating closure`);
    usedUpvalues.add(index);
    return upvalues[index];
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
    // `_` admitted so FORGPREP_NEXT/FORGPREP_INEXT reach the typed unsupported_opcode refusal (D4).
    const match = /^([A-Z][A-Z0-9_]*)(?:\s+(.*))?$/.exec(line);
    if (!match) refuse('listing_structure', `unrecognized disassembly at line ${record.line_number}`, record.line_number);
    const op = match[1];
    const site = { line_number: record.line_number, op };
    const counts = OPERAND_COUNTS.get(op);
    if (!counts) refuse('unsupported_opcode', `unsupported opcode ${op} at disassembly line ${record.line_number}`, record.line_number, op);
    // `SETLIST R<a> R<b> <c> [<s>]`: the bracket is the start-index operand (T2-ADAPTER.md 3.4), kept as args[3].
    // `FORGLOOP R<a> L<x> <n>` takes no bracket; the -O1 ipairs marker ` [inext]` is refused, never ignored.
    if (op === 'FORGLOOP' && /\[inext\]\s*$/.test(match[2] ?? '')) {
      refuseAt(site, 'iteration_fast_path_unsupported', 'FORGLOOP [inext] is the -O1 ipairs fast path');
    }
    const args = (op === 'SETLIST' ? /^(\S+)\s+(\S+)\s+(\S+)\s+\[([^\]]*)\]$/.exec(match[2] ?? '')?.slice(1)
      : op === 'FORGLOOP' ? /^(\S+)\s+(\S+)\s+(\S+)$/.exec(match[2] ?? '')?.slice(1)
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
    } else if (op === 'AND' || op === 'OR') {
      // `AND R<a> R<b> R<c>` sets R<a> = R<b> when R<b> is falsy (nil or false), else R<c>; `OR` the reverse. A conditional
      // move (T4-ADAPTER-ANDOR-IMPORT-DUPTABLE): no metamethod, no error, no transfer. At -O0 the right operand is always a
      // register; the constant forms ANDK and ORK need -O1 constant folding and stay unsupported_opcode.
      instruction.kind = 'logical';
      instruction.operator = op === 'AND' ? 'and' : 'or';
      instruction.writes = [register(args[0], site)];
      instruction.reads = [register(args[1], site), register(args[2], site)];
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
      // `RETURN R<a> -1` (T2-ADAPTER step 4) returns R<a..p-1> and then the pack the previous instruction left at R<p>.
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
      // A named environment access (T2-ADAPTER step 2): the name is an identifier string constant read through
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
      // A call with fixed counts (T2-ADAPTER step 3): it reads the callee R<a> and the arguments R<a+1..a+n>,
      // writes the results R<a..a+m-1> and kills its frame from R<a+m> up (clobbers_from). Open counts (step 4):
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
      // A method call (T2-ADAPTER step 3): `NAMECALL R<a> R<b> K<k>` sets R<a+1> = R<b> and R<a> = R<b>[K<k>] for
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
      // Open counts as for CALL (step 4): the open arguments are R<a+2..p-1> (self is R<a+1>, so p >= a+2).
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
      // `GETVARARGS R<a> <n>` (T2-ADAPTER step 4) copies n of the function's varargs into R<a..a+n-1>; n = -1 leaves
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
      // `NEWTABLE R<a> <h> <n>` (T2-ADAPTER step 5): a fresh table in R<a>; the hash and array size hints are not kept.
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
    } else if (op === 'FORNPREP' || op === 'FORGPREP') {
      // `FORNPREP R<a> L<x>`: numeric loop state [limit R<a>, step R<a+1>, index R<a+2>], exit at L<x>.
      // `FORGPREP R<a> L<x>`: generic loop state [generator R<a>, state R<a+1>, control R<a+2>], first call at L<x>.
      // reads are the header's initial arguments in IR order: numeric (control, limit, step), generic (iterator, state, control).
      const base = register(args[0], site);
      if (!(base + 3 <= 255)) refuseAt(site, 'operand_form', 'invalid iteration base');
      instruction.kind = 'iteration_prepare';
      instruction.iteration = op === 'FORNPREP' ? 'numeric' : 'generic';
      instruction.base = base;
      instruction.label = args[1];
      instruction.reads = op === 'FORNPREP' ? [base + 2, base, base + 1] : [base, base + 1, base + 2];
    } else if (op === 'FORNLOOP' || op === 'FORGLOOP') {
      // The loop's latch; it reads only hidden state, which the IR carries as SSA values, so reads stay empty.
      const base = register(args[0], site);
      instruction.kind = 'iteration_loop';
      instruction.iteration = op === 'FORNLOOP' ? 'numeric' : 'generic';
      instruction.base = base;
      instruction.label = args[1];
      if (op === 'FORGLOOP') {
        if (!/^[1-9]\d*$/.test(args[2])) refuseAt(site, 'operand_form', 'invalid FORGLOOP variable count');
        instruction.variable_count = Number(args[2]);
        if (!(base + 3 + Math.max(instruction.variable_count, 2) <= 255)) refuseAt(site, 'operand_form', 'invalid FORGLOOP range');
      } else {
        if (!(base + 3 <= 255)) refuseAt(site, 'operand_form', 'invalid iteration base');
        instruction.variable_count = 1;
      }
    } else if (op === 'DUPTABLE') {
      // Decision D4: the template constant prints as `{...}`, so its keys are not in the listing (T2-ADAPTER.md 5.5 5c).
      // Without a caller-declared -O0 (`optimization_level: 0`) it stays refused: at -O1 the template carries constant
      // values the listing does not show, and the listing cannot prove its level. At a declared -O0 (PLAN-T6 Task T6.8,
      // T6-DUPTABLE-LOWERING, which amends PLAN-T4 decision D1 for declared -O0 listings only) the compiler stores every
      // template key right after the DUPTABLE, one `LOADK R<k> K<'key'>` + value + `SETTABLE R<v> R<t> R<k>` per record
      // field in source order, and the `REMARK allocation: table template N` line right before it names N. The window
      // (below) must be exactly those N stores; their keys become key_constant, so the bridge emits make_table_literal
      // with constant identifier keys, which the backend prints as record syntax and the compiler turns back into a
      // DUPTABLE of the same template. The stores only overwrite values of a template that already holds all N keys, so
      // the node layout, and with it the `next` order, depends on the key sequence alone, nil values included. The 174,
      // 169 and 67 of 400 key sets of the earlier reason measured a lowering with register or bracketed keys, which
      // recompiles to a hinted NEWTABLE; the record-key lowering differs from the original in none of them.
      if (optimization_level !== 0) refuseAt(site, 'table_template_opaque', 'DUPTABLE template keys are not in the listing');
      let remark = null;
      for (let back = position - 1; back >= 0 && records[back].line.startsWith('REMARK '); back -= 1) {
        remark ??= /^REMARK allocation: table template ([1-9]\d*)$/.exec(records[back].line);
      }
      if (!remark) refuseAt(site, 'table_template_opaque', 'DUPTABLE has no table template remark');
      if (!/^\d+$/.test(args[1]) || constants.get(Number(args[1])) !== '{...}') refuseAt(site, 'operand_form', 'DUPTABLE template constant is absent');
      instruction.kind = 'new_table';
      instruction.template_size = Number(remark[1]);
      instruction.writes = [register(args[0], site)];
    } else if (op === 'GETUPVAL') {
      // `GETUPVAL R<a> <u>`: R<a> = upvalue u (a value capture's value, or a read of a place capture).
      instruction.kind = 'upvalue_get';
      instruction.upvalue = upvalueIndex(args[1], site);
      instruction.upvalue_class = useUpvalue(instruction.upvalue, site);
      instruction.writes = [register(args[0], site)];
    } else if (op === 'SETUPVAL') {
      // `SETUPVAL R<a> <u>`: upvalue u = R<a>; only a by-reference (place) capture is ever written.
      instruction.kind = 'upvalue_set';
      instruction.upvalue = upvalueIndex(args[1], site);
      instruction.upvalue_class = useUpvalue(instruction.upvalue, site);
      if (instruction.upvalue_class !== 'place') refuseAt(site, 'setupval_on_value_capture', `SETUPVAL writes value capture ${instruction.upvalue}`);
      instruction.reads = [register(args[0], site)];
    } else if (op === 'NEWCLOSURE') {
      // `NEWCLOSURE R<a> P<k>` and the CAPTURE lines that follow it are ONE closure instruction (the NAMECALL + CALL
      // precedent). The VM writes R<a> before it reads the captures, so `CAPTURE VAL R<a>` captures the new closure
      // itself (a recursive local function): mode `self`, a place of its own in the bridge. The created function is the
      // one the caller declared for this P<k> (decision D1), never one derived from the function numbering.
      if (!/^P\d+$/.test(args[1])) refuseAt(site, 'operand_form', 'invalid prototype operand');
      const target = register(args[0], site);
      const child = childIds.get(Number(args[1].slice(1)));
      if (child === undefined) refuseAt(site, 'nested_function_undeclared', `NEWCLOSURE ${args[1]} has no declared nested function`);
      const captures = [];
      const lineNumbers = [record.line_number];
      while (/^(?:L\d+:\s*)?CAPTURE\b/.test(records[position + 1]?.line ?? '')) {
        position += 1;
        const captureRecord = records[position];
        const captureSite = { line_number: captureRecord.line_number, op: 'CAPTURE' };
        if (/^L\d+:/.test(captureRecord.line)) refuseAt(captureSite, 'label_inside_closure', 'label on a CAPTURE line');
        const form = /^CAPTURE\s+(VAL|REF|UPVAL)\s+(\S+)$/.exec(captureRecord.line);
        if (!form) refuseAt(captureSite, 'operand_form', 'CAPTURE: operand form');
        lineNumbers.push(captureRecord.line_number);
        if (form[1] === 'UPVAL') {
          if (!/^U\d+$/.test(form[2])) refuseAt(captureSite, 'operand_form', 'invalid upvalue operand');
          const index = upvalueIndex(form[2].slice(1), captureSite);
          const upvalueClass = useUpvalue(index, captureSite);
          captures.push({ mode: 'upvalue', upvalue: index, class: upvalueClass, line_number: captureRecord.line_number });
        } else {
          const captured = register(form[2], captureSite);
          const mode = form[1] === 'REF' ? 'reference' : captured === target ? 'self' : 'value';
          captures.push({ mode, register: captured, class: mode === 'value' ? 'value' : 'place', line_number: captureRecord.line_number });
        }
      }
      instruction.kind = 'closure';
      instruction.function = child;
      instruction.captures = captures;
      instruction.reads = captures.filter((capture) => capture.mode === 'value').map((capture) => capture.register);
      instruction.references = captures.filter((capture) => capture.mode === 'reference').map((capture) => capture.register);
      instruction.writes = [target];
      instruction.line_numbers = lineNumbers;
    } else if (op === 'CAPTURE') {
      refuseAt(site, 'capture_without_closure', 'CAPTURE outside a NEWCLOSURE');
    } else if (op === 'CLOSEUPVALS') {
      // `CLOSEUPVALS R<s>` detaches the open by-reference cells of R<s..>; nothing is lowered, and the reuse rule below
      // refuses every later access of such a register (the bridge keeps one place per register).
      instruction.kind = 'close_upvalues';
      instruction.from = register(args[0], site);
      // Transparent to the open protocol: `return f(x)` with a by-reference capture in scope compiles to the open
      // producer, CLOSEUPVALS, then the open RETURN (values, closeLocals(0), RETURN). The pending pack passes through an
      // unlabelled close; a label on the close would let another path reach the consumer without the pack.
      if (openPack && [...labels.values()].includes(instructions.length)) {
        refuseAt(site, 'open_pack_crosses_label', 'open pack crosses a label');
      }
    } else {
      refuse('unsupported_opcode', `unsupported opcode ${op} at disassembly line ${record.line_number}`, record.line_number, op);
    }
    // A pack still pending here was not consumed by this instruction, the one right after its producer; an unlabelled
    // close_upvalues passes it on to the instruction after it.
    if (openPack && instruction.kind !== 'close_upvalues') refuseAt(openPack.site, 'open_pack_not_consumed', 'open pack is not consumed by the next instruction');
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
    // accepted only over a following LOADB onto a labelled instruction (T2-ADAPTER.skeptic.md D5).
    const skip = instruction.op === 'LOADB' && instruction.args.length === 3;
    if (skip && !(instruction.args[2] === '+1' && instructions[index + 1]?.op === 'LOADB' && labelled.has(index + 2))) {
      refuseAt(instruction, 'relative_skip_unsupported', `relative skip ${instruction.args[2]} is unsupported`);
    }
    // Bytecode successors of the iteration pair (FORNPREP: exit, body; FORGPREP: its FORGLOOP;
    // FORNLOOP/FORGLOOP: body, exit). The bridge does not lower these edges; it uses the loop record.
    const iterationSuccessors = instruction.kind === 'iteration_prepare'
      ? (instruction.iteration === 'numeric' ? [instruction.target, index + 1] : [instruction.target])
      : instruction.kind === 'iteration_loop' ? [instruction.target, index + 1] : null;
    instruction.successors = iterationSuccessors ?? (instruction.kind === 'return' ? []
      : instruction.kind === 'jump' ? [instruction.target]
        : instruction.kind === 'branch' ? [instruction.target, index + 1]
          : skip ? [index + 2] : [index + 1]);
    if (!instruction.successors.every((target) => target < instructions.length)) {
      refuseAt(instruction, 'listing_structure', 'function falls off end');
    }
  }
  // Iteration regions. A PREP at p pairs with the LOOP at l (numeric: the PREP's exit target is l+1;
  // generic: the PREP's target is l), the LOOP jumps back to p+1 with the same base. The region is (p, l]: entered only
  // from the PREP, left only to l+1 (returns aside); no member writes, clobbers or reads the hidden registers.
  for (const [p, prep] of instructions.entries()) {
    if (prep.kind !== 'iteration_prepare') continue;
    const l = prep.iteration === 'numeric' ? prep.target - 1 : prep.target;
    const latch = instructions[l];
    if (!(l > p && latch?.kind === 'iteration_loop' && latch.iteration === prep.iteration && latch.base === prep.base
      && latch.target === p + 1 && latch.loop === undefined)) {
      refuseAt(prep, 'iteration_pair_mismatch', `${prep.op} R${prep.base} has no matching loop instruction`);
    }
    const a = prep.base;
    const hiddenReads = prep.iteration === 'numeric' ? [a, a + 1] : [a, a + 1, a + 2];
    for (let index = p + 1; index < l; index += 1) {
      const member = instructions[index];
      if (member.writes.some((reg) => reg >= a && reg <= a + 2) || (member.clobbers_from ?? Infinity) <= a + 2) {
        refuseAt(member, 'iteration_state_written', `loop state R${a}..R${a + 2} written inside its loop`);
      }
      if (member.reads.some((reg) => hiddenReads.includes(reg))) {
        refuseAt(member, 'iteration_state_read', `hidden loop state of R${a} read inside its loop`);
      }
    }
    for (const [index, instruction] of instructions.entries()) {
      const inside = index > p && index <= l;
      for (const target of instruction.successors) {
        const into = target > p && target <= l;
        if (!inside && into && index !== p) refuseAt(instruction, 'iteration_region_entry', 'jump into a loop body');
        if (inside && !into && target !== l + 1) refuseAt(instruction, 'iteration_region_exit', 'jump out of a loop body');
      }
    }
    const variables = prep.iteration === 'numeric' ? [a + 2]
      : Array.from({ length: latch.variable_count }, (_, i) => a + 3 + i);
    const loop = { iteration: prep.iteration, base: a, prepare: p, latch: l, exit: l + 1, variables };
    prep.loop = loop;
    latch.loop = loop;
    // Per-edge definite assignment: the body edges define the loop variables (a generic LOOP is a call frame at a+3);
    // every exit edge kills the loop's registers R<a..> (the compiler frees them at the loop's end).
    const bodyEdge = prep.iteration === 'numeric' ? { writes: variables } : { kills_from: a + 3, writes: variables };
    if (prep.iteration === 'numeric') prep.edge_effects = [{ kills_from: a }, bodyEdge];
    latch.edge_effects = [bodyEdge, { kills_from: a }];
  }
  for (const instruction of instructions) {
    if (instruction.kind === 'iteration_loop' && instruction.loop === undefined) {
      refuseAt(instruction, 'iteration_pair_mismatch', `${instruction.op} R${instruction.base} has no matching prepare instruction`);
    }
  }
  // Constructor windows (T2-ADAPTER.md 5.5 5b). A `NEWTABLE R<t>` opens a window when a `SETLIST R<t>` follows: the
  // window runs to the last store into R<t> (SETLIST, SETTABLE/SETTABLEKS with table R<t>) before the first instruction
  // that reads or writes R<t> in any other way (a call frame that kills R<t> included), carries a label, or jumps,
  // branches or returns (a LOADB skip included). The NEWTABLE and every member carry `constructor`, the last member also
  // `complete`; a member reads only its key and value registers, never R<t>. Field order is the listing's store order,
  // which at -O0 is source order (T2-ADAPTER.md 2.7).
  const storeRegisters = (store) => (store.kind === 'set_list' ? store.values
    : [...(store.key === undefined ? [] : [store.key]), store.value]);
  // T6.8 (T6-DUPTABLE-LOWERING): a DUPTABLE window holds exactly N members, each a -O0 record store: SETTABLE whose key
  // register was last written inside the window by LOADK of a string that the backend prints as a record key (an identifier
  // and not a reserved word, src/luau_syntax.zig:3-7 and :74-79), the last member included.
  const RESERVED = new Set(['and', 'break', 'do', 'else', 'elseif', 'end', 'false', 'for', 'function', 'if', 'in', 'local',
    'nil', 'not', 'or', 'repeat', 'return', 'then', 'true', 'until', 'while']);
  const recordStores = (create, template, members) => {
    if (members.length !== template) {
      refuseAt(instructions[create], 'constructor_window_unsupported', `DUPTABLE template of ${template} fields has ${members.length} stores in its window`);
    }
    for (const index of members) {
      const member = instructions[index];
      let writer = null;
      for (let at = index - 1; at > create && writer === null; at -= 1) {
        if (instructions[at].writes.includes(member.key) || (instructions[at].clobbers_from ?? Infinity) <= member.key) writer = instructions[at];
      }
      if (!(member.op === 'SETTABLE' && writer?.op === 'LOADK' && typeof writer.value.string === 'string')) {
        refuseAt(member, 'constructor_window_unsupported', 'DUPTABLE member is not a record field store');
      }
      if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(writer.value.string) || RESERVED.has(writer.value.string)) {
        refuseAt(member, 'non_identifier_name', 'DUPTABLE member key is not a record name');
      }
    }
    // T6.8 (T6-DUPTABLE-LOWERING, Step B): the window is closed. (a) Every transfer inside goes forward and lands at or before the next member,
    // so each member lies on every path from the create. (b) Nothing outside (create, last] jumps into it. (c) Nothing
    // jumps past a member's key load into the stretch up to that member.
    const last = members[members.length - 1];
    for (let index = create + 1; index < last; index += 1) {
      const bound = members.find((member) => member > index);
      if (!instructions[index].successors.every((target) => target > index && target <= bound)) {
        refuseAt(instructions[index], 'constructor_window_unsupported', 'transfer leaves the DUPTABLE window or passes a member');
      }
    }
    for (const [index, other] of instructions.entries()) {
      if (index >= create && index <= last) continue;
      if (other.successors.some((target) => target > create && target <= last)) {
        refuseAt(other, 'constructor_window_unsupported', 'transfer enters a DUPTABLE window');
      }
    }
    for (const index of members) {
      const { key } = instructions[index];
      let load = index - 1;
      while (!(instructions[load].writes.includes(key) || (instructions[load].clobbers_from ?? Infinity) <= key)) load -= 1;
      for (let at = create + 1; at < load; at += 1) {
        if (instructions[at].successors.some((target) => target > load && target <= index)) {
          refuseAt(instructions[at], 'constructor_window_unsupported', 'transfer passes the key load of a DUPTABLE member');
        }
      }
    }
  };
  for (const [create, table] of instructions.entries()) {
    if (table.kind !== 'new_table') continue;
    const [t] = table.writes;
    const members = [];
    const template = table.template_size; // DUPTABLE windows only
    for (let index = create + 1; index < instructions.length; index += 1) {
      const instruction = instructions[index];
      const transfers = ['jump', 'branch', 'return', 'iteration_prepare', 'iteration_loop'].includes(instruction.kind)
        || instruction.successors[0] !== index + 1;
      // T6.8 (Step B): a template window may hold labels and forward transfers (checked by recordStores); a return or an
      // iteration instruction still ends it.
      if (template === undefined ? (labelled.has(index) || transfers)
        : ['return', 'iteration_prepare', 'iteration_loop'].includes(instruction.kind)) break;
      const store = (instruction.kind === 'set_list' || instruction.kind === 'table_set') && instruction.table === t;
      const touched = store ? storeRegisters(instruction)
        : [...instruction.reads, ...instruction.writes, ...(instruction.references ?? [])];
      if (touched.includes(t) || (instruction.clobbers_from ?? Infinity) <= t) break;
      if (store) members.push(index);
      if (template !== undefined && members.length === template) break; // exactly its N stores
    }
    if (template !== undefined) recordStores(create, template, members);
    else if (!members.some((index) => instructions[index].kind === 'set_list')) continue;
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
    // A SETTABLE member whose key register was last written inside the window by LOADK of a string keeps that string as
    // its key (T4-ADAPTER-ANDOR-IMPORT-DUPTABLE, skeptic objection 2): `key_constant` and no `key`, as for SETTABLEKS, so the
    // bridge emits a constant key and the member reads only its value. The scan is definitelyValidKey's: the last writer
    // after the NEWTABLE, a clobbering call ends it.
    for (const index of members) {
      const member = instructions[index];
      if (member.kind !== 'table_set' || !Object.hasOwn(member, 'key')) continue;
      for (let at = index - 1; at > create; at -= 1) {
        const writer = instructions[at];
        if (writer.writes.includes(member.key) || (writer.clobbers_from ?? Infinity) <= member.key) {
          if (writer.op === 'LOADK' && typeof writer.value.string === 'string') {
            member.key_constant = { string: writer.value.string };
            delete member.key;
          }
          break;
        }
      }
    }
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
  // Reuse rule (closures): the bridge binds a by-reference capture to the register's one place, so after a
  // `CLOSEUPVALS R<s>` no instruction reachable from it (back edges included) may read, write or capture a register
  // x >= s that is captured by reference anywhere in the function; only a RETURN right after the close may read it
  // (the compiler's `return` computes its values, closes, then returns). Per-iteration or reused cells stay refused.
  const byReference = new Set(instructions.flatMap((instruction) => instruction.references ?? []));
  for (const [index, close] of instructions.entries()) {
    if (close.kind !== 'close_upvalues') continue;
    const detached = [...byReference].filter((reg) => reg >= close.from);
    if (detached.length === 0) continue;
    const seen = new Set();
    const pending = [...close.successors];
    while (pending.length) {
      const at = pending.pop();
      if (seen.has(at)) continue;
      seen.add(at);
      const reached = instructions[at];
      const exitRead = at === index + 1 && reached.kind === 'return';
      const touched = [...(exitRead ? [] : reached.reads), ...reached.writes, ...(reached.references ?? [])];
      const hit = detached.find((reg) => touched.includes(reg));
      if (hit !== undefined) {
        refuseAt(reached, 'captured_register_reused_after_close',
          `R${hit} is used after CLOSEUPVALS R${close.from} (line ${close.line_number}) detached its by-reference capture`);
      }
      pending.push(...reached.successors);
    }
  }
  // Self rule (closures): in the VM a self capture is a value taken at each creation, but the bridge models it as one
  // place of the creating function (closure_self_<i>) that every creation overwrites (skeptic objection B), so a
  // NEWCLOSURE with a `self` capture must not lie on a cycle; refused until each creation can have a place of its own
  // (an instruction-origin place, which the frozen dispatcher hoists).
  for (const [index, closure] of instructions.entries()) {
    if (closure.kind !== 'closure' || !closure.captures.some((capture) => capture.mode === 'self')) continue;
    const seen = new Set();
    const pending = [...closure.successors];
    while (pending.length) {
      const at = pending.pop();
      if (at === index) refuseAt(closure, 'self_capture_in_loop', 'a closure that captures itself is created inside a loop');
      if (seen.has(at)) continue;
      seen.add(at);
      pending.push(...instructions[at].successors);
    }
  }
  const registers = [...new Set([
    ...Array.from({ length: parameter_count }, (_, i) => i),
    ...instructions.flatMap((instruction) => [...instruction.reads, ...instruction.writes, ...(instruction.references ?? []),
      ...(instruction.edge_effects ?? []).flatMap((effect) => effect.writes ?? [])]),
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
    for (const [slot, target] of instructions[index].successors.entries()) predecessors[target].push([index, slot]);
  }
  // An edge's set is its source's outgoing set with the edge's own effect (iteration edges only).
  const edgeOut = (parent, slot) => {
    const effect = instructions[parent].edge_effects?.[slot];
    if (!effect) return outgoing[parent];
    return new Set([...[...outgoing[parent]].filter((reg) => reg < (effect.kills_from ?? Infinity)), ...(effect.writes ?? [])]);
  };
  const initial = new Set(Array.from({ length: parameter_count }, (_, i) => i));
  const incoming = instructions.map(() => new Set(registers));
  const outgoing = instructions.map(() => new Set(registers));
  let changed = true;
  while (changed) {
    changed = false;
    for (const index of reachable) {
      const sources = predecessors[index].map(([parent, slot]) => edgeOut(parent, slot));
      if (index === 0) sources.push(initial);
      const next = new Set(registers.filter((reg) => sources.every((source) => source.has(reg))));
      // A call kills its frame (T2-ADAPTER.md 5.3): outgoing = (incoming - {r >= clobbers_from}) + writes.
      const clobbers = instructions[index].clobbers_from ?? Infinity;
      const after = new Set([...[...next].filter((reg) => reg < clobbers), ...instructions[index].writes]);
      if (next.size !== incoming[index].size || after.size !== outgoing[index].size) changed = true;
      incoming[index] = next;
      outgoing[index] = after;
    }
  }
  for (const index of reachable) {
    const instruction = instructions[index];
    // A by-reference capture is a use of the register too, except of the closure's own target, which the closure
    // itself initializes.
    const referenced = (instruction.references ?? []).filter((reg) => reg !== instruction.writes[0]);
    for (const reg of [...instruction.reads, ...referenced]) {
      if (!incoming[index].has(reg)) {
        refuse('uninitialized_register', `uninitialized R${reg} at disassembly line ${instruction.line_number}`,
          instruction.line_number, instruction.op);
      }
    }
  }
  return { registers, instructions, usedUpvalues };
}

// The shape of the `nested` option: { "<function index>": { parent, prototype, parameter_count, is_variadic } }.
function nestedDeclarations(nested) {
  const invalid = (message) => refuse('invalid_options', message);
  const isRecord = (value) => typeof value === 'object' && value !== null && !Array.isArray(value);
  if (!isRecord(nested)) invalid('nested must map function indices to declarations');
  return Object.entries(nested).map(([key, entry]) => {
    if (!/^(?:0|[1-9]\d*)$/.test(key)) invalid(`nested key ${key} is not a function index`);
    if (!isRecord(entry)) invalid(`nested function ${key} must be a declaration`);
    const { parent, prototype, parameter_count, is_variadic = false } = entry;
    if (!(Number.isInteger(parent) && parent >= 0)) invalid(`nested function ${key}: parent must be a non-negative integer`);
    if (!(Number.isInteger(prototype) && prototype >= 0)) invalid(`nested function ${key}: prototype must be a non-negative integer`);
    if (!(Number.isInteger(parameter_count) && parameter_count >= 0 && parameter_count < 255)) {
      invalid(`nested function ${key}: parameter_count must be an integer from 0 to 254`);
    }
    if (typeof is_variadic !== 'boolean') invalid(`nested function ${key}: is_variadic must be a boolean`);
    return { index: Number(key), parent, prototype, parameter_count, is_variadic };
  }).sort((a, b) => a.index - b.index);
}

// The compiler owns bytecode decoding. This adapter accepts its pinned text
// format, not arbitrary binary bytecode or original source ASTs.
export function parseDisassembly(text, { function_index = 0, parameter_count = 2, is_variadic = false, nested = {},
  optimization_level = null } = {}) {
  if (!(Number.isInteger(function_index) && function_index >= 0)) {
    refuse('invalid_options', 'function_index must be a non-negative integer');
  }
  if (!(Number.isInteger(parameter_count) && parameter_count >= 0 && parameter_count < 255)) {
    refuse('invalid_options', 'parameter_count must be an integer from 0 to 254');
  }
  if (typeof is_variadic !== 'boolean') refuse('invalid_options', 'is_variadic must be a boolean');
  // T6.8 (T6-DUPTABLE-LOWERING): the compiler level that produced the listing, declared by the caller as
  // parameter_count is; the listing cannot prove it (T4-ADAPTER-ANDOR-IMPORT-DUPTABLE.md 3.1, its skeptic 1.9).
  if (!(optimization_level === null || optimization_level === 0)) refuse('invalid_options', 'optimization_level must be 0 or omitted');
  const declared = nestedDeclarations(nested);
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
  const records = functions.get(function_index);
  const closures = records.some((record) => CLOSURE_OPCODES.has(instructionOf(record)?.op));
  const childIds = (parent) => new Map(declared.filter((entry) => entry.parent === parent)
    .map((entry) => [entry.prototype, entry.index]));
  if (closures) {
    // The census (skeptic objection A): every function but the main chunk is created by exactly one NEWCLOSURE line.
    // A function after an always-terminating statement keeps its number but gets no NEWCLOSURE line, the text does not
    // mark it, and a declared map could then bind a live NEWCLOSURE line to its body; so the whole listing is refused,
    // without naming a function, since the text cannot tell which one is never instantiated.
    const creations = [...functions.values()].flat().filter((record) => instructionOf(record)?.op === 'NEWCLOSURE').length;
    if (creations !== functions.size - 1) {
      refuse('uninstantiated_function', `${creations} NEWCLOSURE lines for ${functions.size} functions: every function but the main chunk must be created by exactly one, and the listing cannot tell which one is not`);
    }
    // The selected function is lifted under a synthetic module that binds nothing, so it must capture nothing.
    for (const record of records) {
      const entry = instructionOf(record);
      const upvalue = entry?.op === 'GETUPVAL' || entry?.op === 'SETUPVAL' ? operands(entry.rest, [2])?.[1]
        : entry?.op === 'CAPTURE' ? /^UPVAL\s+U(\d+)$/.exec(entry.rest)?.[1] : undefined;
      if (upvalue !== undefined) {
        refuseAt(entry.site, 'selected_function_captures',
          `the selected function captures upvalue ${upvalueIndex(upvalue, entry.site)}; it is lifted under a synthetic module and must capture nothing`);
      }
    }
    // The declared map against the listing: each declared function exists, is not the selected function, hangs below the
    // selected function through declared parents, and is created by exactly one `NEWCLOSURE R<a> P<prototype>` line of
    // its parent, which no other declaration names.
    const mismatch = (message) => refuse('nested_map_mismatch', message);
    for (const entry of declared) {
      if (entry.index === function_index) mismatch(`nested function ${entry.index} is the selected function`);
      if (!functions.has(entry.index)) mismatch(`nested function ${entry.index} is absent from the listing`);
    }
    const lifted = new Set([function_index]);
    for (let grown = true; grown;) {
      grown = false;
      for (const entry of declared) {
        if (!lifted.has(entry.index) && lifted.has(entry.parent)) {
          lifted.add(entry.index);
          grown = true;
        }
      }
    }
    const closureLines = new Map([...lifted].map((index) => [index, closureSites(functions.get(index))]));
    for (const entry of declared) {
      if (!lifted.has(entry.index)) mismatch(`nested function ${entry.index}: its parent ${entry.parent} is not lifted`);
      const lines = closureLines.get(entry.parent).filter((site) => site.prototype === entry.prototype);
      if (lines.length !== 1) {
        mismatch(`nested function ${entry.index}: function ${entry.parent} has ${lines.length} NEWCLOSURE lines with P${entry.prototype}, not one`);
      }
      const twin = declared.find((other) => other !== entry && other.parent === entry.parent && other.prototype === entry.prototype);
      if (twin) mismatch(`nested functions ${entry.index} and ${twin.index} share parent ${entry.parent} and prototype P${entry.prototype}`);
    }
    // Every NEWCLOSURE line of a lifted function creates a declared function.
    for (const [index, sites] of closureLines) {
      for (const site of sites) {
        if (!childIds(index).has(site.prototype)) {
          refuseAt(site, 'nested_function_undeclared', `NEWCLOSURE P${site.prototype} of function ${index} has no declared nested function`);
        }
      }
    }
  }
  const selected = parseFunction(records, { parameter_count, is_variadic, upvalues: [], childIds: childIds(function_index), optimization_level });
  const result = {
    schema_version: 'compiler_disassembly_handoff_v2',
    listing_sha256: createHash('sha256').update(text).digest('hex'),
    function_index, parameter_count, is_variadic, registers: selected.registers, instructions: selected.instructions,
    signature_origin: 'caller-declared; text disassembly does not encode arity',
    scope: 'selected capture-free function; remaining compiled functions are not lifted',
  };
  if (!closures) return result;
  // The declared tree in pre-order, children by prototype; each function's upvalue classes come from its creating
  // closure record.
  const nestedFunctions = [];
  const visit = (parentIndex, parentInstructions) => {
    for (const entry of declared.filter((candidate) => candidate.parent === parentIndex).sort((a, b) => a.prototype - b.prototype)) {
      const closure = parentInstructions.find((instruction) => instruction.kind === 'closure' && instruction.function === entry.index);
      const upvalues = closure.captures.map((capture) => capture.class);
      const body = parseFunction(functions.get(entry.index), {
        parameter_count: entry.parameter_count, is_variadic: entry.is_variadic, upvalues, childIds: childIds(entry.index),
        optimization_level,
      });
      // The compiler captures exactly the upvalues a function references, in first-reference order.
      if (body.usedUpvalues.size !== upvalues.length) {
        refuse('capture_count_mismatch', `nested function ${entry.index} references ${body.usedUpvalues.size} upvalues but its closure captures ${upvalues.length} at disassembly line ${closure.line_number}`);
      }
      nestedFunctions.push({
        function_index: entry.index, parent_index: parentIndex, parameter_count: entry.parameter_count,
        is_variadic: entry.is_variadic,
        upvalues: closure.captures.map(({ class: upvalueClass, line_number }) => ({ class: upvalueClass, line_number })),
        registers: body.registers, instructions: body.instructions,
      });
      visit(entry.index, body.instructions);
    }
  };
  visit(function_index, selected.instructions);
  return {
    ...result,
    schema_version: 'compiler_disassembly_handoff_v3',
    functions: nestedFunctions,
    signature_origin: 'caller-declared for the selected function and every nested function; text disassembly does not encode arity',
    scope: 'selected function and its nested closures; the selected function captures nothing; remaining compiled functions are not lifted',
  };
}
