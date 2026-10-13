# Semantic-Lifter

Semantic-Lifter lifts protected (obfuscated or virtualized) Luau to readable, verified Luau. A
frontend recovers the program as `lifter_ir_v1`, a typed intermediate representation; the backend
in this repository validates it, solves and restructures its control flow, and emits Luau that the
official Luau compiler must accept before the output is published.

The backend works under a typed evidence contract. Output is published only for a program that
passes an admission profile, `core` for the IR itself and `emission` for readable Luau output (named
`readable-luau` on the command line), and every refusal is a typed diagnostic: a code plus the index
of the IR entity it concerns. The design is tested on paired representations: the same program is
lifted once through the source path (the Luau parser's syntax tree) and once through the
compiler-disassembly path (the official compiler's text listing), and the results are compared under
the official Luau VM.

The preprint that describes the design is published separately and will be linked here.

## Repository contents

- `src/`: the backend (IR, validation, solving, restructuring, emission) and the command-line
  interface, `semantic-lifter`.
- `luau/`: the source frontend, the IR library and codec, and the conformance fixtures and audits.
- `research/compiler_disassembly_adapter.mjs` and `research/lift_compiler_disassembly.luau`: the
  compiler-disassembly frontend (`research/compiler_disassembly_adapter.test.mjs` tests the adapter).
- `build.zig` and `build.ps1`: the build graph and its Windows wrapper.
- `LICENSE`, `CONTRIBUTING.md` and `.gitattributes`.

Manuscripts, run records, evidence and test-data archives are published separately and are not in
this repository.

## Requirements

- Zig 0.16.0 ([ziglang.org downloads](https://ziglang.org/download/)).
- Lune 0.10.4 ([lune-org/lune releases](https://github.com/lune-org/lune/releases)).
- The Luau 0.720 command-line tools `luau-compile`, `luau-ast` and `luau-analyze`
  ([luau-lang/luau releases, tag `0.720`](https://github.com/luau-lang/luau/releases/tag/0.720)).
- Node 24, only for the disassembly adapter and its test
  (`node --test research/compiler_disassembly_adapter.test.mjs`).
- Z3, optional and maintainers-only for now: `-Dz3=true` (off by default) links the Z3 4.16.0 C API
  from a fixed location outside the repository that `build.zig` names; 61 tests compile only with it.

## Build and test

Every `zig build` command resolves the four external tools before it runs any step, so each command
below takes their paths. An option can be left out when that tool is on `PATH` under its own name.

```sh
zig build test -Doptimize=ReleaseFast -Dlune=<path> -Dluau-compile=<path> -Dluau-ast=<path> -Dluau-analyze=<path>
zig build conformance -Doptimize=ReleaseFast -Dlune=<path> -Dluau-compile=<path> -Dluau-ast=<path> -Dluau-analyze=<path>
zig build -Doptimize=ReleaseFast -Dlune=<path> -Dluau-compile=<path> -Dluau-ast=<path> -Dluau-analyze=<path>
```

`test` runs the Zig unit tests and the Luau frontend's tests; `conformance` validates, emits,
compiles and runs the generic fixtures and audits; the install step (the last line) puts `semantic-lifter.exe`, with the `proof-attest.exe`
helper, under `zig-out/bin/`. `-Doptimize` also takes `Debug` and `ReleaseSafe`.

On Windows, `build.ps1 <step> [zig build args]` runs the same build, for example
`pwsh -File build.ps1 test -Doptimize=ReleaseFast`. It uses the Zig toolchain under
`tools\zig-x86_64-windows-0.16.0\` when that directory exists and `zig` from `PATH` otherwise, runs
in the repository root, and adds each of the four tool options that the caller did not pass when it
finds that tool in the maintainers' workspace layout. It never sets `--prefix` or the cache
directories; pass them as arguments when you need them.

Expected results on the maintainers' machine (ReleaseFast, with `--summary all`): `test` ends with
`Build Summary: 46/46 steps succeeded; 828/828 tests passed` (828 unit tests) and `conformance` with
`Build Summary: 489/489 steps succeeded` (489 conformance steps).

## Command-line use

The command-line interface reads `lifter_ir_v1` JSON that a frontend produced. Run the frontends
from the repository root.

Source path (Luau source, parsed by `luau-ast`):

```sh
lune run luau/lift_source.luau <path to luau-ast> <input.luau> <program-id> <program.ir.json>
```

Compiler-disassembly path (the `luau-compile --text` listing of one compiled function, turned into
a handoff document by the adapter, then into IR):

```sh
node --input-type=module -e "import { execFileSync } from 'node:child_process'; import { writeFileSync } from 'node:fs'; import { parseDisassembly } from './research/compiler_disassembly_adapter.mjs'; const [compiler, source, out] = process.argv.slice(1); writeFileSync(out, JSON.stringify(parseDisassembly(execFileSync(compiler, ['--text', '--dump-constants', '-O0', '-g0', source], { encoding: 'utf8' }), { function_index: 0, parameter_count: 2 })));" <path to luau-compile> <input.luau> <handoff.json>
lune run research/lift_compiler_disassembly.luau <handoff.json> <program.ir.json> <program-id>
```

`function_index` selects the compiled function in the listing, and `parameter_count` declares its
arity, which the text listing does not encode.

Then validate, resolve and emit:

```sh
semantic-lifter validate <program.ir.json> core
semantic-lifter resolve-admitted-readable-ir <program.ir.json> <admitted.ir.json>
semantic-lifter emit-luau <program.ir.json> <output.luau> standard-luau <path to luau-compile>
```

`validate` checks the IR against an admission profile (`core` or `readable-luau`).
`resolve-admitted-readable-ir` writes the resolved program that the emission profile admits.
`emit-luau` runs the checked pipeline on the frontend's IR and publishes the Luau output only after
the given `luau-compile` accepts it; `direct-locals-luau` is its other output form.

A refusal is reported on stderr as `diagnostic=<code> entity=<index>` lines (`entity=null` when no
single IR entity applies), some followed by indented detail lines. Exit status 0 means success and 1
a refusal; a `resolve-*` command can leave an output file behind on refusal, so check the exit
status. Running `semantic-lifter` without arguments prints the usage text.

Three commands are diagnostic-only: `emit-admitted-readable-luau-raw`, `emit-readable-luau-strategy`
and `resolve-exact-control-ir` skip admission or part of the checked pipeline (the usage text says
which) and exist for analysis, never for output you rely on. The usage text lists them, with
`emit-function-probe`, under "diagnostic-only or unchecked".

## Known limitations

These are the limits that the preprint reports:

- The compiler-disassembly frontend covers scalar programs only: 24 opcodes, no calls, globals or
  tables.
- 28 of 28 generated multi-entry rings fall back to the dispatcher form.
- There is no plan-level accounting check.
- The two raw protected inputs produced no handoff.
- Re-resolution is not idempotent.
- stderr carries untyped stage traces by default, next to the typed diagnostic lines.

The issue tracker holds the K-numbered items.

## Licence

MIT (`LICENSE`), copyright Luawl. Third-party: the modified Luraph-family frontend is not
redistributed.
