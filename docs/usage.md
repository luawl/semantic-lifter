# Using Semantic-Lifter

[Back to the README](../README.md)

## Requirements

- Zig 0.16.0 ([ziglang.org downloads](https://ziglang.org/download/)).
- Lune 0.10.4 ([lune-org/lune releases](https://github.com/lune-org/lune/releases)).
- The Luau 0.720 command-line tools `luau-compile`, `luau-ast` and `luau-analyze`
  ([luau-lang/luau releases, tag `0.720`](https://github.com/luau-lang/luau/releases/tag/0.720)).
- Node 24 ([nodejs.org](https://nodejs.org/)). Node is a build requirement: `zig build` resolves it
  like the four tools above, so every build command needs `node` on `PATH` or `-Dnode=<path>`, and
  `zig build test` runs the compiler-disassembly adapter's tests with it.
- Z3 4.16.0, optional ([Z3Prover/z3 releases](https://github.com/Z3Prover/z3/releases)):
  `-Dz3=true -Dz3-dir=<path>` (off by default) compiles the Z3 backend against the C API in `<path>`,
  an unpacked Z3 4.16.0 release for Windows x64 that holds `include/z3.h`, `bin/libz3.lib` and
  `bin/libz3.dll`; a relative `<path>` resolves against the repository root, and 61 tests compile
  only with it. Without `-Dz3-dir`, or when one of those files is missing, `zig build` stops at
  configure time with a message that names `-Dz3-dir`. A build against the Z3 4.16.0 release for
  Windows x64 is on record: with `-Dz3=true`, `zig build test` passes in Debug, ReleaseSafe and
  ReleaseFast. A Z3 build of `semantic-lifter.exe` loads `libz3.dll` when it starts and runs with
  `<path>/bin` on `PATH` (`zig build run` and `zig build test` add that entry themselves). Other
  platforms' Z3 archives are not wired.

## Build and test

The build section below verifies the backend and the source frontend (every unit test and conformance step passes, and a fresh clone builds with the documented tool options); its `test` step also runs the compiler-disassembly adapter's tests under Node.

Every `zig build` command resolves the five external tools (Lune, `luau-compile`, `luau-ast`,
`luau-analyze` and Node) before it runs any step, so each command below takes their paths. An option
can be left out when that tool is on `PATH` under its own name.

```sh
zig build test -Doptimize=ReleaseFast -Dlune=<path> -Dluau-compile=<path> -Dluau-ast=<path> -Dluau-analyze=<path> -Dnode=<path>
zig build conformance -Doptimize=ReleaseFast -Dlune=<path> -Dluau-compile=<path> -Dluau-ast=<path> -Dluau-analyze=<path> -Dnode=<path>
zig build -Doptimize=ReleaseFast -Dlune=<path> -Dluau-compile=<path> -Dluau-ast=<path> -Dluau-analyze=<path> -Dnode=<path>
```

`test` runs the Zig unit tests, the Luau frontend's tests and the compiler-disassembly adapter's
tests (`test-disassembly` runs the adapter's tests alone); `conformance` validates, emits, compiles
and runs the generic fixtures and audits; the install step (the last line) puts
`semantic-lifter.exe`, with the `proof-attest.exe` helper, under `zig-out/bin/`. `-Doptimize` also
takes `Debug` and `ReleaseSafe`.

On Windows, `build.ps1 <step> [zig build args]` runs the same build, for example
`pwsh -File build.ps1 test -Doptimize=ReleaseFast`. It uses the Zig toolchain under
`tools\zig-x86_64-windows-0.16.0\` when that directory exists and `zig` from `PATH` otherwise, runs
in the repository root, and adds each of the four tool options that the caller did not pass when it
finds that tool in the maintainers' workspace layout; Node comes from `PATH` unless `-Dnode` is passed. It never sets `--prefix` or the cache
directories; pass them as arguments when you need them. Every other argument, such as
`-Dz3=true -Dz3-dir=<path>`, reaches `zig build` unchanged, and a `-D` value that PowerShell splits
at a drive colon or at a dot is joined again.

With `--summary all`, `test` reports a `Build Summary` in which every step succeeded and
every test passed, and `conformance` one in which every step succeeded; a failing step is named in the step tree that follows the summary line.

## Command-line use

The command-line interface reads `lifter_ir_v1` JSON that a frontend produced. Run the frontends
from the repository root.

Source path (Luau source, parsed by `luau-ast`):

```sh
lune run luau/lift_source.luau <path to luau-ast> <path to luau-compile> <input.luau> <program-id> <program.ir.json>
```

The frontend compiles the source with that `luau-compile` and `--fflags=LuauIntegerType=false` before `luau-ast`
parses it, and refuses a source that does not compile: an `i`-suffixed integer literal, which has Luau's integer
type rather than the number type, as `unsupported_integer_literal` at the literal's zero-based line and column,
and any other compile error as `source_compile_refused`.

Compiler-disassembly path (the frontend reads the `luau-compile --text` listing, turns the function
that `function_index` selects into a handoff document, then into IR; the one-liner below runs the
compiler and the adapter in one step):

```sh
node --input-type=module -e "import { execFileSync } from 'node:child_process'; import { writeFileSync } from 'node:fs'; import { parseDisassembly } from './frontends/disassembly/compiler_disassembly_adapter.mjs'; const [compiler, source, out] = process.argv.slice(1); writeFileSync(out, JSON.stringify(parseDisassembly(execFileSync(compiler, ['--text', '--dump-constants', '-O0', '-g0', '--fflags=LuauIntegerType=false', source], { encoding: 'utf8' }), { function_index: 0, parameter_count: 2 })));" <path to luau-compile> <input.luau> <handoff.json>
lune run frontends/disassembly/lift_compiler_disassembly.luau <handoff.json> <program.ir.json> <program-id>
```

`function_index` selects the compiled function in the listing; the caller declares its signature,
`parameter_count` (default 2) and `is_variadic` (default `false`), which the text listing does not encode.
A caller may also declare the listing's level, `optimization_level: 0` for a `-O0` listing such as the
one-liner's (the only value the option takes); with that declaration a table record template
(`DUPTABLE`) is lowered to a literal constructor, and without it the template stays a typed refusal.

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
single IR entity applies), some followed by indented detail lines; by default stderr carries nothing
else (the internal stage traces print only in a `-Dtrace-normalize-phases=true` build). Exit status 0
means success; 1 means a refusal or an error such as a missing file or a bad argument, and the stderr
lines say which. A refused `resolve-*` command writes no output file. Running `semantic-lifter`
without arguments prints the usage text.

The usage text lists some commands under "diagnostic-only or unchecked (exit 0 is not a checked
publication)", among them `emit-admitted-readable-luau-raw`, `emit-readable-luau-strategy`,
`emit-function-probe` and `resolve-exact-control-ir`. Each skips admission or part of the checked
pipeline, and the usage text says which. Unlike `emit-luau`, these commands do not gate their own
output, so their output serves analysis, or a harness that gates it separately. In the preprint's paired tests, every file that `emit-readable-luau-strategy` emits must pass
`luau-compile` and `luau-ast` before it runs against the original under the official Luau VM.

## Example

The [Getting Started example](README.md#example) lifts a tracked fixture through the source path and shows the published output.

The output is what the backend published after the official compiler accepted it. The backend rebuilt
the loop from the control-flow graph in the IR, not from the source text, so the result is a structured
rendering of the program rather than a copy of it.
