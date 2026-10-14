# Contributing

## Fix protocol

1. Write the failing test first (a Zig `test` block, a conformance fixture, or for the compiler-disassembly adapter a `node:test` case in `frontends/disassembly/compiler_disassembly_adapter.test.mjs`) and run it to show that it fails for the reason you are fixing.
2. Make the minimal change that turns it green: no unrelated refactors, renames or reformatting.
3. Run `zig fmt` on every Zig file you touch; `zig fmt --check <file>` must pass.
4. Keep `zig build test` and `zig build conformance` green in ReleaseFast (`-Doptimize=ReleaseFast` plus the five tool options, see `README.md`; Node is among them because `zig build test` runs the adapter's tests); a change to `src/structure.zig`, `src/emit_luau.zig`, `src/proof_orchestrator.zig` or `src/irreducible_normalize.zig` must pass both steps in all three modes (`Debug`, `ReleaseSafe` and `ReleaseFast`).

## Scope of `src/`

No frontend-, family-, sample- or path-specific behaviour in `src/`. Target-specific recovery belongs in a frontend and must finish before the program is admitted as `lifter_ir_v1`.

## Line endings

The repository stores every file byte for byte: `.gitattributes` sets `* -text`, so Git converts no line endings, neither on `git add` nor on checkout. Byte-exact fixtures and hashes depend on this. Anyone creating a fork or mirror must have `.gitattributes` in place before the first `git add`.

## Licence

The project is licensed under the PolyForm Strict License 1.0.0 (`LICENSE`): noncommercial use only, and no distribution of changed or new works based on it. Contributions are accepted only together with the contributor's grant to the project of the rights needed to include them under this licence.
