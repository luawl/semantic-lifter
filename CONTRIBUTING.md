# Contributing

## Fix protocol

1. Write the failing test first (a Zig `test` block or a conformance fixture) and run it to show that it fails for the reason you are fixing.
2. Make the minimal change that turns it green: no unrelated refactors, renames or reformatting.
3. Run `zig fmt` on every Zig file you touch; `zig fmt --check <file>` must pass.
4. Keep `zig build test` and `zig build conformance` green in ReleaseFast (`-Doptimize=ReleaseFast` plus the four tool options, see `README.md`); a change to `src/structure.zig`, `src/emit_luau.zig`, `src/proof_orchestrator.zig` or `src/irreducible_normalize.zig` must pass both steps in all three modes (`Debug`, `ReleaseSafe` and `ReleaseFast`).

## Scope of `src/`

No frontend-, family-, sample- or path-specific behaviour in `src/`. Target-specific recovery belongs in a frontend and must finish before the program is admitted as `lifter_ir_v1`.

## Line endings

The repository stores every file byte for byte: `.gitattributes` sets `* -text`, so Git converts no line endings, neither on `git add` nor on checkout. Byte-exact fixtures and hashes depend on this. Anyone creating a fork or mirror must have `.gitattributes` in place before the first `git add`.

## Licence

The project is licensed under the MIT licence (`LICENSE`). Contributions are accepted under the same licence.
