# Semantic Lifter

This directory is the standalone rich-IR to readable-Luau package.

## Layout

- `src/` - durable Zig IR, validation, solving, restructuring, emission, and CLI.
- `luau/` - maintained Luau frontend, codec, oracle, and conformance modules.
- `testdata/` - checked-in IR and source fixtures.
- `showcase/` - bounded demonstrations and their documentation.
- `tmp/build/` - active Zig caches and installed build output.
- `tmp/archive/` - preserved historical caches, binaries, logs, and old probes.

Generated state belongs under `tmp/`; it is not part of the package contract.

## Research Manuscript

The active paper is
[Semantic-Lifter: An Evidence-Preserving Architecture for Defensive Luau Analysis](LUAU_EXECUTOR_DEOBFUSCATION_RESEARCH_ARTICLE_VENUE_READY.md).
Its [research plan](LUAU_EXECUTOR_DEOBFUSCATION_RESEARCH_PLAN.md) separates the
implemented proof of concept from remaining empirical submission gates.
The earlier detailed evidence ledger is preserved as
`research/archive/manuscripts/LUAU_EXECUTOR_DEOBFUSCATION_RESEARCH_ARTICLE_EVIDENCE_LEDGER_2026-10-07.md`;
it is not a second submission. The current revision is Markdown-only, with
artifact packaging deferred.

## Build

Run the wrapper from this directory so both Zig cache roots and test temporary
directories stay under `tmp/build`:

```powershell
.\build.ps1 -Doptimize=ReleaseFast
.\build.ps1 test -Doptimize=ReleaseFast
.\build.ps1 -Dz3=true -Doptimize=ReleaseFast
```

The normal executable is written to
`tmp/build/zig-out/bin/semantic-lifter.exe`. The wrapper accepts the same
arguments as `zig build` after the script name. The build graph resolves its
external Luau tools from the package root, so running from `tmp/build` does not
change those paths.

## Conformance

Run the package-owned fixture, compiler, and runtime-oracle checks with:

```powershell
.\build.ps1 conformance -Doptimize=ReleaseFast
```

Three optional whole-program checks use sample files from the parent workspace,
not package-owned inputs. Enable them only when those workspace samples are
available:

```powershell
.\build.ps1 conformance -Dworkspace-sample-conformance=true -Doptimize=ReleaseFast
```

Do not add frontend-, family-, sample-, or source-path-specific behavior to
`src/`. Target recovery belongs under its target analysis directory and must
finish before admission to `lifter_ir_v1`.
