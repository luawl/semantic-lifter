# Semantic Lifter

This directory is the standalone rich-IR to readable-Luau package.

## Layout

- `src/` - durable Zig IR, validation, solving, restructuring, emission, and CLI.
- `luau/` - maintained Luau frontend, codec, oracle, and conformance modules.

Generated state (Zig caches and build output) is not part of the package contract.

## Research Manuscript

The active paper is
*Semantic-Lifter: An Evidence-Preserving Architecture for Defensive Luau Analysis*.
Its research plan separates the implemented proof of concept from remaining
empirical submission gates. The manuscript and its plan are kept outside this
repository.

## Build

Build with the wrapper from this directory:

```powershell
.\build.ps1 -Doptimize=ReleaseFast
.\build.ps1 test -Doptimize=ReleaseFast
.\build.ps1 -Dz3=true -Doptimize=ReleaseFast
```

The normal executable is written to
`zig-out/bin/semantic-lifter.exe` by default. The wrapper accepts the same
arguments as `zig build` after the script name. The build graph resolves its
external Luau tools from the package root, so the working directory does not
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
