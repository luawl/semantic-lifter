# Development Roadmap

[Back to the README](../README.md)

Active milestones, upcoming constructs, and evidence work. Day-to-day tracking lives in the [issue tracker](https://github.com/luawl/semantic-lifter/issues).

## Active

- **Loop side exits under a transfer wrapper.** A side exit, shared exit or loop-control exit that would be written as a plain `break` inside a transfer wrapper falls back fail-closed.
- **Scope plan of fused generic `for` initializers.** Every operand of a fused generic `for` initializer is scoped to the loop header (the `direct-locals-luau` scoping report, [#29](https://github.com/luawl/semantic-lifter/issues/29)), and an initializer call moves onto the `for` line only where its evaluation order is kept.
- **Chained nested `or` arms.** A compound short-circuit `or` arm, a chained nested one included, is split by the normalizer instead of being cloned.

## Upcoming constructs

- Loops whose body always exits with `break`.

## Solver

- Building and testing the optional Z3 backend against the Z3 4.16.0 release ([#9](https://github.com/luawl/semantic-lifter/issues/9)).

## Evidence

- Publishing the run records and the evidence archive ([#10](https://github.com/luawl/semantic-lifter/issues/10)).

## Recently landed

- **Closures in dispatcher output.** Captured locals used across several blocks share one cell per execution, written as a holder with a fresh box each time the block that creates them runs ([#14](https://github.com/luawl/semantic-lifter/issues/14), closed).
- **More always-exiting loop bodies.** A `for` loop whose body breaks from inside a nested `if`, or may `return` instead of breaking, is now admitted.
- **Entry-block predecessor guard.** An edge into a function's entry block no longer counts as the entry's only predecessor, so it cannot decide the entry's values.
- **Jump budget of the dispatcher's flat root.** The forced dispatcher's whole-body back jump is budgeted like a structured loop's, so both layouts of a function are certified under one jump policy.
- **Paired host-call programs on the updated adapter.** Rerun under a fresh freeze on the disassembly adapter that now lowers table record templates: every program lifts through both frontends and agrees with the original on every recorded input.
- **Held-out test set.** Twenty new programs, written independently of the lifter and frozen before their first run, lifted through both frontends and checked against the originals.
