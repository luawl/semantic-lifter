# Development Roadmap

[Back to the README](../README.md)

Active milestones, upcoming constructs, and evidence work. Day-to-day tracking lives in the [issue tracker](https://github.com/luawl/semantic-lifter/issues).

## Active

- **Pack-tail truncation.** A value pack is truncated to the entries its consumer keeps.
- **Native `for` exit copy.** A native `for` loop's variable is copied out where the code after the loop reads it.
- **Hygiene removals.** Two removals of unused or superseded code.
- **Fused-loop-result refusal.** A loop result that is fused yet read after the loop is refused fail-closed rather than emitted.
- **Remaining read-order sites and multiple-assignment store order.** The source frontend's remaining evaluation-order read sites, and the order a multiple assignment writes its targets.
- **Solver soundness and coverage-filtered planning.** Two soundness fixes in the solver and a planning fix that views the applicable facts filtered by input coverage.
- **Rewrite-id canonicality.** A check that every control-flow rewrite carries a canonical identity.
- **Per-function layout for nested closures.** A per-function register layout for nested closures, with inherited flat-layout budgets.
- **Two-level publication gate.** Emitted output is published only when the official compiler accepts it at both the default and `-O0` levels.
- **Call-frame operand need.** Accounting for the registers a call frame's operands require.
- **Latch-tail split.** Splitting the tail of a loop latch.
- **Loops whose exits never return.** Structuring a loop all of whose exits never return.
- **Readability and fusion.** A group of readability and value-fusion improvements.
- **Ergonomics.** Richer diagnostics and a decision dump.
- **IR-level simplifier.** A general simplifier over the IR, starting with constant folding and boolean identities.

## Upcoming constructs

- Loops whose body always exits with `break`.

## Solver

- Building and testing the optional Z3 backend against the Z3 4.16.0 release ([#9](https://github.com/luawl/semantic-lifter/issues/9)).

## Evidence

- Publishing the run records and the evidence archive ([#10](https://github.com/luawl/semantic-lifter/issues/10)).

## Recently landed

- **Closure-store environment order.** A value stored into a closure's captured cell is no longer folded across a call, so an environment change the call may make is observed in order ([#37](https://github.com/luawl/semantic-lifter/issues/37), closed).
- **Dead-code use counts.** Eliminating an instruction subtracts only the operand uses it actually counted, so a value a removed branch referenced is not later emitted as an undeclared local ([#36](https://github.com/luawl/semantic-lifter/issues/36), closed).
- **Source read order.** In a binary expression the source frontend reads a register local where the compiled code reads it, after an effectful right operand, keeping Luau's evaluation order ([#35](https://github.com/luawl/semantic-lifter/issues/35), closed).
- **Chained nested `or` arms.** A compound short-circuit `or` arm, a chained nested one included, is split by the normalizer instead of being cloned ([#34](https://github.com/luawl/semantic-lifter/issues/34), closed).
- **Scope plan of fused generic `for` initializers.** Every operand of a fused generic `for` initializer is scoped to the loop header ([#29](https://github.com/luawl/semantic-lifter/issues/29), closed), and an initializer call moves onto the `for` line only where its evaluation order is kept ([#33](https://github.com/luawl/semantic-lifter/issues/33), closed).
- **Loop side exits under a transfer wrapper.** A side exit, shared exit or loop-control exit that would be written as a plain `break` inside a transfer wrapper falls back fail-closed ([#32](https://github.com/luawl/semantic-lifter/issues/32), closed).
- **Closures in dispatcher output.** Captured locals used across several blocks share one cell per execution, written as a holder with a fresh box each time the block that creates them runs ([#14](https://github.com/luawl/semantic-lifter/issues/14), closed).
- **More always-exiting loop bodies.** A `for` loop whose body breaks from inside a nested `if`, or may `return` instead of breaking, is now admitted.
- **Entry-block predecessor guard.** An edge into a function's entry block no longer counts as the entry's only predecessor, so it cannot decide the entry's values.
- **Jump budget of the dispatcher's flat root.** The forced dispatcher's whole-body back jump is budgeted like a structured loop's, so both layouts of a function are certified under one jump policy.
- **Paired host-call programs on the updated adapter.** Rerun under a fresh freeze on the disassembly adapter that now lowers table record templates: every program lifts through both frontends and agrees with the original on every recorded input.
- **Held-out test set.** Twenty new programs, written independently of the lifter and frozen before their first run, lifted through both frontends and checked against the originals.
