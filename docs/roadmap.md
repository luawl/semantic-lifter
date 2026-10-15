# Development Roadmap

[Back to the README](../README.md)

Active milestones, upcoming constructs, and evidence work. Day-to-day tracking lives in the [issue tracker](https://github.com/luawl/semantic-lifter/issues).

## Active

- **Held-out test set.** Twenty new programs, written independently of the lifter and frozen before their first run, lifted through both frontends and checked against the originals.

## Upcoming constructs

- Loops whose body always exits with `break`.

## Correctness

- Closures in dispatcher output: captured locals used across several blocks keep one shared cell ([#14](https://github.com/luawl/semantic-lifter/issues/14)).

## Solver

- Building and testing the optional Z3 backend against the Z3 4.16.0 release ([#9](https://github.com/luawl/semantic-lifter/issues/9)).

## Evidence

- Publishing the run records and the evidence archive ([#10](https://github.com/luawl/semantic-lifter/issues/10)).
