# trust-wp

A deductive verifier for Rust. Write Creusot-compatible contracts —
`#[requires]`, `#[ensures]`, `#[invariant]`, `#[variant]`, `#[logic]`,
`proof_assert!`, `ghost!` — and trust-wp proves them by weakest-precondition
over the compiler's MIR, discharging obligations with the
[`ay`](https://github.com/alabsystems/ay) solver. Every machine-integer
overflow, division and index is an obligation, not an assumption. A proof is
credited only when `ay` produces a checked certificate; anything less is
reported as unknown, never as verified.

**Author:** Andrew Yates · **License:** Apache-2.0 · version: `Cargo.toml`

## Use

```
trust-wp FILE.rs          # verify one file, no Cargo project
trust-wp                  # verify the crate in the current directory
targo trust-wp            # the same, as a targo subcommand
trust-wp example          # write a sample file
trust-wp doctor           # report readiness
```

Exit codes: `0` verified · `1` counterexample · `2` refusal, encoding gap, or
nothing proved · `3` parse or CLI error · `101` internal. A run that examines
no obligation exits `2`. Unknown options are refused. `demo/run.sh` walks the
CLI and asserts these codes.

## Build

Requires the Trust toolchain (`rust-toolchain.toml` pins the channel; install
[aterm](https://github.com/alabsystems/aterm#install) and atpkg installs Trust)
and a sibling `../ay` checkout (`Cargo.toml` path dependencies). Only
`trust-wp-driver` links `rustc_private`; `scripts/trustc-private-wrapper.sh`
supplies the private sysroot without mutating the toolchain.

```
targo --unverified build -p trust-wp-driver -p targo-trust-wp -p trust-wp-cli
targo --unverified test  -p trust-wp-driver --lib --bins
```

`targo` is the Trust toolchain's cargo; it refuses a build that names no lane.
`--unverified` builds with the Trust verification pass off (no proof claim);
`targo trust check` runs it.

## Layout

```
crates/
  trust-wp-driver/    rustc driver: MIR extraction, WP, contract discovery (bins trust-wp-driver, trust-wp-rustc)
  trust-wp-ay/        encoder to ay and the verify pipeline; certification and verdict gates
  trust-wp-core/      formula AST and contract parsing
  trust-wp-macros/    contract proc macros
  trust-wp-std/       specifications for the standard library
  trust-wp-cli/       the `trust-wp` binary
  cargo-trust-wp/     `targo trust-wp`
  creusot-contracts/, creusot-std/   Creusot-namespace shims over the above
  trust-wp-lib/       stable, rustc_private-free facade for external consumers
tests/creusot_compat/ the Creusot corpus harness (reference/creusot is the pinned oracle)
tests/adversarial/    programs that must be rejected; the suite is red when a known hole is open
docs/                 undated design documents only: GOAL, DIRECTION, DECISIONS, SOUNDNESS, and the design notes DIRECTION §8 is folding
```

## Status

The goal is a drop-in, strictly stronger replacement for Creusot with `ay` as
the only backend (`docs/GOAL.md`). The claim rests on trust-wp-std's
`#[trusted]` specifications, which trust-wp takes as axioms and does not prove.
Progress is measured by one function,
`scripts/compare_baselines.py::find_true_100_violations`, over a fresh corpus
run; results live beside the run, not here. The plan and the architectural
decisions taken on it are in `docs/DIRECTION.md` §10 and `docs/DECISIONS.md`.
