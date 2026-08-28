# trust-wp

**Prove your Rust code correct for every input — without running it.**

Write a contract. trust-wp reads the post-borrowck MIR, turns your code into a
verification condition with a Dijkstra-style weakest-precondition transform, and
discharges it on the `ay` SMT solver. When a contract does not hold, you get the
input that breaks it.

```console
$ trust-wp example > demo.rs && trust-wp demo.rs
✓ increment verified
✓ identity verified

2 verified, 0 failed, 0 errors
finished in 2.3s

$ sed -i '' 's/x + 1/x - 1/' demo.rs && trust-wp demo.rs
✗ increment FAILED (postcondition)
  return expression at demo.rs:20:5: 20:10
  violated ensures #0: (result > x)
  counterexample:
    result = 0
    x = 1
✓ identity verified

1 verified, 1 failed, 0 errors
```

No test wrote `x = 1`. The solver did, because it is the smallest input for
which `#[ensures(result > x)]` is false. That is the difference between testing
and proving: a passing run means *no such input exists*.

**What it is not.** This is a research verifier, not a product. It needs a
Trust-fork toolchain and the first-party `ay` solver to run — see Install. Some
contracts come back `unknown (proof-trusted)` rather than proved: the solver
reached UNSAT but the proof carried a step no checker could confirm, so the
verdict is withheld. That is a completeness gap — nothing is proved wrong — and
it is the honest failure mode to have. It is also predictable rather than
mysterious, which matters more: see below.

Most importantly: **arithmetic overflow is currently assumed, not proved.** The
`increment` above verifies, and at `x = i32::MAX` it overflows and panics —
`x > 0` does not exclude that input. MIR's overflow assertions enter the
verification condition as hypotheses rather than obligations, so a proof here
means "correct assuming no overflow", not "correct". Verify it yourself:

```console
$ printf 'use trust_wp::{ensures, requires};\n#[requires(x > 0)]\n#[ensures(result > x)]\npub fn f(x: i32) -> i32 { x + 1 }\n' > ovf.rs
$ trust-wp ovf.rs
✓ f verified
```

Closing that gap is the single most valuable contribution available here.

**Author:** Andrew Yates · **License:** Apache-2.0 · **Copyright:** 2026 Andrew Yates

## Install

There is no `cargo install` for this, and it would be dishonest to imply one.
trust-wp is a rustc driver: it links `rustc_private` and reads the compiler's
own post-borrowck MIR, so it must be built against the same compiler it drives
— and that compiler is a fork. Expect to build three things.

**1. The Trust toolchain.** A self-hosted rustc fork. Stock nightly will not
work: the driver reads internals whose shapes differ from upstream's, so it
does not merely fail to build, it would read the wrong thing. Build it, then
register it under the name `rust-toolchain.toml` asks for:

```sh
rustup toolchain link trust <trust-checkout>/build/host/stage2
rustup toolchain list | grep trust      # should print: trust
```

**2. The `ay` solver, as a sibling checkout.** trust-wp consumes it by path,
not by version — `ay-core = { path = "../ay/crates/ay-core" }` — so `ay` must
sit next to this repository and be checked out at a revision new enough for the
manifest. An older `ay` does not fail loudly; it demotes whole lanes to
`unknown (proof-trusted)`.

```
parent/
├── trust-wp/     <- this repository
└── ay/           <- github.com/alabsystems/ay
```

**3. trust-wp itself.**

```sh
cargo build --release -p trust-wp-cli                            # the `trust-wp` binary
cargo build --release -p trust-wp-driver --bin trust-wp-rustc    # engine, single-file mode
cargo build --release -p targo-trust-wp                          # engine, crate mode
cargo build --release -p trust-wp -p creusot-contracts           # the contract crates
```

Then ask the tool whether it believes you:

```console
$ trust-wp doctor
trust-wp 0.2.0+g58a37601 (https://github.com/alabsystems/trust-wp)

  checkout          /path/to/trust-wp
  trust-wp-rustc    .../target/release/trust-wp-rustc (via .../target/release)
  engine runtime    ok (driver loads and responds)
  targo-trust-wp    .../target/release/targo-trust-wp (via .../target/release)
  trust_wp          .../deps/libtrust_wp-<hash>.rlib
  creusot_contracts .../deps/libcreusot_contracts-<hash>.rlib
  cargo             cargo 1.99.0-dev
  active sysroot    .../build/aarch64-apple-darwin/stage2

ready. try:  trust-wp example > demo.rs && trust-wp demo.rs
```

`doctor` exits non-zero when it is not ready and names what is missing, so it
works as a setup check in a script. Only the `verify` path needs any of the
above: `contract`, `bundle` and `result` run entirely in-process and need
nothing but `trust-wp-cli`.

## How it works

Contracts are ordinary Rust attributes — `#[requires]`, `#[ensures]`,
`#[invariant]`, `#[variant]`, and `proof_assert!`. trust-wp works on
post-borrowck MIR rather than HIR, so what it proves is what the compiler
actually compiles, and it models `&mut` borrows with a
[RustHorn](https://doi.org/10.1145/3462205)-style (current, final) encoding. The
contract syntax is [Creusot](https://github.com/creusot-rs/creusot)-compatible;
`creusot_contracts` sources verify unchanged.

## Command line

`trust-wp` is the front door. It verifies one file or a whole crate, and its
exit code is the answer:

```
trust-wp <FILE.rs>       verify one file — no Cargo project needed
trust-wp                 verify the crate in the current directory
trust-wp example         write a small contracted file to start from
trust-wp doctor          report what is installed, and how to fix what is not
trust-wp completions     print a completion script for bash, zsh or fish
trust-wp man             print the roff manual page
```

`-h` is a summary and `--help` is the full page; `trust-wp help <COMMAND>`
covers one verb. `-q` prints only failures and the summary, and `--json` gives
one machine-readable document on stdout.

Nothing to configure on a first run:

```console
$ trust-wp example > demo.rs && trust-wp demo.rs
✓ increment verified
✓ identity verified

2 verified, 0 failed, 0 errors
finished in 1.4s
```

When a contract is false, the answer is the input that breaks it:

```console
$ trust-wp demo/02_counterexample.rs
✗ clamp FAILED (postcondition)
  return expression at demo/02_counterexample.rs:16:8: 16:14
  violated ensures #0: (result >= lo)
  counterexample:
    hi = -1
    lo = -1
    result = -2
    x = 0
```

| exit | meaning |
| --- | --- |
| `0` | everything verified |
| `1` | a contract was disproved — a counterexample exists |
| `2` | encoding/solver error, a soundness gap, **nothing was proved**, or the engine could not run |
| `3` | a contract failed to parse, or the command line was rejected |
| `101` | internal error |

Exit 2 covers "nothing was proved" on purpose: a run that examined no obligation
— a file with no contracts, a `--filter` that matched nothing — is an error, not
a pass. Unknown options are refused rather than ignored, and options from
comparable verifiers name the trust-wp equivalent.

`trust-wp --help` lists every option; `trust-wp doctor` reports what is
installed and the exact command that supplies anything missing.

**Building it** (needs the Trust toolchain — see `rust-toolchain.toml`; stock
nightly will not do, because the driver links this compiler's `rustc_private`):

```bash
cargo build -p trust-wp-cli -p trust-wp-driver -p targo-trust-wp -p trust-wp -p creusot-contracts
./target/debug/trust-wp doctor
```

`cargo install` is not supported: the engine resolves a Trust sysroot at
runtime and is not relocatable on its own. trust-wp reaches users inside the
`trust` sysroot bundle, which exposes `trust-wp`, `trust-wp-driver` and
`targo-trust-wp` (with back-compat aliases `trust-wp-rustc` and
`cargo-trust-wp`).

## Demo

`demo/` is a guided, self-checking tour of the tool from the command line —
contracts, counterexamples, loop invariants, the emitted SMT query, and what
trust-wp refuses to claim:

```bash
./demo/run.sh            # the full tour
./demo/run.sh --quick    # skip the crate-mode step
```

Every step asserts its exit code and part of its output, so the demo doubles as
a regression test for the CLI's user-visible contract. `demo/README.md` is the
written version of the same tour.

## Snapshot scope

This is a source snapshot of the trust-wp **specification surface and Weakest-Precondition
core** — the contract macros (`crates/trust-wp-macros`), verified std specs
(`crates/trust-wp-std`), the WP/formula core (`crates/trust-wp-core`), the Creusot-compat
contract crates, and the `targo-trust-wp` front-end (`targo trust-wp`, back-compat
alias `cargo trust-wp`) — together with the test harness,
examples, and reference docs.

The `trust-wp` command itself ships (`crates/trust-wp-cli`, core-only): its
`contract`, `bundle` and `result` verbs run in this snapshot with no engine,
and `verify` reports exactly what is missing (`trust-wp doctor`).

The executable verifier lanes — the SMT encoder, the rustc-driver, and the CIC kernel
suite — take a hard dependency on the first-party `ay` solver, which is not yet public.
Those crates are omitted from this snapshot and will be restored once `ay` is published.
The WP-core crates build standalone; end-to-end verification of a `.rs` file is not
exercised here.

The `demo/` tour needs the engine too, so it runs in the full tree rather than
in this snapshot. The Command line section describes both.

## Documentation

Public reference docs live at the repo root:

- `contract-syntax.md` — the contract syntax reference (the full grammar).
- `creusot-compatibility.md` — the Creusot-compatible attribute lane and its status.
- `INTERFACE-v1.md` — the frozen specification-language interface (carrier, grade,
  lane contract, invariants).
- `benchmarking.md` — running and extending the benchmark suite.

The project's goal statement, soundness-assumption inventory, developer-workflow
guide, and the `&mut` give-back (normativity-flip) decision record are internal
documents of the private tree and are not part of this snapshot; the soundness
and workflow notes concern the executable verifier lanes omitted above.

## Examples

Annotated contract examples. Run any of them with `trust-wp <path>`; the
status column is what this tree actually prints today, not an aspiration.

| file | shows | status |
| --- | --- | --- |
| `examples/simple.rs` | `#[requires]` / `#[ensures]` on plain functions | 2 verified |
| `examples/loop_invariant.rs` | `#[invariant]` and `#[variant]` on loops | 3 verified |
| `examples/mut_borrow.rs` | RustHorn `&mut` contracts (`^v`, `old(*v)`) | 3 verified — exit 0 |
| `examples/verified_math/` | a small verified crate — run `trust-wp` inside it | verifies |
| `demo/` | the guided CLI tour, with a self-checking runner | 16/16 checks |

`unknown (proof-trusted)` is the verifier refusing to claim a result it cannot
back: the solver reached UNSAT but the proof carried a step no checker
confirmed, so the verdict is withheld rather than reported as proved. It is a
completeness gap, not a soundness one — and it is the honest failure mode to
have.

**When to expect it.** Earlier revisions of this file named one condition — a
`&mut` parameter together with a reachable branch — and gave `abs_mut` as the
example. That shape proves now, and `examples/mut_borrow.rs` verifies all three
of its functions and exits 0.

There is no short rule to put in its place that I can substantiate, and
inventing one would be worse than admitting that. The verdict is uncommon in
ordinary contract code; where it does appear it clusters around loop invariants
and mutation-heavy bodies. When it happens, isolate the function with
`--filter <NAME>` and read the obligation with `--emit-smt`; stating the same
property in a form the solver can present — an explicit bound rather than an
implied one, or returning a value rather than mutating through a reference —
often gets it proved. The CLI prints the same advice with the verdict.

The verifier links the sibling `../ay` checkout as a path dependency, so it is
only as good as the revision sitting there. An `ay` behind the one the manifest
expects demotes whole lanes to `unknown (proof-trusted)`. If a contract you
expect to prove does not, check that first.
