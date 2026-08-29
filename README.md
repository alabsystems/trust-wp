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
Trust-fork toolchain and the first-party `ay` solver to run — see Install.

Most importantly: **arithmetic overflow is currently assumed, not proved.** The
`increment` above is `#[requires(x > 0)] #[ensures(result > x)] { x + 1 }`; at
`x = i32::MAX` it overflows and panics, and `x > 0` does not exclude that input,
yet the contract verifies. MIR's `+`, `-` and `*` overflow assertions enter the
verification condition as hypotheses rather than obligations, so a proof here
means "correct assuming no overflow", not "correct". (Shift amounts are the
exception: an over-wide shift is a proof obligation, not an assumption.) Closing
the arithmetic gap is the single most valuable contribution available here.

The other honest failure mode is `unknown (proof-trusted)`: the solver reached
UNSAT but the proof carried a step no checker could confirm, so the verdict is
withheld rather than reported as proved. Nothing is proved wrong — this is a
completeness gap, not a soundness one. When it happens, isolate the function
with `--filter <NAME>` and read the obligation with `--emit-smt`; stating the
same property in a form the solver can present — an explicit bound rather than
an implied one, or returning a value rather than mutating through a reference —
often gets it proved. The CLI prints the same advice with the verdict.

**Author:** Andrew Yates · **License:** Apache-2.0 · **Copyright:** 2026 Andrew Yates

## Install

There is no `cargo install` for this, and it would be dishonest to imply one.
trust-wp is a rustc driver: it links `rustc_private` and reads the compiler's
own post-borrowck MIR, so it must be built against the same compiler it drives
— and that compiler is a fork. The engine also resolves a Trust sysroot at
runtime, so it is not relocatable on its own. Expect to build three things.

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
`unknown (proof-trusted)`. If a contract you expect to prove does not, check
that first.

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
trust-wp 0.3.0+g58a37601 (https://github.com/alabsystems/trust-wp)

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
above: the in-process verbs need nothing but `trust-wp-cli`.

trust-wp reaches users inside the `trust` sysroot bundle, which exposes
`trust-wp`, `trust-wp-driver` and `targo-trust-wp` (with back-compat aliases
`trust-wp-rustc` and `cargo-trust-wp`).

## How it works

Contracts are ordinary Rust attributes — `#[requires]`, `#[ensures]`,
`#[invariant]`, `#[variant]` and `proof_assert!`, with `#[logic]`,
`#[predicate]` and `#[law]` for specification functions. trust-wp works on
post-borrowck MIR rather than HIR, so what it proves is what the compiler
actually compiles, and it models `&mut` borrows with a
[RustHorn](https://doi.org/10.1145/3462205)-style (current, final) encoding.

The attribute and expression syntax is
[Creusot](https://github.com/creusot-rs/creusot)-compatible — `*v`, `^v`,
`old()`, `@` and quantifiers all carry over — but compatibility is not
complete, and trust-wp is not a drop-in replacement: `creusot-compatibility.md`
has the matrix, feature by feature, with the open gaps (ghost code chief among
them). trust-wp is an independent ALab tool, not affiliated with, derived from,
or endorsed by that project.

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

Three verbs run `trust-wp-core` in this process and need no engine, sysroot or
solver:

```
trust-wp contract parse|vc    parse a contract expression, or emit its
                              weakest-precondition VC as SMT-LIB2
trust-wp bundle verify|validate|replay|example
                              prove, check or independently replay a
                              `trust-wp.verify-bundle.v1` request
trust-wp result               decode a saved result-protocol transcript
```

`-h` is a summary and `--help` is the full page; `trust-wp help <COMMAND>`
covers one verb. `-q` prints only failures and the summary; `--filter <NAME>`
narrows a run to the functions whose path matches `NAME`; `--emit-smt` prints
the SMT-LIB2 query instead of proving; `--json` gives one
`trust-wp.cli-report.v1` document on stdout, on every exit, with human output
left on stderr.

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
comparable verifiers name the trust-wp equivalent. `trust-wp --help` lists every
option.

## Snapshot scope

This repository is a source snapshot of the trust-wp **specification surface
and weakest-precondition core**: the contract macros (`crates/trust-wp-macros`),
the verified std specs (`crates/trust-wp-std`), the WP/formula core
(`crates/trust-wp-core`), the Creusot-compat contract crates, the
`targo-trust-wp` front end (`targo trust-wp`, back-compat alias
`cargo trust-wp`) and the `trust-wp` command itself (`crates/trust-wp-cli`,
core-only) — together with the test harness, examples and reference docs.

The executable verifier lanes — the SMT encoder (`crates/trust-wp-ay`), the
rustc driver (`crates/trust-wp-driver`) and the library facade
(`crates/trust-wp-lib`) — depend on the `ay` solver and the `trust-ir` proof IR,
and are not part of this snapshot. The WP-core crates build standalone, and the
in-process verbs run here with nothing installed; `verify` reports exactly what
is missing (`trust-wp doctor`). End-to-end verification of a `.rs` file, and the
`demo/` tour that exercises it, live in the full tree.

## Documentation

Public reference docs live at the repo root:

- `contract-syntax.md` — the contract syntax reference (the full grammar).
- `creusot-compatibility.md` — the Creusot-compatible attribute lane and its status.
- `INTERFACE-v1.md` — the frozen specification-language interface (carrier, grade,
  lane contract, invariants).
- `benchmarking.md` — running and extending the benchmark suite.
- `CHANGELOG.md` — what changed, and why.

The project's goal statement, soundness-assumption inventory, developer-workflow
guide, and the `&mut` give-back (normativity-flip) decision record are internal
documents of the private tree.

Source comments cite two trees that do not resolve in a clone of this
repository. `designs/*.md` paths name the private tree's design notes; they are
retained as provenance only. `reference/creusot/...` paths name a local Creusot
checkout that the compatibility harness expects at that path — it is gitignored
and you provision it yourself (`tests/creusot_compat/README.md`).

## Examples

Annotated contract examples. Run any of them with `trust-wp <path>`; the
status column is what this tree actually prints today, not an aspiration.

| file | shows | status |
| --- | --- | --- |
| `examples/simple.rs` | `#[requires]` / `#[ensures]` on plain functions | 2 verified |
| `examples/loop_invariant.rs` | `#[invariant]` and `#[variant]` on loops | 3 verified |
| `examples/mut_borrow.rs` | RustHorn `&mut` contracts (`^v`, `old(*v)`) | 3 verified — exit 0 |
| `examples/verified_math/` | a small verified crate — run `trust-wp` inside it | 6 verified |

`demo/` — in the full tree, not this snapshot — is a guided tour of the same
ground from the command line: contracts, counterexamples, loop invariants, the
emitted SMT query, and what trust-wp refuses to claim. Every step asserts an
exit code and part of the output (16 checks on a full `./demo/run.sh`;
`--quick` skips the crate-mode one), so the tour doubles as a regression test
for the CLI's user-visible contract. `demo/README.md` is the written version.
