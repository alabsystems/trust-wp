# trust-wp, from the command line

A guided tour of **trust-wp** as a standalone tool: what you type, what comes
back, and what it does and does not claim.

```bash
./demo/run.sh            # the full tour
./demo/run.sh --quick    # skip the crate-mode step, which compiles a crate
```

Every step in `run.sh` asserts its exit code and a piece of its output, so the
demo is also a regression test for the CLI's user-visible contract. It exits
non-zero if anything drifts.

---

## What trust-wp is

You write contracts into ordinary Rust source — `#[requires]`, `#[ensures]`,
`#[invariant]`, `#[variant]`, `proof_assert!`. trust-wp intercepts the
post-borrowck MIR, turns each contract into a verification condition using a
Dijkstra-style **weakest-precondition** transformation, and discharges it on the
[`ay`](https://github.com/alabsystems/ay) SMT solver.

It does not run your program. There is no input to choose, no coverage to chase,
and no unroll depth to pick: a `verified ✓` covers every input the precondition
admits.

## The three things to know about the CLI

```
trust-wp <FILE.rs>       verify one file — no Cargo project needed
trust-wp                 verify the crate in the current directory
trust-wp example         write a small contracted file to start from
trust-wp doctor          report what is installed, and how to fix what is not
```

Exit codes are the interface for scripts:

| code | meaning |
| --- | --- |
| `0` | everything verified |
| `1` | a contract was disproved — a counterexample exists |
| `2` | encoding/solver error, a soundness gap, **nothing was proved**, or the engine could not run |
| `3` | a contract failed to parse, or the command line was rejected |
| `101` | internal error — a bug worth reporting, not something in your code |

## Getting a binary

From a fresh checkout, on a machine with the Trust toolchain installed:

```bash
targo --unverified build -p trust-wp-cli -p trust-wp-driver -p targo-trust-wp -p trust-wp -p creusot-contracts
./target/debug/trust-wp doctor
```

`trust-wp doctor` names anything still missing and the exact command that
supplies it. The front-door binary links nothing but libSystem, so `--help`,
`--version` and `example` work before any of the rest exists; the engine
(`trust-wp-rustc`) links `rustc_private` and needs a Trust sysroot at runtime.

`TRUST_WP_BIN=/path/to/trust-wp ./demo/run.sh` runs the tour against a binary
from somewhere else — a release build in another checkout, for instance. There
is no packaged install: as of 2026-08-30 the Trust toolchain's `bin/` ships no
`trust-wp`, so the build above is how you get one.

---

## The tour

### 1. A contract, proved

```rust
#[requires(lo <= hi)]
#[requires(lo >= 0 && hi <= 1000)]
#[ensures(result >= lo)]
#[ensures(result <= hi)]
pub fn midpoint(lo: i32, hi: i32) -> i32 {
    lo + (hi - lo) / 2
}
```

```console
$ trust-wp demo/01_contracts.rs
✓ increment verified
✓ midpoint verified
✓ max_of verified

3 verified, 0 failed, 0 errors
finished in 8.2s
```

`--filter <NAME>` narrows a run to the functions whose path contains `NAME`.

### 2. A contract that is false

The useful answer is not "no". It is the input that breaks the contract:

```console
$ trust-wp demo/02_counterexample.rs
trust-wp: clamp FAILED ✗ (postcondition)
  return expression at demo/02_counterexample.rs:16:8: 16:14
  violated ensures #0: (result >= lo)
  counterexample:
    hi = 0
    lo = 0
    result = -1
    x = 1
```

`clamp(1, 0, 0)` returns `-1`. Exit code 1.

### 3. Loops, without unrolling

A bounded model checker unrolls a loop to some depth and reports "no bug up to
N". trust-wp asks for the induction hypothesis instead, and proves it for all N:

```rust
#[requires(n >= 0 && n <= 46_340)]
#[ensures(result >= 0)]
#[invariant(total >= 0 && i >= 0 && i <= n && total <= 46_340 * i)]
#[variant(n - i)]
pub fn sum_to(n: i32) -> i32 { /* ... */ }
```

Four obligations come out of that: **initialization** (the precondition
establishes the invariant), **preservation** (one arbitrary iteration maintains
it), **postcondition** (invariant plus loop exit imply the `#[ensures]`), and
**termination** (the `#[variant]` strictly decreases and stays non-negative).

An invariant has to be strong enough to prove *itself*, not merely be true.
`preservation check failed` means it is not, and strengthening it is the fix.

Because there is nothing to unroll, `--unwind` is refused rather than accepted
and ignored:

```console
$ trust-wp --unwind 5 demo/03_loops.rs
error: `--unwind` is not a trust-wp option
help: trust-wp is a deductive (unbounded) verifier, so loops take
      `#[invariant(...)]` (and `#[variant(...)]` for termination) rather than an
      unwind bound
```

### 4. The obligation itself

`--emit-smt` prints the SMT-LIB2 query. It is self-contained — every symbol it
mentions is declared, and the well-definedness guards the driver attaches to
terms (a divisor being non-zero, say) are lifted into assertions of their own —
so it goes straight into a solver:

```console
$ trust-wp --emit-smt --filter increment demo/01_contracts.rs
; Verification condition for: increment
(set-logic ALL)

; Variable declarations
(declare-const result Int)
(declare-const x Int)
(declare-const x_view Int)

; Preconditions
(assert (> x 0))
(assert (>= x_view (- 2147483648)))
(assert (<= x_view 2147483647))

; Result assignment
(assert (= result (+ x 1)))

; Negated postconditions (unsat = verified)
(assert (not (> result x)))

(check-sat)
```

```console
$ trust-wp --emit-smt --filter increment demo/01_contracts.rs > vc.smt2
$ ay vc.smt2
unsat
c ay.proof.certificate unproved_steps=0 foreign_assumes=no trust_free=yes
```

`unsat` on the *negated* postcondition is the proof. `--emit-smt-dir <DIR>`
writes one annotated `.smt2` per function instead; `--dry-run` prints the exact
engine invocation without running it.

### 5. What it refuses to claim

A verifier that reports success when it proved nothing is worse than no
verifier. trust-wp fails closed — a run that examined no obligation is an error:

```console
$ trust-wp --filter no_such_function demo/01_contracts.rs
error: nothing was verified — the run proved nothing
help: `--filter no_such_function` matched no function; drop it to see everything
      the file declares
$ echo $?
2
```

The same rule catches a file with no contracts at all. Unknown options are
refused rather than ignored, and options from comparable tools name the
trust-wp equivalent instead of failing silently.

### 6. Creusot-compatible attributes

`demo/04_creusot_compat.rs` is the same shape written against the
`creusot_contracts` surface. The front door links that shim for a lone `.rs`
file exactly as it links `trust_wp`, so the invocation does not change either.

trust-wp is an independent ALab tool: not affiliated with, derived from, or
endorsed by the Creusot project.

### 7. A whole crate

Run `trust-wp` with no file inside a Cargo project and it verifies the package,
driving `targo --unverified check` with the trust-wp driver as the `RUSTC_WRAPPER`:

```console
$ cd examples/verified_math && trust-wp
    Checking verified_math v0.1.0 (examples/verified_math)
info: adaptive timeout: 6 verifiable functions, reducing per-function timeout
      from 60s to 50s (crate budget: 300s)
✓ safe_increment verified
✓ double verified
✓ abs verified
✓ is_positive verified
✓ zero verified
✓ negate verified

6 verified, 0 failed, 0 errors
```

Everything after `--` goes to cargo untouched: `trust-wp -- -p mycrate
--all-features`.

---

## What this demo does not show

Deliberately, because it would not be honest to claim it:

- **Arithmetic overflow.** Every machine-integer addition, subtraction,
  multiplication, division and index in a verified function is a proof
  obligation (`crates/trust-wp-driver/src/mir_analysis/extract/assertion.rs`).
  The preconditions in the demo bound their inputs so those obligations are
  provable; without them the run reports a counterexample at the overflow.
- **`&mut` prophecy contracts** (`^v`, `old(*v)`) are shown only in
  `examples/mut_borrow.rs`, not here. All three of its functions verify and the
  file exits 0. An earlier revision of this document recorded the third,
  `abs_mut`, as `unknown (proof-trusted)`; that was accurate when written and is
  no longer.

`unknown (proof-trusted)` is the tool declining, not passing: it counts as an
error and exits 2. That is the honesty meter working — a solver verdict without
a replayable proof does not license a claim. It is uncommon in ordinary contract
code, and when it appears the verdict is withheld rather than guessed.

**A prerequisite, not a limitation:** the verifier links the sibling `../ay`
checkout as a path dependency, so it is only as good as the revision sitting
there. An `ay` behind the one the manifest expects demotes whole lanes to
`unknown (proof-trusted)` and, on division contracts, has produced counterexamples
that falsify nothing. If results here look worse than this document claims,
check that first: `cd ../ay && git fetch && git status`.

## Where to go next

- `trust-wp --help` — every option, with the exit codes.
- `../contract-syntax.md` — the full contract grammar: `#[logic]`, `#[predicate]`,
  `#[trusted]`, `ghost!`, `snapshot!`, `proof_assert!`, `extern_spec!`.
- `../creusot-compatibility.md` — what the compat lane covers.
- `../INTERFACE-v1.md` — the frozen specification-language interface.
