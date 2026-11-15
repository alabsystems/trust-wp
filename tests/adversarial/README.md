<!-- Copyright 2026 Andrew Yates -->
<!-- Author: Andrew Yates <andrewyates.name@gmail.com> -->
<!-- Licensed under the Apache License, Version 2.0 -->

# trust-wp adversarial negative corpus

A trust-wp-**owned** suite of programs whose contracts are **FALSE**, each constructed so that
it is provable **only if** a specific, root-caused encoder/driver defect is present. A clean
accept here is a false accept — not a compat gap, not a scoring nuance.

```bash
python3 tests/adversarial/run_adversarial.py            # the whole suite
python3 tests/adversarial/run_adversarial.py -v --filter a2
python3 tests/adversarial/run_adversarial.py --json out.json --keep-output
```

Exit code `0` = every case behaved as declared; `1` = a false accept or an over-refusal;
`2` = runner/setup failure.

The committed `cases/*.k.log` files are captured `--keep-output` transcripts kept as
evidence beside the case they belong to. Nothing reads them, and the campaign's own
absolute paths are rewritten in them to `<campaign-root>/` and `<rustup-home>` — this
directory ships in the public snapshot, where a home directory is forbidden content.
The same rewrite applies to the `/tmp` path four `s61_*` `//@ teeth:` lines cited. Set `TRUST_WP_HARNESS_TARGET_DIR` to reuse a warm shared Cargo
target directory across runs (strongly recommended — otherwise each run pays a cold dependency
compile).

## Why this exists

trust-wp's only automated false-accept detector is the Creusot **should_fail** lane. That lane
is a **reference** corpus: compat accounting depends on it staying pristine, so its blind spots
cannot be closed by editing it. And it has blind spots:

```
$ grep -rln 'Option<&mut' reference/creusot/tests/should_fail/
(no output)
```

Zero `should_fail` tests use an enum-embedded `&mut` — the exact shape of the `take_first_mut`
false accept that was adjudicated on 2026-08-05 and demoted by Fix A (932a7de).

Worse, that adjudication proved live that **every other gate is blind to a premise that is
consistent but false**:

| Gate | Catches a consistent-but-false premise? |
|---|---|
| vacuity / base recheck | **No** — it only detects *contradictory* premise sets |
| fresh base recheck (e51e8e8) | **No** — same polarity |
| unsoundness demotion roster | **No** — a wrong pin that encodes cleanly fires no counter |
| ay model validation / DebugChecked | **No** — a wrong pin makes the base *more* constrained, still satisfiable |
| should_fail lane | **Yes — and it is the only one** |

The `take_first_mut` false accept was found by hand audit. This suite exists so the next one
is not.

**Do not modify `reference/creusot`.** This corpus is the place to add negative coverage.

## Layout

```
tests/adversarial/
  run_adversarial.py     the runner (reuses the compat harness's fixture scaffolding only)
  cases/*.rs             one standalone crate root per case, adversarial and control side by side
```

The runner reuses `tests/creusot_compat/harness_*` for **fixture scaffolding only** — reviewed-lock
derivation, toolchain pinning, the stable wrapper bin dir, shared-target locking and per-test cache
invalidation, and the harness's own definition of a clean verification run
(`_verification_run_succeeded`). It does **not** touch the Creusot lane discovery, the
classification tables, or any baseline JSON, and it never reads `reference/creusot`.

## Writing a case

Each case is a normal Rust crate root plus a directive header:

```rust
//@ expect: reject            // adversarial: a clean ACCEPT is a false accept
//@ expect: verify            // control: must verify cleanly today
//@ xfail: <reason>           // controls only — known not to verify today
//@ xfail-verdict: <failed|unknown|error|timeout>   // xfail controls: the rejection MUST be this flavour
//@ mechanism: <what defect this targets>
//@ fixed-by: <commit that closed it>
//@ accept-means: <what an accept would prove is broken>
//@ teeth: <how the case was shown to have teeth, or why it could not be>
//@ timeout: <seconds>        // optional per-case budget override
```

```rust
//@ verdict: <failed|unknown|error|timeout>   // reject cases: the rejection MUST be this flavour
//@ refused-with: <text>      // reject cases: one of trust-wp's OWN lines must contain <text>
//@ fn-failed: <name>         // reject cases: `trust-wp: <name> FAILED` must be reported
//@ ay-not-unsat: <name>      // reject cases: ay was asked about <name> and did not answer unsat
//@ also-verified: <names>    // reject cases: the only functions that may print `verified`, comma-separated,
                              // each spelled as its line prints it (`<S as Inc>::inc` for a trait impl)
//@ also-verified-assertion: <names>
                              // reject cases: the only `proof_assert in <name> verified` lines, one entry
                              // per assertion, crate first (`creusot_test::k`); name a function twice
                              // for two of its assertions
```

A reject case passes only when every positive verdict it carries is one it declares TRUE. The
process verdict is a whole-crate summary, so one refuted function makes the run a rejection while
another function, or an assertion, in the same crate is credited on a claim that is false. An
assertion credit is its own claim about the program at one point: it is declared apart from its
function's credit, and neither declares the other. The line names the function and not the
assertion, so each assertion is counted, which is what stops a second, false assertion riding on
a first one's declaration. A credit the driver withdrew (a trait-contract withdrawal takes back its
function's assertion credits too) needs no declaration, and the gate holds its count of standing
assertion credits to the driver's own `proof_assert_verified`. A function credit beside an
assertion of its own that did not prove is flagged even when declared, whatever word reported the
assertion unproved.

### When a rejection earns credit (wp-s47 v2)

A non-ACCEPTED run of an `expect: reject` case is **ok only if trust-wp delivered the rejection**:

1. **Verifier refutation**: verdict `failed`, `unknown` or `timeout`, AND the run carries a parseable
   `TRUST_WP_RESULT` wire line (the driver reached its verdict phase). Inconclusive `proof_assert`s
   are read from the wire counters and count as `unknown`.
2. **Named trust-wp refusal**: verdict `error`, AND the case declares `//@ verdict: error` plus
   `//@ refused-with: <text>`, AND `<text>` occurs on one of trust-wp's own output lines
   (`trust-wp: ...`, `trust-wp: error: ...`, or `error: trust-wp: ...`), AND a wire line is present.
   `verdict: error` without `refused-with:` is a load error.

Everything else is **TEETH LOST** (exit 1), never ok:

* a rustc/cargo compile error: no wire line, because the driver never ran its analysis. Before this
  rule a fixture that stopped compiling kept its `[ok]`; edition 2024 did exactly that to
  `s40_extern_never_branch` (`error: extern blocks must be unsafe`);
* a run the harness killed at its budget without a wire line;
* an `error` verdict the case did not name;
* a crash: `panics>0` on the wire, `panicked at`, `internal compiler error`, or exit status 101.

So a new case that is rejected by an up-front refusal must name that refusal, and a case whose
fixture breaks fails loudly. Controls (`expect: verify`) are unchanged, except that an `xfail`
control declaring `xfail-verdict:` must be rejected with exactly that flavour: a true program
priced as `unknown` that starts printing `FAILED` has gained a false refutation, and that is an
over-refusal, not the known price.

Directives are read from the header block only — parsing stops at the first line of real Rust, so
a `//@` in the body cannot silently retune a case. Repeat a key to continue a long
value: the pieces join with a space. A key that steers the verdict (`expect`,
`timeout`, `verdict`, `fn-failed`, `refused-with`, `ay-not-unsat`, `also-verified`,
`also-verified-assertion`, `xfail-verdict`) may appear only
once -- repeating one is ambiguous about which value wins, so it is refused.
`expect` and `mechanism` are required; `xfail` on an `expect: reject` case is a hard error (an
adversarial case may never be excused from rejecting).

Rules that keep the suite honest:

1. **The contract must actually be false**, refutable by a concrete execution — say which one in
   the header. "Unprovable" is not good enough; a merely-unprovable contract turns the case into
   a completeness test that will be silently "fixed" one day.
2. **Ship the control.** A false accept and an over-refusal are both regressions. If the control
   does not verify today, mark it `xfail` with the reason — never delete it.
3. **Prove the teeth, or say you did not.** A case that cannot be shown to fail on a build with
   the defect re-introduced is documentation, not a gate. Record which it is in `//@ teeth:`.

### Demonstrating teeth

Preference order: (i) build a pre-fix commit and show the case is ACCEPTED; (ii) disable the
specific guard via an env knob or a one-line local revert and show the accept; (iii) say plainly
that neither was practical and mark the teeth UNVERIFIED.

Use an isolated checkout for a defective build, or make a narrowly scoped local
guard change and restore it before validating the final tree. Record the exact
build and observed outcome beside the run. Do not depend on an untracked
scratchpad or leave a bypass in production code.

## Coverage and evidence

Case headers are the source of expectations, mechanisms, and demonstrated or
prospective teeth. Current outcomes belong in the runner's JSON and logs with
the source and solver identities. A historical verdict table cannot establish
the state of a later build, and passing this corpus does not establish coverage
of every Rust or contract shape.

Check both directions of a change. A missing premise can reject a true claim;
an unjustified premise can prove a false one. For the former, the positive
control carries the strongest regression signal. Keep the negative twin too.

The `g_r4_*` family exercises projected expiry of unnamed `Option<&mut T>`
carriers. Its negative cases distinguish guarded Some-branch pins, current
versus final values, and independent call identities. Its value controls pair
true and false claims about the same write. The prior-obligation controls also
check that a later write-back cannot contaminate an earlier obligation through
the base premise set. Read each case's directives before changing this lane;
prospective teeth and known completeness limits are declared per case.
