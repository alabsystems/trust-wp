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
`2` = runner/setup failure. Set `TRUST_WP_HARNESS_TARGET_DIR` to reuse a warm shared Cargo
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
//@ mechanism: <what defect this targets>
//@ fixed-by: <commit that closed it>
//@ accept-means: <what an accept would prove is broken>
//@ teeth: <how the case was shown to have teeth, or why it could not be>
//@ timeout: <seconds>        // optional per-case budget override
```

Directives are read from the header block only — parsing stops at the first line of real Rust, so
a `//@` in the body cannot silently retune a case. Repeat a key to continue a long value.
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

Every case here used **(ii)**. The cheapest reliable recipe on this box: add a
`std::env::var_os("...").is_some()` early return to the guard predicate, build
(`cargo build --locked -p trust-wp-driver` plus `--release --bin trust-wp-rustc` when a release
binary exists — about 75s total on a warm target), then A/B the same build with and without the
env var. Revert the knob afterwards and confirm `git diff --stat` is empty. The knob patch used
for the current teeth column is preserved in the session scratchpad as `defect-knobs.patch`.

## Current status (trust-wp c453385, ay 153665fb9)

7 adversarial cases, all REJECTED, 0 ACCEPTED. 7 controls: 5 verify, 2 xfail.

| Case | Mechanism | Verdict on main | Teeth |
|---|---|---|---|
| `a1_optmut_prophecy_inversion` | Final-collapse inversion, `Option<&mut T>` | failed (CE) | unverified — rides the real-prophecy carrier; shape gate for the grep-verified blind spot |
| `a2_sibling_binder_fusion` | sibling-binder prophecy fusion (take_first_mut) | unknown (final-collapse refused on `^first`) | **verified — ACCEPTED with Fix A disabled** |
| `a3_user_adt_payload_inversion` | Final-collapse inversion, user ADT payload | failed (CE) | unverified — payload lowers to a plain Int; shape gate |
| `b_rc_view_sort_hijack` | Rc/Arc view-sort hijack | failed | unverified, structurally — the defect only weakens premises |
| `c_singleton_collapse_identity` | ghost-token singleton collapse | failed | **verified — ACCEPTED with the resfid gate disabled** |
| `d_sort_fallback_premise_drop` | sort-fallback premise drop | unknown | unverified, structurally — same reason as `b` |
| `e_declare_collision_degrade` | declare-collision degrade | failed | unverified — degrade is fail-closed; two knobs tried |

Controls with demonstrated teeth: `b_rc_view_control` (rejected with the adtpa fix disabled —
reproduces the adjudicated arc_and_rc counterexample), `c_singleton_control` (errors with the
resfid gate disabled), `a2_sibling_binder_control` (XPASSes with Fix A disabled — reproducing the
pre-932a7de `take_first_mut` pass that rested on the false lemma).

Two mechanisms — the Rc/Arc view-sort hijack and the sort-fallback premise drop — move in the
**false-reject** direction: fabricating a premise away can never make a false goal provable. For
those, the case with teeth is the **control**, and the adversarial twin is a standing shape gate.
That asymmetry is worth remembering when adding cases: decide which direction your defect moves
before deciding which side of the pair carries the gate.

## The `g_r4_*` family — the gate that must exist BEFORE R4 is closed

Fix B M6 (`430aa45`) wired the projected-expiry lane into the `proof_assert` pipeline. Its census
emitted **9 candidates, 0 pins**; two disarmed on **R4 (`root_unnamed`)** — the live `ghost_map`
and `ghost_vec` shapes, where the `Option<&mut V>` carrier is consumed in scrutinee position
(`if let Some(x) = map.get_mut_ghost(&1) { *x = 43 }`) and so has no source name for `is-Some(root)`
to receive. R4's refusal is a soundness condition, and the M6 report made the order explicit:
**the `Option<&mut>` negative corpus must exist before anyone closes R4 by naming the carrier.**
That is this family — built adversary-first, as with the restore-route guard and `take_first_mut`.

Four attacks (`none_branch_pin`, `scrutinee_stale_value`, `two_call_pin_fusion`,
`seq_scrutinee_stale_value`) and six controls. Two things about it are unusual and deliberate:

1. **Its `//@ teeth:` lines are PROSPECTIVE, not demonstrated.** R4 emits no pin at all today, so
   every attack in this family is rejected *trivially* — there is nothing yet to be wrong. A case
   that merely fails today is worthless, so each attack instead states, concretely, **what a wrong
   R4 fix would have to do for it to start being accepted** (assert `is-Some(root)` as a base
   premise rather than as the pin's antecedent; land the withheld `(^self)[key] == ^r` write-back
   while `Final` still collapses onto the binder; key the pin on anything shared between two call
   sites). Read those lines as the specification the fix is being held to.
2. **Four of the six controls are `xfail`, and that is the finding, not an excuse.** The R4 lane
   proves nothing yet, so every TRUE claim that *depends* on a pin is unprovable — including the
   two obligations `ghost_map.rs`/`ghost_vec.rs` actually want. An XPASS on
   `g_r4_scrutinee_value_control` or `g_r4_seq_value_control`, **with its adversarial twin still
   rejecting**, is the signal that R4 was closed correctly. Each pair differs only in a literal
   (`43` vs `21`, `42` vs `21`), so nothing but a pin carrying the correct *death* value can
   separate them; a fix that flips both has landed the inversion.

Because of (2), the family's non-blanket-refusal gate rests on the two controls that verify
**today** — `g_r4_prior_obligation_control` and `g_r4_seq_prior_obligation_control`. Both hold an
R4 candidate shape in the body while discharging an obligation placed *before* it. They are not
decorative: pins are bound in `apply_mut_borrow_base_assertions`, i.e. into the **base** premise
set, which carries no statement position and no path condition — so a pin emitted for a shape at
the end of a body is in scope for an obligation at its start. A contradictory or carrier-stealing
pin presents as *these breaking*, not as an adversarial case flipping, because the vacuity check
demotes rather than accepts.

## Not covered yet

* Prophecy pins in datatype carriers (Fix B). `memory/fixb-prophecy-slots-design.md` §B.4 lists
  four probes — `optmut_premature_resolve`, `optmut_id_distinct`, `optmut_none_branch_pin`, plus
  the pin/resolve consistency self-check. `a1`/`a3` cover the first two shapes;
  `g_r4_none_branch_pin` covers the third. The pin/resolve consistency self-check is still open,
  and cannot be written as a rejectable contract until a pin actually exists to be inconsistent
  with.
* The still-armed std axioms the Final-collapse audit listed (`GET_MUT_GENERIC`,
  `HASHMAP_ITER_MUT`, `CELL_SET`). They are consumer-masked today and refuse fail-closed under
  Fix A; a case per axiom would pin that.
