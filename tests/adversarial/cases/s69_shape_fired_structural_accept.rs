//@ expect: reject
//@ verdict: failed
//@ fn-failed: g
//@ ay-not-unsat: g
//@ mechanism: the in-slice refutation SHAPES (`postcondition_contradicts_requirements`, `result_postcondition_contradicts_return_expr`, ...) stopped ending the slice so that a `Failed` could carry a validated model, and that reopened the ~10 STRUCTURAL ACCEPT lanes that sit between the shape checks and the final negated-goal solve in `verify_single_obligation_slice_inner`. Here `postcondition-contradicts-requirements` fires on `fact(3) == 5` vs `fact(3) == 6`, and `recursive_logic_fn_equality_matches_evaluation` then reaches `prove_prechecked_literal_false_obligation_with_solver`, which asserts `false` in a FRESH encoder and reports the trivial UNSAT as `Verified(fully_verified)`. No negated-goal solve for `g` runs at all.
//@ accept-means: trust-wp claims it PROVED `g`'s contract while its own refutation shape says the contract cannot hold, on evidence that is literally `false |= anything` — the accepted UNSAT is over a stack containing only `false`, with nothing of `g` in it. The `#[requires]` is also inconsistent (`fact(3) = 6`, not 5), and trust-wp's own policy makes vacuity a soundness gap (`vacuous > 0` -> exit 2, `requirements_are_obviously_contradictory` -> Unknown), so an exit-0 `verified` here is a false accept under this tool's stated policy in two independent ways.
//@ fixed-by: wp-s69 v2 — a fired shape `break`s to the real negated-goal solve ('structural_lanes) and `SLICE_REFUTATION_SHAPE` makes every structural accept lane refuse after a shape has fired
//@ teeth: ACCEPTED — `trust-wp: g verified ✓`, `1 verified, 0 failed, 0 errors`, exit 0, `vacuous=0`, with NO negated-goal solve for `g` in `TRUST_WP_AUTHORITY_TRACE=1` — on wp-s69 81458208 (measured on the vacuous-bypass review probe: a `#[requires]`/`#[ensures]` pair contradicting a recursive logic fn's value)
//@ also-verified: creusot_test::fact
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
#[variant(n)]
#[requires(n >= 0)]
pub fn fact(n: Int) -> Int {
    pearlite! { if n <= 0 { 1 } else { n * fact(n - 1) } }
}

#[requires(fact(3) == 5)]
#[ensures(fact(3) == 6)]
pub fn g(x: i32) -> i32 {
    x
}
