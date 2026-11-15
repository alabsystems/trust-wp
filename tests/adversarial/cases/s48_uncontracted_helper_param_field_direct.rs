//@ expect: reject
//@ mechanism: an uncontracted helper writes through a `&mut` borrow of a BY-VALUE parameter's field; the assertion reads that field back at its entry value.
//@ fixed-by: D-241: the `&mut p.a` borrow withdraws `p`'s entry facts at the assertion, which is now FAILED; `k` stays refused as before.
//@ accept-means: a write through `&mut p.a` does not reach the by-value owner `p`, so a precondition about `p.a` survives the call as a post-call fact.
//@ WHY THE PROGRAM IS WRONG: `set7` leaves `p.a == 7`; the assertion claims 3, the value `p.a` had at entry.
//@ teeth: NO TEETH vs campaign, recorded deliberately as a REGRESSION GUARD, not a fix:
//@ teeth: `failed` on wp-campaign ff8f5aa6 as well (adversarial run) and
//@ teeth: `k FAILED` at wp-s48 e7b818f0. NOT FULLY CLOSED: the
//@ teeth: `proof_assert` itself is still reported `verified ✓` and the rejection is `k`'s own
//@ teeth: contract failing on an evidence gap. `verdict:`/`fn-failed:` below pin that the
//@ teeth: rejection is trust-wp's OWN verdict on `k` and not an unrelated refusal, so a
//@ teeth: regression to a clean ACCEPT is still caught. Root cause measured
//@ teeth: on the review probe f3_param_field_ensures under TRUST_WP_LOG=debug: the
//@ teeth: substitution lane rewrites the assertion to `tuple_get_0(^p)@ == 3` — correct intent —
//@ teeth: but `^` over a by-value `Datatype` carrier has no prophecy slot, so the encoder's
//@ teeth: Final-collapse folds `^p` back to `p` and the precondition `tuple_get_0(p)@ == 3`
//@ teeth: discharges it. The copy form (s48_uncontracted_helper_param_field_scalar) rejects
//@ teeth: properly because its assertion does not go through `^p`.
//@ verdict: failed
//@ refused-with: k unknown (refutation withheld
//@ teeth: D-241 RE-PIN: the assertion is FAILED (it was `verified ✓`), which makes the crate verdict `failed`; `k` is still refused with the line above.
//@ teeth: wp-s81 RE-PIN (not a weakening). `k`'s rejection was trust-wp refuting the `false`
//@ teeth: it injected for the uncontracted `set7` call — the shape wp-s81 D1 stops publishing as
//@ teeth: a counterexample; the case file already recorded the rejection as riding on "an
//@ teeth: evidence gap" rather than a real refutation. `k` is still refused (exit 2, never
//@ teeth: gate-clean); the crate verdict is now `unknown` and the per-function pin moved to
//@ teeth: `refused-with:`, so a regression that credited `k` is still caught. The proof_assert
//@ teeth: is STILL wrongly `verified ✓` — that half is untouched and still open. Its credit is
//@ teeth: deliberately NOT declared in `also-verified-assertion`, so the gate holds this case
//@ teeth: RED until the write through `&mut p.a` reaches `p`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P {
    pub a: u32,
    pub b: u32,
}

fn set7(q: &mut u32) {
    *q = 7;
}

#[requires(p.a@ == 3)]
#[ensures(true)]
pub fn k(mut p: P) -> u32 {
    set7(&mut p.a);
    proof_assert!(p.a@ == 3);
    0
}
