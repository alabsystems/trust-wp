//@ expect: reject
//@ mechanism: R4 (`root_unnamed`) — the exact live census shape
//@ mechanism: `if let Some(x) = map.get_mut_ghost(&1) { *x = 43 }`, carrying a FALSE claim about the
//@ mechanism: entry's value AFTER the write. Targets a pin (or a write-back clause) that resolves
//@ mechanism: `^x` to the PRE-write payload instead of the death value.
//@ fixed-by: n/a (OPEN — R4 refuses to pin; prerequisite gate for closing it)
//@ accept-means: `(^map)[1]` was equated to the payload's value at EXTRACTION rather than at DEATH.
//@ accept-means: That is the prophecy inversion `trust-wp-std/src/logic/fmap.rs` names in prose as
//@ accept-means: the reason `GET_MUT_GHOST`'s `(^self)[*key] == ^r` clause is withheld: `Final` on a
//@ accept-means: match binder collapses to the binder (`match_enc/deref_collapse.rs`) and `Final` on
//@ accept-means: the Datatype-sorted carrier collapses to the carrier (`pure_encoding/wrapper.rs`
//@ accept-means: Phase 1b), so `^r` aliases `*r` and the clause inverts into `(^self)[key] == OLD`.
//@ accept-means: An accept here means that inversion went live.
//@
//@ WHY THE CONTRACT IS FALSE: the map holds `1 -> 21`, the arm runs (key 1 is present) and writes 43.
//@ After the block `map.lookup(1) == 43`, not 21. Refutable by running `scrutinee_stale_value()`.
//@ teeth: PROSPECTIVE — NOT an A/B-demonstrated accept, and the weakest-evidence case of this family.
//@ teeth: Measured today: REJECTED, but by solver exhaustion, not by refutation —
//@ teeth: `hard timeout expired ... outer_timeout=22.6s`, `proof_assert ... unknown (timeout)` at the
//@ teeth: 120s case budget, and still rejected (51s / 62s) when the budget is raised to 300s. State
//@ teeth: that plainly: a timeout is not a refutation, and this case is currently held by a BUDGET.
//@ teeth: ON THE STALE-CARRIER ROUTE, WHICH IS THE OTHER WAY THIS CONTRACT COULD BE PROVED (the
//@ teeth: post-block `map.lookup(1)` resolving against the PRE-call map, which still holds 21): it is
//@ teeth: NOT measured closed. What is measured is that it is not a FAST accept route — the same
//@ teeth: assertion placed BEFORE the write closes in ~1.7s (`g_r4_prior_obligation_control`), while
//@ teeth: this one burns two successive solver budgets without accepting. That is consistent with
//@ teeth: `fmap.rs`'s claim that the `^self` mentions advance the receiver's carrier, and it is
//@ teeth: circumstantial, not conclusive. Do not upgrade it without an A/B.
//@ teeth: WHAT A WRONG R4 FIX MUST DO TO START ACCEPTING THIS: land `GET_MUT_GHOST`'s withheld
//@ teeth: `(^self)[*key] == ^r` write-back — which ANY R4 closure needs, since a caller-side pin on
//@ teeth: `^x` reaches the map through no other clause — without first giving the `Option<&mut V>`
//@ teeth: payload a real prophecy slot. Then `^x` collapses to `*x` and `(^map)[1] == 21` follows.
//@ teeth: The same accept arrives if the pin's death value is read from the extraction statement
//@ teeth: rather than the last tracked write (a mis-implemented R8/R9).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{logic::FMap, prelude::*};

pub fn scrutinee_stale_value() {
    let mut map = FMap::<i32, i32>::new();
    ghost! {
        map.insert_ghost(1, 21);
        if let Some(x) = map.get_mut_ghost(&1) {
            *x = 43;
        }
        proof_assert!(map.lookup(1i32) == 21i32);
    };
}
