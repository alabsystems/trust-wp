//@ expect: verify
//@ mechanism: R4 (`root_unnamed`) — LIVE blast-radius control. Two `get_mut_ghost` shapes are present
//@ mechanism: in this body, so the projected-expiry lane adjudicates both; the obligation sits BEFORE
//@ mechanism: them and must be unaffected.
//@ fixed-by: n/a (this is the standing gate an R4 closure must not break)
//@ accept-means: n/a (control) — this contract is TRUE and verifies TODAY.
//@
//@ ★WHY THIS CASE CARRIES THE GATE. Every other control in the `g_r4_*` family is xfail: the R4 lane
//@ proves nothing yet, so every TRUE claim that DEPENDS on a pin is unprovable, and a future "fix"
//@ that simply refused harder would leave the whole family green. This one does not depend on a pin,
//@ so it is the case that stops the family from being satisfiable by blanket refusal.
//@
//@ ★AND IT IS NOT MERELY DECORATIVE. Pins are bound inside `apply_mut_borrow_base_assertions`, i.e.
//@ into the BASE premise set of the whole request — they carry no statement position and no path
//@ condition. A pin emitted for a shape at the END of a body is therefore in scope for an obligation
//@ at its START. If an R4 closure emits a premise that is wrong, contradictory, or that re-threads the
//@ receiver's carrier, this earlier obligation is where it shows up first — as a false accept if the
//@ premise is merely wrong (the assertion is already true, so it would still pass) or, more usefully,
//@ as a REJECT if the premise makes the base contradictory or steals the map carrier. Both matter:
//@ the vacuity check demotes rather than accepts, so a contradictory pin presents here as this control
//@ breaking, not as an adversarial case flipping.
//@
//@ WHY THE CONTRACT IS TRUE: the assertion is discharged against the map right after the insert,
//@ before either `get_mut_ghost` call.
//@ teeth: n/a — over-refusal control. ★MEASURED verifying on main (ACCEPTED), with both R4 candidate
//@ teeth: shapes present in the same body. The paired negative measurement is on record too: move the
//@ teeth: same assertion to AFTER the calls and it stops verifying, which is `g_r4_two_call_separation_control`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{logic::FMap, prelude::*};

pub fn prior_obligation_survives() {
    let mut map = FMap::<i32, i32>::new();
    ghost! {
        map.insert_ghost(1, 21);
        proof_assert!(map.lookup(1i32) == 21i32);
        if let Some(x) = map.get_mut_ghost(&1) {
            *x = 43;
        }
        if let Some(y) = map.get_mut_ghost(&2) {
            *y = 44;
        }
    };
}
