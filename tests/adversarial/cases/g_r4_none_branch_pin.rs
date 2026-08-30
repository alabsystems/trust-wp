//@ expect: reject
//@ mechanism: R4 (`root_unnamed`) — the `optmut_none_branch_pin` shape: an enum-payload expiry pin
//@ mechanism: emitted without PROVING the `Some` branch was taken, on a carrier consumed in
//@ mechanism: scrutinee position (`if let Some(x) = map.get_mut_ghost(&k)`).
//@ fixed-by: n/a (OPEN — R4 refuses to pin at all today; this case is the PREREQUISITE gate that
//@ fixed-by: must exist before anyone closes R4 by naming the call-result carrier)
//@ accept-means: the projected-expiry lane concluded the `Some` arm ran on a path where the callee
//@ accept-means: returned `None`. `FMap::GET_MUT_GHOST` already ensures
//@ accept-means: `Some(v) => self.contains(*k) && (^self).contains(*k)`, so believing the arm is
//@ accept-means: enough to manufacture containment out of nothing — no value write-back clause
//@ accept-means: required. Every `Option<&mut V>` postcondition in the corpus becomes untrustworthy.
//@
//@ WHY THE CONTRACT IS FALSE: `map` is an unconstrained parameter. Call `none_branch_pin(FMap::new())`
//@ and `get_mut_ghost(&1)` returns `None`, the arm never runs, the map is unchanged, and
//@ `map.contains(1)` is false. A concrete execution refutes it.
//@
//@ WHY CONTAINMENT IS LEFT UNKNOWN, DELIBERATELY: an empty *literal* map would make the wrong pin's
//@ premise set CONTRADICTORY (`is-Some` vs. a provably absent key), and a contradictory base is
//@ demoted by the vacuity check rather than accepted — the case would reject for a reason that has
//@ nothing to do with the defect. `c_singleton_control` is the standing example of that trap. With
//@ containment free the wrong premise set stays SAT and the accept is a real accept.
//@ teeth: PROSPECTIVE — NOT an A/B-demonstrated accept. Measured today: rejected in 2s,
//@ teeth: `proof_assert ... inconclusive (incomplete)` (runner verdict `error`) — i.e. rejected
//@ teeth: trivially, because R4 emits no pin at all so nothing links `^x` to the map.
//@ teeth: WHAT A WRONG R4 FIX MUST DO TO START ACCEPTING THIS: name the call-result carrier and then
//@ teeth: ASSERT `is-Some(root)` as a base premise instead of using it as the pin's ANTECEDENT.
//@ teeth: That is the natural mistake here — the write is unconditionally present in the arm's MIR
//@ teeth: block, so the producer "knows" the arm ran; and pins are bound inside
//@ teeth: `apply_mut_borrow_base_assertions`, i.e. into the BASE premise set, which carries no path
//@ teeth: condition of its own. Asserting rather than assuming deletes the `None` path from the VC.
//@ teeth: Equivalently: emit the pin UNGUARDED after synthesising a root name (projected_expiry.rs
//@ teeth: R4's own stated failure mode). Either edit makes this contract provable.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{logic::FMap, prelude::*};

pub fn none_branch_pin(mut map: FMap<i32, i32>) {
    ghost! {
        if let Some(x) = map.get_mut_ghost(&1) {
            *x = 43;
        }
        proof_assert!(map.contains(1i32));
    };
}
