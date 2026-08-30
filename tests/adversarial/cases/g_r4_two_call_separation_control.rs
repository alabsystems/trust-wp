//@ expect: verify
//@ xfail: same wall as `g_r4_scrutinee_value_control` — no prophecy slot for the `Option<&mut V>`
//@ xfail: payload, so neither entry's post-value is constrained. Measured today: rejected.
//@ mechanism: R4 (`root_unnamed`) — the TRUE twin of `g_r4_two_call_pin_fusion`: two separate borrows
//@ mechanism: keep two separate final values.
//@ fixed-by: n/a (open; blocked on the R4 closure)
//@ accept-means: n/a (control). An XPASS means an R4 closure produced pins that are BOTH real and
//@ accept-means: SEPARABLE. It only counts alongside a still-rejecting `g_r4_two_call_pin_fusion`:
//@ accept-means: a fusion defect flips control and adversarial TOGETHER, which is exactly how the
//@ accept-means: `take_first_mut` false accept presented (`a2_sibling_binder_control` XPASSes with
//@ accept-means: Fix A disabled, and so does its adversarial twin).
//@
//@ WHY THE CONTRACT IS TRUE: both keys are present, both arms run, and each writes its own entry.
//@ teeth: n/a — over-refusal control, currently xfail. Not demonstrated in either direction.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{logic::FMap, prelude::*};

pub fn two_call_separation() {
    let mut map = FMap::<i32, i32>::new();
    ghost! {
        map.insert_ghost(1, 21);
        map.insert_ghost(2, 22);
        if let Some(x) = map.get_mut_ghost(&1) {
            *x = 43;
        }
        if let Some(y) = map.get_mut_ghost(&2) {
            *y = 44;
        }
        proof_assert!(map.lookup(1i32) == 43i32);
        proof_assert!(map.lookup(2i32) == 44i32);
    };
}
