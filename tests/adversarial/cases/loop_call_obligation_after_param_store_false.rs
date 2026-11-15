//@ expect: reject
//@ mechanism: reject twin of loop_call_obligation_after_param_store_control: `need_zero(*a)` with `*a`
//@ mechanism: stored 7 before the loop, a precondition that holds only of the entry value the
//@ mechanism: precondition `(*a)@ == 0` states. The call obligation is the marker, so it is never
//@ mechanism: proved; its refutation is withheld with the control's.
//@ accept-means: `f` calls `need_zero(7)`, violating its precondition, and trust-wp proved the call.
//@ also-verified: need_zero
//@ teeth: UNVERIFIED as a false-accept gate: rejected `failed` before D-225 (over the marker, which is
//@ teeth: no run of the program either) and `unknown` at D-225. It pins that withholding the marker's
//@ teeth: refutation never turns the call into a proof.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
pub fn need_zero(x: u32) {}

#[requires((*a)@ == 0)]
pub fn f(a: &mut u32) {
    *a = 7;
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { need_zero(*a); i += 1; }
}
