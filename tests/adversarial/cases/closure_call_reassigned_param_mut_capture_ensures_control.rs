//@ expect: verify
//@ xfail: the closure's `ensures(a@ == 7)` is credited over the FINAL value of its `&mut` capture,
//@ xfail: whose value at the call is `a + 1`; that has no prophecy slot, and the constant-carrier arm
//@ xfail: of the final-collapse guard refuses it (D-14): `final-collapse refused (fail-closed)`. The
//@ xfail: campaign driver verified this program only by reading the clause over the parameter's entry
//@ xfail: value, the reading that also verifies its false twin
//@ xfail: closure_call_reassigned_param_mut_capture_ensures_pins_entry. Retire this directive when a
//@ xfail: `&mut` capture of a computed local gets a prophecy carrier at the call.
//@ xfail-verdict: unknown
//@ mechanism: control for closure_call_reassigned_param_mut_capture_ensures_pins_entry: the
//@ mechanism: assertion reads the value the closure leaves.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@ < 100)]
pub fn caller(mut a: i32) {
    a = a + 1;
    let mut c = #[ensures(a@ == 7)]
    || {
        a = 7;
    };
    c();
    proof_assert!(a@ == 7);
}
