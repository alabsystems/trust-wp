//@ expect: reject
//@ mechanism: proof_assert_after_param_field_write_keeps_entry_requires.rs with the write made through a local borrow of the field (`let r = &mut p.a; *r = 7;`) instead of a place assignment. Neither spelling reaches the proof_assert lane's view of the by-value parameter, so a fix keyed on one place shape leaves the other open.
//@ accept-means: an assertion about a parameter's field after a write through a local `&mut` to that field is proved from the precondition on its entry value, and the crate exits 0.
//@ WHY THE ASSERTION IS FALSE: `*r = 7` stores into `p.a` before the assertion, so `p.a` is 7 there, never 3.
//@ teeth: MEASURED ACCEPTED, exit 0: `proof_assert in creusot_test::k verified ✓` and `k verified ✓`.
//@ fixed-by: D-140: the proof_assert lane withdraws the entry facts naming a by-value parameter its substitution binds to anything but itself (`p` to the tuple whose `a` is 7), so the precondition no longer contradicts the write. The assertion is then `unknown` on ay's sort mismatch between the struct's sort and the tuple constructor that binding builds, not FAILED. The place-assignment spelling, which the substitution gives no binding, is proof_assert_after_param_field_write_keeps_entry_requires, still open.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P {
    pub a: u32,
    pub b: u32,
}

#[requires(p.a@ == 3)]
pub fn k(mut p: P) {
    let r = &mut p.a;
    *r = 7;
    proof_assert!(p.a@ == 3);
}
