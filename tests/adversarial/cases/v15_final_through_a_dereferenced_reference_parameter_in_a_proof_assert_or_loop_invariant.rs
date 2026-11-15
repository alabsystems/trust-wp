//@ expect: reject
//@ mechanism: `^*x` of `x: &mut &mut i32` in a `proof_assert!` or a loop invariant: `*x` is a
//@ mechanism: dereference of a name, which D-129's text guard counts as a borrow named as one, but
//@ mechanism: the borrow it denotes is the caller's inner borrow, whose final value the caller
//@ mechanism: decides after the call (D-129 "Not closed" (c)). No guard refused it: the assertion
//@ mechanism: was inconclusive and the invariant FAILED, each only by what the solver answered.
//@ accept-means: a claim about the final value of the caller's inner borrow is credited.
//@ WHY THE CONTRACT IS FALSE: `let mut a = 1; let mut r = &mut a; pa_deref_deref(&mut r); *r = 7;`
//@ WHY THE CONTRACT IS FALSE: ends the inner borrow at 7 while `**x` is 1 at the assertion.
//@ fixed-by: D-183 (the parameter's type decides a final read reached through it in every lane)
//@ refused-with: final value of a value held through the
//@ teeth: MEASURED (debug driver, ay 561e68c7c): on f214082f the assertion was inconclusive and the
//@ teeth: loop FAILED (loop invariant), with no named refusal; with D-183 both are refused before
//@ teeth: encoding.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn pa_deref_deref(x: &mut &mut i32) {
    proof_assert!(^*x == **x);
}

pub fn loop_deref_deref(x: &mut &mut i32) {
    let mut i = 0i32;
    #[invariant(^*x == **x)]
    while i < 3i32 {
        i += 1i32;
    }
}
