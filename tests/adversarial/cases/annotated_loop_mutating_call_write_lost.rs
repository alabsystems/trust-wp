//@ expect: reject
//@ mechanism: The pointee is changed by a CALL inside an annotated loop — a contracted helper
//@ mechanism: whose own `#[ensures(^x == 7)]` verifies — and the caller still keeps the
//@ mechanism: identity resolve for the borrow it handed over. Same lane as
//@ mechanism: annotated_loop_param_write_prophecy_lost: making the post-loop final-value
//@ mechanism: injection a no-op rejects this too. This is the shape ordinary Creusot code
//@ mechanism: takes, so the family is not confined to a direct store in a synthetic loop.
//@ accept-means: calling a mutating helper in a loop leaves the caller's `&mut` parameter
//@ accept-means: reading as untouched, and the helper's OWN postcondition is what proves the
//@ accept-means: pointee changed — the two facts are both available and they contradict.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut v = 0; f(&mut v); afterwards
//@ v == 7, so `^r` is 7 while `*r` is 0.
//@ teeth: OPEN. Measured ACCEPTED, exit 0, "trust-wp: f verified ✓".
//@ also-verified: set7
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^x == 7i32)]
pub fn set7(x: &mut i32) {
    *x = 7;
}

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    let mut i = 0i32;
    #[invariant(true)]
    while i < 1 {
        set7(r);
        i += 1;
    }
}

pub fn caller() {
    let mut v = 0i32;
    f(&mut v);
    assert!(v == 7);
}
