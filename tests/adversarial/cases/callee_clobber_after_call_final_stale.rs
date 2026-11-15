//@ expect: reject
//@ mechanism: the credit-killing write is inside a SECOND callee. `clobber` takes the same
//@ mechanism: `&mut` and stores through it, and its `#[ensures]` says nothing about `^r`,
//@ mechanism: so nothing contradicts the first call's `Final(x) == 1` and the premise
//@ mechanism: survives unopposed. A rule that only counts writes appearing in THIS body's
//@ mechanism: statements leaves it live: the write is in another function's MIR.
//@ accept-means: a callee that writes a `&mut` without advertising it in its postcondition
//@ accept-means: is invisible to the earlier call that pinned the parameter's final value.
//@ WHY THE PROGRAM IS WRONG: `clobber` leaves `*x == 5`, so `^x` is 5, not 1.
//@ teeth: LIVE on the build that already rejected the direct-write spellings of this
//@ teeth: family: ACCEPTED, `trust-wp: f verified`. Closed by counting a call that is
//@ teeth: handed the borrow as a write to the referent.
//@ also-verified: set, clobber
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

#[ensures(result == 0i32)]
pub fn clobber(r: &mut i32) -> i32 {
    *r = 5i32;
    0i32
}

#[requires(*x == 0i32)]
#[ensures(^x == 1i32)]
pub fn f(x: &mut i32) {
    set(x);
    let _z = clobber(x);
}
