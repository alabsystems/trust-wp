//@ expect: reject
//@ mechanism: the credit-killing write is inside a CLOSURE built by this body and called
//@ mechanism: after the crediting call. The captured `&mut` reaches the parameter through
//@ mechanism: the closure's environment, whose type the shared mut-ref collector does not
//@ mechanism: walk, so borrow provenance stopped at the closure construction and the
//@ mechanism: call `c()` looked like a call about nothing.
//@ accept-means: a write a closure performs through a captured `&mut` is invisible to the
//@ accept-means: earlier call that pinned the parameter's final value.
//@ WHY THE PROGRAM IS WRONG: the closure sets `*x` to 3, so `^x` is 3, not 1.
//@ teeth: LIVE on the build that already rejected the direct-write and second-callee
//@ teeth: spellings: ACCEPTED, `trust-wp: f verified`. Refuted here.
//@ also-verified: set
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

#[requires(*x == 0i32)]
#[ensures(^x == 1i32)]
pub fn f(x: &mut i32) {
    set(x);
    let mut c = || {
        *x = 3i32;
    };
    c();
}
