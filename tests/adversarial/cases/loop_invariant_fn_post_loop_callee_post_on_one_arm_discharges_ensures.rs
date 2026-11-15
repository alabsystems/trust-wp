//@ expect: reject
//@ mechanism: after the loop, `if flag { below(x) }`: the block-slice walker recorded `below`'s postcondition
//@ mechanism: `x@ < 100` as a premise of the function VC unguarded, and it proved the postcondition on the path that
//@ mechanism: skips the call. The post-loop ensures spelling of
//@ mechanism: loop_invariant_fn_post_loop_callee_post_on_other_arm.rs, found probing sideways from D-243.
//@ accept-means: a postcondition false on the path that skips the call is verified, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(200, false)` returns with `x == 200`.
//@ also-verified: below
//@ fixed-by: D-243: each premise of the walker is stated under a formula that holds only where its block runs.
//@ teeth: ACCEPTED at exit 0 before D-243; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

#[ensures(x@ < 100)]
pub fn f(x: u32, flag: bool) {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
    if flag {
        below(x);
    }
}
