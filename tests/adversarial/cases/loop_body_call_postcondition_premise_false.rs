//@ expect: reject
//@ mechanism: reject twin of loop_body_call_postcondition_premise_control: `go_m` returns false
//@ mechanism: and says so, so `#[invariant(b)]` is FALSE at establishment and after every
//@ mechanism: iteration. Carrying the postcondition into the loop VC must not cost the refutation.
//@ accept-means: `go_loop(1)` returns false, so its `ensures(result)` and the invariant `b` are
//@ accept-means: FALSE, and trust-wp proved them.
//@ verdict: failed
//@ fn-failed: go_loop
//@ also-verified: go_m
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(!result)]
pub fn go_m() -> bool { false }

#[ensures(result)]
pub fn go_loop(n: u32) -> bool {
    let mut b = go_m();
    let mut i: u32 = 0;
    #[invariant(b)]
    while i < n {
        b = go_m();
        i += 1;
    }
    b
}
