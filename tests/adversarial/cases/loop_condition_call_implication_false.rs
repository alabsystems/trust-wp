//@ expect: reject
//@ mechanism: reject twin of loop_condition_call_implication_control: `more` stops at 9 and says so,
//@ mechanism: so the loop exits with `i == 9`. The condition's clauses carry the exit, and must not
//@ mechanism: carry it past what they say.
//@ accept-means: `go()` returns 9, so `ensures(result == 10u32)` is FALSE, and trust-wp proved it.
//@ verdict: failed
//@ fn-failed: go
//@ also-verified: small, more
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (k < 10u32))]
pub fn small(k: u32) -> bool { k < 10 }

#[ensures(result ==> k < 9u32)]
#[ensures(!result ==> k >= 9u32)]
pub fn more(k: u32) -> bool { k < 9 }

#[ensures(result == 10u32)]
pub fn go() -> u32 {
    let mut i = 0u32;
    #[invariant(i <= 10u32)]
    while more(i) {
        if small(i) { i += 1; }
    }
    i
}
