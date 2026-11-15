//@ expect: reject
//@ mechanism: reject twin of loop_condition_call_variant_control: `small` admits `k == 10`, where the
//@ mechanism: variant `9 - i@` is -1 on entry to the body.
//@ accept-means: `go()` runs its body at `i == 10` with the variant at -1, so the loop's termination
//@ accept-means: argument is FALSE, and trust-wp proved it.
//@ verdict: failed
//@ fn-failed: go
//@ also-verified: small
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result ==> k < 11u32)]
pub fn small(k: u32) -> bool { k < 11 }

pub fn go() {
    let mut i = 0u32;
    #[invariant(i@ <= 11)]
    #[variant(9 - i@)]
    while small(i) { i += 1; }
}
