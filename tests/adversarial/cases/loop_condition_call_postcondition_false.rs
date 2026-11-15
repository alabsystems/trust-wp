//@ expect: reject
//@ mechanism: reject twin of loop_condition_call_postcondition_control: `small` returns `k < 11` and
//@ mechanism: says so, so the body runs at `i == 10` and leaves `i == 11`. Reading the condition's
//@ mechanism: call through its contract must not cost the refutation.
//@ accept-means: `go()` runs its body at `i == 10` and returns 11, so the invariant `i <= 10u32` and
//@ accept-means: `ensures(result == 10u32)` are FALSE, and trust-wp proved them.
//@ verdict: failed
//@ fn-failed: go
//@ also-verified: small
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (k < 11u32))]
pub fn small(k: u32) -> bool { k < 11 }

#[ensures(result == 10u32)]
pub fn go() -> u32 {
    let mut i = 0u32;
    #[invariant(i <= 10u32)]
    while small(i) { i += 1; }
    i
}
