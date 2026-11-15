//@ expect: verify
//@ mechanism: the control of loop_entry_reads_local_before_untranslated_reassignment.rs: the same loops,
//@ mechanism: postcondition, snapshot and one-arm write, with the assignment before the loop translated
//@ mechanism: (`a = x - x`), so each invariant and postcondition is true and is established from the value the
//@ mechanism: assignment computes. The reassigned parameter has no twin here: with `x = x - x` before the loop
//@ mechanism: its invariant `x == 0u32` is not established (FAILED, an incompleteness).
//@ accept-means: n/a (control) — `a` is `0` at loop entry in every execution.
//@ fixed-by: n/a (control)
//@ teeth: every function verified on the campaign tip and with D-217.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unused_assignments)]

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(n < 10u32)]
pub fn preloop_invariant(x: u32, n: u32) {
    let mut a = 0u32;
    a = x - x;
    let mut i = 0u32;
    #[invariant(a == 0u32)]
    while i < n {
        i += 1;
    }
}

#[requires(n < 10u32)]
#[ensures(result == 0u32)]
pub fn preloop_post(x: u32, n: u32) -> u32 {
    let mut a = 0u32;
    a = x - x;
    let mut i = 0u32;
    #[invariant(a == 0u32)]
    while i < n {
        i += 1;
    }
    a
}

#[requires(n < 10u32)]
#[ensures(result == 0u32)]
pub fn snapshot_invariant_then_return(x: u32, n: u32) -> u32 {
    let mut a = 0u32;
    a = x - x;
    let s = snapshot!(a);
    let mut i = 0u32;
    #[invariant(*s == 0u32)]
    #[invariant(a == *s)]
    while i < n {
        i += 1;
    }
    a
}

#[requires(n < 10u32)]
pub fn one_arm(x: u32, n: u32, c: bool) {
    let mut a = 0u32;
    if c {
        a = x - x;
    }
    let mut i = 0u32;
    #[invariant(a == 0u32)]
    while i < n {
        i += 1;
    }
}
