//@ expect: reject
//@ verdict: failed
//@ mechanism: the twin of s71_closure_ensures_sibling_fallback_implies_pa that pins the CAUSE
//@ mechanism: to the single-entry fallback: with BOTH closures contracted there are two
//@ mechanism: `closure_ensures` entries, no fallback fires, and the false `proof_assert!(r == 1)`
//@ mechanism: FAILED even on the pre-fix build. This case must keep failing for that reason.
//@ fixed-by: n/a — never accepted; kept beside its siblings as the cause-pinning control
//@ accept-means: identity-matched injection gave c2's call a contract other than c2's own.
//@ WHY THE CONTRACT IS FALSE: r == c2(0) == 2 (c2's own ensures says so); `r == 1` is false.
//@ WHY THE CONTRACT IS FALSE: The callee is #[trusted] (exit 2 regardless); the proof_assert
//@ WHY THE CONTRACT IS FALSE: verdict is what this case pins.
//@ teeth: n/a — never accepted: pre-fix wp-s71 75f19abf `✗ proof_assert in driver_fn FAILED`
//@ teeth: on a review probe with BOTH closures contracted, the shape this case keeps in place.
//@ also-verified: driver_fn::{closure#0}, driver_fn::{closure#1}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[trusted]
#[requires((*f).precondition(arg))]
#[ensures((*f).precondition(arg) ==> exists<st> (*f).postcondition_mut(arg, st, result))]
pub fn call_guarded<F: FnMut(i32) -> i32>(f: &mut F, arg: i32) -> i32 {
    f(arg)
}

pub fn driver_fn() {
    let mut c1 = #[requires(true)]
    #[ensures(result == 1)]
    |_x: i32| -> i32 { 1 };
    let mut c2 = #[requires(true)]
    #[ensures(result == 2)]
    |_x: i32| -> i32 { 2 };
    let _ = call_guarded(&mut c1, 0);
    let r = call_guarded(&mut c2, 0);
    proof_assert!(r == 1);
}

pub fn main() {
    driver_fn();
}
