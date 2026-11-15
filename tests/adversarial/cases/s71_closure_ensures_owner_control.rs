//@ expect: verify
//@ xfail: both closures are capture-less, so both environments lower to the SAME term
//@ xfail: `__trust_wp_tuple0()`; no evidence tells c2's call from c1's, and wp-s71 v2's
//@ xfail: identity rule attaches neither contract (`driver_fn unknown`). Verifying this needs
//@ xfail: closure environments that carry their closure's identity (a translate/rvalue.rs
//@ xfail: representation change), not a shortcut — see s71_closure_ensures_sole_owner_control
//@ xfail: for the shape identity does reach (one closure of its arity in the body).
//@ mechanism: over-refusal control for the wp-s71 v2 identity rule: the shape of
//@ mechanism: s71_closure_ensures_sibling_fallback_flat with the TRUE contract (c2's own
//@ mechanism: `result == 2`). Pins the cost of identity-or-nothing on identical environments.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — this contract is TRUE; an XPASS means identity reached
//@ accept-means: identical environments (check it did so by identity, not by a shortcut).
//@ teeth: n/a — over-refusal control; xfail on wp-s71 v2 (see xfail reason).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires((*f).precondition(arg))]
#[ensures(exists<st> (*f).postcondition_mut(arg, st, result))]
pub fn call_plain<F: FnMut(i32) -> i32>(f: &mut F, arg: i32) -> i32 {
    f(arg)
}

#[ensures(result == 2)]
pub fn driver_fn() -> i32 {
    let mut c1 = #[requires(true)]
    #[ensures(result == 1)]
    |_x: i32| -> i32 { 1 };
    let mut c2 = #[requires(true)]
    #[ensures(result == 2)]
    |_x: i32| -> i32 { 2 };
    let _ = call_plain(&mut c1, 0);
    call_plain(&mut c2, 0)
}

pub fn main() {
    assert_eq!(driver_fn(), 2);
}
