//@ expect: verify
//@ mechanism: the control of loop_invariant_fn_join_of_two_callee_posts_read_as_the_stronger.rs: each arm's premise
//@ mechanism: holds where its arm runs, and `x@ < 100` follows on both, so the disjunction of the arms proves it.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
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

#[ensures(x@ < 50)]
pub fn below50(x: u32) {
    #[invariant(true)]
    while x >= 50 {}
}

#[ensures(x@ < 100)]
pub fn f(x: u32, flag: bool) {
    if flag {
        below50(x);
    } else {
        below(x);
    }
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
}
