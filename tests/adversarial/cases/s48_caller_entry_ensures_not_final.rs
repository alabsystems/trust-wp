//@ expect: reject
//@ mechanism: a callee ensures over the ENTRY value `*p` read at the call site as if it were `^p`.
//@ fixed-by: guard (rejected on wp-campaign 541d1c75 too); it pins the CALLER half of the s48 entry-read fix.
//@ accept-means: a call keeps the callee's entry-value clause as a post-call fact about the argument.
//@ WHY THE PROGRAM IS WRONG: keep5_then_set7 leaves x == 7; its ensures states only the ENTRY value.
//@ teeth: rejected (unknown) on wp-campaign 541d1c75 and on wp-s48, measured 2026-09-13. It ACCEPTS
//@ teeth: (exit 0) as soon as the pre-s48 call-site filter is restored — measured on a build with
//@ teeth: spec_mutating_ref_arg_positions back on spec_mentions_post_state_for_aliases.
//@ also-verified: keep5_then_set7
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires((*p)@ == 5)]
#[ensures((*p)@ == 5)]
fn keep5_then_set7(p: &mut u32) {
    *p = 7;
}

pub fn k() {
    let mut x: u32 = 5;
    keep5_then_set7(&mut x);
    proof_assert!(x@ == 5);
}
