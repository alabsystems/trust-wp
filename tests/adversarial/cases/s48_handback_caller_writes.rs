//@ expect: reject
//@ mechanism: a `#[ensures(result == p)]` callee's entry-value clause used as a post-call fact — the caller writes through the borrow it was handed back and still reads the entry value of the argument.
//@ fixed-by: wp-s48 570e6edc (the borrow-forwarding exception needs a KNOWN library callee, not a contract shape)
//@ accept-means: a call to a user function whose contract hands its `&mut` argument back as the result freezes that argument at its entry value, so any write the CALLER then performs through the returned borrow is invisible.
//@ WHY THE PROGRAM IS WRONG: `*r = 7` writes through the very borrow of `x` that `hand_back` returned, so `x` is 7 when the borrow expires; the proof_assert claims 5.
//@ teeth: A/B'd 2026-09-14: ACCEPTED (false accept) on wp-campaign ff8f5aa6
//@ teeth: in the campaign adversarial run, built from a separate pre-fix checkout; rejected here.
//@ teeth: It also accepted at wp-s48 2e75bc47 and on the reviewer's build with the
//@ teeth: result-identity exception forced off, so the hole is OLDER than this front
//@ teeth: — the reviewer's probe was this same handback-then-caller-write shape.
//@ verdict: unknown
//@ also-verified: hand_back
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == p)]
fn hand_back(p: &mut u32) -> &mut u32 {
    p
}

pub fn k() {
    let mut x: u32 = 5;
    {
        let r = hand_back(&mut x);
        *r = 7;
    }
    proof_assert!(x@ == 5);
}
