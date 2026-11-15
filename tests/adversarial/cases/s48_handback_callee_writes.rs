//@ expect: reject
//@ mechanism: the callee writes through the `&mut` argument before handing it back as the result; the caller still reads the argument's entry value after the call.
//@ fixed-by: wp-s48 570e6edc (the borrow-forwarding exception needs a KNOWN library callee, not a contract shape)
//@ accept-means: `#[ensures(result == p)]` is being trusted as a claim that the callee's BODY left `*p` alone — a claim trust-wp never checks.
//@ WHY THE PROGRAM IS WRONG: `hand_back_write` sets `*p` to 9 before returning it, so `x` is 9; the proof_assert claims 5.
//@ teeth: A/B'd 2026-09-14: ACCEPTED (false accept) on wp-campaign ff8f5aa6
//@ teeth: in a full adversarial run, rejected here. It also accepted at
//@ teeth: 2e75bc47 and on the reviewer's build with the result-identity exception forced
//@ teeth: off on a standalone probe of this same callee-writes-then-hands-back call.
//@ teeth: wp-s57 435abd9b changed the FLAVOUR of this rejection, not the fact of it: the
//@ teeth: callee's own `#[ensures(result == p)]` is now refuted (`hand_back_write FAILED`)
//@ teeth: before the caller's proof_assert is reached, so the run reports `failed` instead of
//@ teeth: `unknown`. The declared verdict was updated from `unknown` to `failed` to match;
//@ teeth: nothing about the s48 call-site mechanism this case documents was weakened.
//@ verdict: failed
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == p)]
fn hand_back_write(p: &mut u32) -> &mut u32 {
    *p = 9;
    p
}

pub fn k() {
    let mut x: u32 = 5;
    {
        let r = hand_back_write(&mut x);
        let _y = *r;
    }
    proof_assert!(x@ == 5);
}
