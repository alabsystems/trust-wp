//@ expect: reject
//@ mechanism: the recursive spelling of proof_assert_after_reborrow_call_keeps_pre_call_write. The self-call's spec is empty, so after `rec_set(0, acc)` the pointee is unconstrained, but the assertion lane still reads the `*acc = n` written before the call. s80_rec_selfspec_mut_leak.rs records the same defect and is rejected only because its `n - 1` leaves an arithmetic panic site the function-level lane does not walk; with the recursion argument a literal, nothing refuses.
//@ accept-means: a `&mut` pointee keeps its pre-call value across a recursive self-call that overwrote it, and the crate exits 0.
//@ WHY THE ASSERTION IS FALSE: for every `n > 0`, `rec_set(0, acc)` stores 0, so `*acc` is 0 at the assertion, never `n`.
//@ teeth: MEASURED ACCEPTED, exit 0: `proof_assert in creusot_test::rec_set verified ✓` beside `rec_set verified ✓ (termination)`, which is true (`0 < n`). A `bool`-flagged recursion with no termination attributes is accepted the same way, contract-free or under `#[ensures(true)]`. The control asserts before the self-call.
//@ fixed-by: ?
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[variant(n)]
pub fn rec_set(n: u32, acc: &mut u32) {
    if n > 0 {
        *acc = n;
        rec_set(0, acc);
        proof_assert!(*acc == n);
    } else {
        *acc = 0;
    }
}
