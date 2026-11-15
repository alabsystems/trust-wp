//@ expect: reject
//@ mechanism: mutating-receiver state propagation rewrote every Var(receiver) mention in every
//@ mechanism: local to Final(receiver), so a value COPY read before the call followed the mutation
//@ fixed-by: s31 receiver copy freeze (closure.rs receiver_mutation_frozen_locals)
//@ accept-means: a copy EQUAL to the receiver pre-state was rebound to the post-call state
//@
//@ WHY THE ASSERTION IS FALSE: y is 0, x is 1 after inc(&mut x).
//@ teeth: UNVERIFIED — `unknown (sort-coercion bridge in negated goal)` on 3bba620, bc5554c and with the s31 freeze: the equality branch of the propagation is not reached as a verdict yet (skeptic k3). With the freeze, y is a frozen copy (region-free, not a MIR place of the receiver).
//@ also-verified: inc
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*x < 1000i32)]
#[ensures(^x == *x + 1i32)]
pub fn inc(x: &mut i32) {
    *x += 1;
}

pub fn int_copy_eq_wrong() {
    let mut x: i32 = 0i32;
    let y = x;
    inc(&mut x);
    proof_assert!(y == x);
}
