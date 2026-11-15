//@ expect: reject
//@ mechanism: mutating-receiver state propagation rewrote every Var(receiver) mention in every
//@ mechanism: local to Final(receiver), so a value COPY read before the call followed the mutation
//@ fixed-by: s31 receiver copy freeze (closure.rs receiver_mutation_frozen_locals)
//@ accept-means: the copy SOURCE was advanced by a mutation of its copy
//@
//@ WHY THE ASSERTION IS FALSE: x stays 0; only its copy y was incremented.
//@ teeth: PROSPECTIVE — rejected on bc5554c and with the s31 freeze; a freeze that identified the mutated place by the receiver EXPRESSION (Var(x) after `let mut y = x`) instead of MIR would freeze the mutated local and accept it.
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

pub fn copy_source_wrong() {
    let x: i32 = 0i32;
    let mut y = x;
    inc(&mut y);
    proof_assert!(x == 1i32);
}
