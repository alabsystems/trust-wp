//@ expect: reject
//@ mechanism: mutating-receiver state propagation rewrote every Var(receiver) mention in every
//@ mechanism: local to Final(receiver), so a value COPY read before the call followed the mutation
//@ fixed-by: s31 receiver copy freeze (closure.rs receiver_mutation_frozen_locals)
//@ accept-means: a copy of a captured variable followed the closure's write
//@
//@ WHY THE ASSERTION IS FALSE: y copied x == 0 before the closure set x = 5.
//@ teeth: PROSPECTIVE — rejected on bc5554c and with the s31 freeze (capture-binding loop now skips frozen copies).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn capture_copy_wrong() {
    let mut x: i32 = 0i32;
    let y = x;
    {
        let mut c = || {
            x = 5i32;
        };
        c();
    }
    proof_assert!(y == 5i32);
}
