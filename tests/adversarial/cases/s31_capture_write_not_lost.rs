//@ expect: reject
//@ mechanism: mutating-receiver state propagation rewrote every Var(receiver) mention in every
//@ mechanism: local to Final(receiver), so a value COPY read before the call followed the mutation
//@ fixed-by: s31 receiver copy freeze (closure.rs receiver_mutation_frozen_locals)
//@ accept-means: the closure's write to its captured variable was undone by a freeze
//@
//@ WHY THE ASSERTION IS FALSE: the closure set x to 5.
//@ teeth: PROSPECTIVE — rejected on bc5554c and with the s31 freeze (skeptic k4 capture_wrong); a blanket restore after the capture loop would accept it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn capture_wrong() {
    let mut x: i32 = 0i32;
    {
        let mut c = || {
            x = 5i32;
        };
        c();
    }
    proof_assert!(x == 0i32);
}
