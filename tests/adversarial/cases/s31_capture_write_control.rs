//@ expect: verify
//@ mechanism: captured-variable update advances (true: x == 5 after the closure call)
//@ fixed-by: s31 receiver copy freeze (closure.rs receiver_mutation_frozen_locals)
//@ accept-means: n/a (control)
//@ xfail: FnMut closure capture write is not propagated to the proof_assert read of x (k4 capture_true)
//@ teeth: UNVERIFIED — FAILED on 3bba620 (skeptic k4), bc5554c and with the s31 freeze.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn capture_true() {
    let mut x: i32 = 0i32;
    {
        let mut c = || {
            x = 5i32;
        };
        c();
    }
    proof_assert!(x == 5i32);
}
