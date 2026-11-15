//@ expect: reject
//@ mechanism: wp-s41 v2 — the invariant at the loop exit names a loop-written by-value parameter by its
//@ mechanism: entry name, which the postcondition also uses for the entry value (y11).
//@ accept-means: `ensures(x@ == 9)` about the ENTRY value proved from the exit invariant although x may enter as 0
//@ fixed-by: wp-s41 v2 extraction.rs r17 guard without the obligation condition
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ <= 9)]
#[ensures(x@ == 9)]
pub fn f(mut x: i32) {
    let mut i = 0;
    #[invariant(i@ > 0 ==> x@ == 9)]
    #[invariant(0 <= i@ && i@ <= 3)]
    while i < 3 {
        x = 9;
        i += 1;
    }
}
