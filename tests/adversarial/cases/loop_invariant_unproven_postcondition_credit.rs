//@ expect: reject
//@ mechanism: a loop phase that comes back unknown sends the function to the function-level
//@ mechanism: check WITHOUT the loop invariant, and a postcondition that needs no invariant
//@ mechanism: (`ensures(true)`) was proved there and credited `verified ✓`. The invariant is an
//@ mechanism: obligation of the function; a proof that never read it says nothing about it.
//@ accept-means: `f(1, 1)` leaves `x == 1` after its first outer iteration, so the outer invariant
//@ accept-means: `x == 0u32` is FALSE, and the function was credited anyway.
//@ fixed-by: D-221 (a function-level proof run without an unproved loop invariant is not a credit)
//@ teeth: ACCEPTED at exit 0 on the build before this fix: the inner-loop havoc withholds the
//@ teeth: outer preservation refutation, the function-level check proves `ensures(true)`.
//@ also-verified: one
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 1u32)]
pub fn one() -> u32 { 1 }

#[ensures(true)]
pub fn f(n: u32, m: u32) {
    let mut i = 0u32;
    let mut x = 0u32;
    let mut y = 0u32;
    #[invariant(x == 0u32)]
    while i < n {
        x = 0;
        y = 0;
        let mut j = 0u32;
        #[invariant(true)]
        while j < m { x = one(); j += 1; }
        i += 1;
    }
}
