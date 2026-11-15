//@ expect: reject
//@ mechanism: a `proof_assert!` after a loop reading a local written between the loop's exit and
//@ mechanism: the assertion was proved from the loop's exit facts stated over the local's NEW
//@ mechanism: value: `#[invariant(i <= n)] while i < n { i += 1; } i = 0; proof_assert!(i >= n)` at
//@ mechanism: function level (tw), and after an inner loop in an outer loop's body (plw).
//@ accept-means: a loop's exit facts are read at a state the loop never left with.
//@ WHY THE CONTRACT IS FALSE: with n = 1 the assertion reads i = 0, and 0 >= 1 is false.
//@ fixed-by: D-188 (a loop exit fact naming a local written between the exit arm and the
//@ fixed-by: assertion is not stated)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on b7ed4bbf (D-187) both assertions VERIFIED and tw with them (a file holding tw alone
//@ teeth: was ACCEPTED); with D-188 both are FAILED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n < 1000u32)]
pub fn tw(n: u32) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    i = 0u32;
    proof_assert!(i >= n);
}

pub fn plw(n: u32) {
    let mut k = 0u32;
    while k < 2u32 {
        let mut i = 0u32;
        #[invariant(i <= n)]
        while i < n {
            i += 1;
        }
        i = 0u32;
        proof_assert!(i >= n);
        k += 1;
    }
}
