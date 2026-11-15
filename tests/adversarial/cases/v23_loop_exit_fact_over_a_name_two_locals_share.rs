//@ expect: reject
//@ mechanism: a loop's exit facts name source names, and the assertion (or the function-level
//@ mechanism: postcondition) reads each name by name: where the body binds a name to two locals,
//@ mechanism: the fact about the loop's local was read as a fact about the other. An inner-scope
//@ mechanism: `let mut i` loop before an assertion about the outer `i` at function level (sht,
//@ mechanism: the loop lane's exit facts) and inside an outer loop (shn, the post-loop pass); a
//@ mechanism: block-local `n` shadowing the parameter `n` and bounding the loop (shp); and the
//@ mechanism: postcondition `result >= n` of a function returning the outer `i` (she, the loop
//@ mechanism: lane's exit facts injected into the function-level VC).
//@ accept-means: a fact about one local is credited as a fact about another that shares its name.
//@ WHY THE CONTRACT IS FALSE: with n = 1 the outer i is 0 (sht, shn, she: 0 >= 1 is false), and
//@ WHY THE CONTRACT IS FALSE: the inner loop of shp runs zero times, leaving i = 0 < n = 1.
//@ fixed-by: D-189 (a fact naming a name the body binds to more than one local is not stated)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on a3ba4a3a (D-188) the assertions of sht, shn and shp VERIFIED, sht and shn with them,
//@ teeth: and she was verified; with D-189 sht, shn and she are FAILED and shp's assertion FAILED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n < 1000u32)]
pub fn sht(n: u32) {
    let i = 0u32;
    {
        let mut i = 0u32;
        #[invariant(i <= n)]
        while i < n {
            i += 1;
        }
        let _ = i;
    }
    proof_assert!(i >= n);
}

#[requires(n < 1000u32)]
pub fn shn(n: u32) {
    let mut k = 0u32;
    while k < 2u32 {
        let i = 0u32;
        {
            let mut i = 0u32;
            #[invariant(i <= n)]
            while i < n {
                i += 1;
            }
            let _ = i;
        }
        proof_assert!(i >= n);
        k += 1;
    }
}

#[requires(n < 1000u32)]
pub fn shp(n: u32) {
    let mut i = 0u32;
    {
        let n = 0u32;
        #[invariant(i <= n)]
        while i < n {
            i += 1;
        }
    }
    proof_assert!(i >= n);
}

#[requires(n < 1000u32)]
#[ensures(result >= n)]
pub fn she(n: u32) -> u32 {
    let i = 0u32;
    {
        let mut i = 0u32;
        #[invariant(i <= n)]
        while i < n {
            i += 1;
        }
        let _ = i;
    }
    i
}
