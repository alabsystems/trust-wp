//@ expect: reject
//@ mechanism: a `proof_assert!` after a loop that a `break` can leave was proved from the loop's
//@ mechanism: exit facts (its invariant and negated condition) as if every path had left through
//@ mechanism: the condition's exit arm: `#[invariant(i <= n)] while i < n { if c { break; } i += 1;
//@ mechanism: } proof_assert!(i >= n)` at function level, where the loop lane's exit facts are
//@ mechanism: offered (tb), with a `break` that leaves the invariant false (tbi), and the same two
//@ mechanism: after an inner loop in an outer loop's body, where the post-loop pass states them
//@ mechanism: (plb, plbi).
//@ accept-means: an assertion after a loop is credited from exit facts a `break` path never
//@ accept-means: established.
//@ WHY THE CONTRACT IS FALSE: with c true and n = 1 the `break` leaves i = 0 (tb, plb: 0 >= 1 is
//@ WHY THE CONTRACT IS FALSE: false) or i = 2 (tbi, plbi: 2 <= 1 is false).
//@ fixed-by: D-188 (a loop's exit facts are stated at an assertion only when the condition
//@ fixed-by: switch's exit arm, whose only predecessor is the switch, dominates its block)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on b7ed4bbf (D-187) every assertion here VERIFIED (each function unknown or FAILED by
//@ teeth: the loop lane, which flags the break); with D-188 tb's and tbi's are FAILED and plb's
//@ teeth: and plbi's unknown.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n < 1000u32)]
pub fn tb(n: u32, c: bool) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        if c {
            break;
        }
        i += 1;
    }
    proof_assert!(i >= n);
}

#[requires(n < 1000u32)]
pub fn tbi(n: u32, c: bool) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        if c {
            i += 2u32;
            break;
        }
        i += 1;
    }
    proof_assert!(i <= n);
}

pub fn plb(n: u32, c: bool) {
    let mut k = 0u32;
    while k < 2u32 {
        let mut i = 0u32;
        #[invariant(i <= n)]
        while i < n {
            if c {
                break;
            }
            i += 1;
        }
        proof_assert!(i >= n);
        k += 1;
    }
}

#[requires(n < 1000u32)]
pub fn plbi(n: u32, c: bool) {
    let mut k = 0u32;
    while k < 2u32 {
        let mut i = 0u32;
        #[invariant(i <= n)]
        while i < n {
            if c {
                i += 2u32;
                break;
            }
            i += 1;
        }
        proof_assert!(i <= n);
        k += 1;
    }
}
