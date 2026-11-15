//@ expect: reject
//@ mechanism: a `proof_assert!` placed in a loop BEFORE the loop's own test was proved from that
//@ mechanism: test as if it had already passed: `loop { proof_assert!(i < n); if i >= n { break; }
//@ mechanism: i += 1; }` (bb_min), the same with a TRUE `#[invariant(i <= n)]` (bb_inv), inside a
//@ mechanism: `while` condition block before its test (wc1), the same with an invariant (wi), an
//@ mechanism: inner `loop` whose test breaks the outer loop by label (bv5), a test written as a
//@ mechanism: `match` (pm) and an assertion under an `if` before the test (bv4). The `!(i >= n)`
//@ mechanism: the switch's in-body arm establishes was stated wherever the assertion lay in the
//@ mechanism: loop body, whether or not that arm had been taken.
//@ accept-means: an in-body assertion is credited from a loop condition the iteration reaching it
//@ accept-means: has not tested.
//@ WHY THE CONTRACT IS FALSE: with n = 0 every assertion runs once with i = 0 (j = 0 in bv5, c
//@ WHY THE CONTRACT IS FALSE: true in bv4) before the test that ends the loop, and 0 < 0 is false;
//@ WHY THE CONTRACT IS FALSE: bv5 and bb_min with n = 2 also reach it with i = 2 on the last pass.
//@ fixed-by: D-188 (the loop condition is assumed at an assertion only when the switch's in-body
//@ fixed-by: arm, whose only predecessor is the switch, dominates the assertion's block)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on b7ed4bbf (D-187) the assertions of bb_min, bb_inv, wc1, wi and bv5 VERIFIED and those
//@ teeth: five functions with them (pm's and bv4's were unknown); with D-188 every assertion is
//@ teeth: unknown and no function is verified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn bb_min(n: u32) {
    let mut i = 0u32;
    loop {
        proof_assert!(i < n);
        if i >= n {
            break;
        }
        i += 1;
    }
}

pub fn bb_inv(n: u32) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    loop {
        proof_assert!(i < n);
        if i >= n {
            break;
        }
        i += 1;
    }
}

pub fn wc1(n: u32) {
    let mut i = 0u32;
    while {
        proof_assert!(i < n);
        i < n
    } {
        i += 1;
    }
}

pub fn wi(n: u32) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while {
        proof_assert!(i < n);
        i < n
    } {
        i += 1;
    }
}

pub fn bv5(n: u32) {
    'outer: loop {
        let mut j = 0u32;
        loop {
            proof_assert!(j < n);
            if j >= n {
                break 'outer;
            }
            j += 1;
        }
    }
}

pub fn pm(n: u32) {
    let mut i = 0u32;
    loop {
        proof_assert!(i < n);
        match i >= n {
            true => break,
            false => {}
        }
        i += 1;
    }
}

pub fn bv4(n: u32, c: bool) {
    let mut i = 0u32;
    loop {
        if c {
            proof_assert!(i < n);
        }
        if i >= n {
            break;
        }
        i += 1;
    }
}
