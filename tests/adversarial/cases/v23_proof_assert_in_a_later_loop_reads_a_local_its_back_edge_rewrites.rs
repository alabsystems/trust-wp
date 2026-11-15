//@ expect: reject
//@ mechanism: a finished loop's exit facts (`#[invariant(i <= n)]`, `!(i < n)`) were stated at a
//@ mechanism: `proof_assert!` inside a LATER loop whose body writes `i` after the assertion:
//@ mechanism: `while k < 2 { proof_assert!(i >= n); if c { i = 0; } k += 1; }` (seq), the invariant
//@ mechanism: form with `i = n + 1` (seqi), a `loop {}` whose tail writes `i` (seqb), and the
//@ mechanism: same after an unrelated loop between the two (s3). The written-since check walked
//@ mechanism: from the exit arm to the assertion's block and stopped there, so the path from the
//@ mechanism: assertion round the later loop's back edge to the assertion again went uncounted.
//@ accept-means: an assertion in a loop is credited from facts the loop's own back edge falsifies.
//@ WHY THE CONTRACT IS FALSE: with n = 1 and c true the second iteration reads i = 0 (seq, seqb,
//@ WHY THE CONTRACT IS FALSE: s3: 0 >= 1 is false) or i = 2 (seqi: 2 <= 1 is false).
//@ fixed-by: D-189 (a fact established at P is assumed at Q only when P dominates Q and no local
//@ fixed-by: it names is written on any path from P to Q that does not pass P again)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on a3ba4a3a (D-188) all four assertions VERIFIED and seq, seqi and s3 with them; with
//@ teeth: D-189 seq, seqi and s3 are unknown and seqb FAILED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n < 1000u32)]
pub fn seq(n: u32, c: bool) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let mut k = 0u32;
    while k < 2u32 {
        proof_assert!(i >= n);
        if c {
            i = 0u32;
        }
        k += 1;
    }
}

#[requires(n < 1000u32)]
pub fn seqi(n: u32, c: bool) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let mut k = 0u32;
    while k < 2u32 {
        proof_assert!(i <= n);
        if c {
            i = n + 1u32;
        }
        k += 1;
    }
}

#[requires(n < 1000u32)]
pub fn seqb(n: u32, c: bool) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let mut k = 0u32;
    loop {
        proof_assert!(i >= n);
        k += 1;
        if k >= 2u32 {
            break;
        }
        if c {
            i = 0u32;
        }
    }
}

#[requires(n < 1000u32)]
pub fn s3(n: u32, c: bool) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let mut j = 0u32;
    while j < 3u32 {
        j += 1;
    }
    let mut k = 0u32;
    while k < 2u32 {
        proof_assert!(i >= n);
        if c {
            i = 0u32;
        }
        k += 1;
    }
}
