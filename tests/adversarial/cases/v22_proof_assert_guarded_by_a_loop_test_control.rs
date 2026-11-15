//@ expect: verify
//@ mechanism: the control of D-188: an assertion the loop's test does guard is still proved from
//@ mechanism: it: the `while` condition in the body (c_while), a `loop`'s break test passed before
//@ mechanism: the assertion (c_loop_after_test), a `while` condition block followed by the body's
//@ mechanism: assertion (c_wcond_body), and an assertion after a loop left only through its test,
//@ mechanism: at function level (c_top_after) and after an inner loop (c_nested_after), with an
//@ mechanism: unrelated local written between the exit and the assertion.
//@ fixed-by: n/a (over-refusal guard for D-188)
//@ teeth: MEASURED: every function and assertion verifies on b7ed4bbf (D-187) and with D-188.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn c_while(n: u32) {
    let mut i = 0u32;
    while i < n {
        proof_assert!(i < n);
        i += 1;
    }
}

pub fn c_loop_after_test(n: u32) {
    let mut i = 0u32;
    loop {
        if i >= n {
            break;
        }
        proof_assert!(i < n);
        i += 1;
    }
}

pub fn c_wcond_body(n: u32) {
    let mut i = 0u32;
    while {
        let t = i;
        t < n
    } {
        proof_assert!(i < n);
        i += 1;
    }
}

#[requires(n < 1000u32)]
pub fn c_top_after(n: u32) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let k = 3u32;
    proof_assert!(i >= n);
    let _ = k;
}

pub fn c_nested_after(n: u32) {
    let mut k = 0u32;
    while k < 2u32 {
        let mut j = 0u32;
        #[invariant(j <= n)]
        while j < n {
            j += 1;
        }
        let t = 1u32;
        proof_assert!(j >= n);
        let _ = t;
        k += 1;
    }
}
