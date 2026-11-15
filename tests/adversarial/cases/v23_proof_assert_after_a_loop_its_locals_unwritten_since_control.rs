//@ expect: verify
//@ mechanism: control for v23_proof_assert_in_a_later_loop_reads_a_local_its_back_edge_rewrites.rs
//@ mechanism: and v23_loop_exit_fact_over_a_name_two_locals_share.rs: a finished loop's exit facts
//@ mechanism: hold at an assertion inside a later loop that writes only its own counter (seqc), at
//@ mechanism: one followed by a write of the counter that no loop carries back to it (atw), and over
//@ mechanism: names each bound to one local (one).
//@ accept-means: n/a (control) - every assertion holds on every path.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n < 1000u32)]
pub fn seqc(n: u32) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    let mut k = 0u32;
    while k < 2u32 {
        proof_assert!(i >= n);
        k += 1;
    }
}

#[requires(n < 1000u32)]
pub fn atw(n: u32) {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    proof_assert!(i >= n);
    i = 0u32;
    let _ = i;
}

#[requires(n < 1000u32)]
pub fn one(n: u32) {
    let j = 0u32;
    {
        let mut i = 0u32;
        #[invariant(i <= n)]
        while i < n {
            i += 1;
        }
        proof_assert!(i >= n);
    }
    let _ = j;
}
