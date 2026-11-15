//@ expect: verify
//@ mechanism: the price of D-186: a true `proof_assert!` reading a pointee two stores reach is refused,
//@ mechanism: whatever it claims of them: after `*x = 0; if c { *x = 5; }` (p1, `*x` is 0 or 5), and in a
//@ mechanism: loop body after a store the back edge also carries (p2, `*x = 5; proof_assert!(*x == 5)`).
//@ xfail: D-186 reads a pointee through the walk's recorded value only where ONE store reaches the
//@ xfail: read on every path and that store is on no cycle; p1's read is reached by two stores and
//@ xfail: p2's store is on the loop's cycle, so both are refused as stale reads. Measured: on
//@ xfail: 4c67cea8 (D-185) both verified.
//@ xfail-verdict: unknown
//@ fixed-by: n/a (over-refusal guard, priced by D-186)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn p1(x: &mut i32, c: bool) {
    *x = 0i32;
    if c {
        *x = 5i32;
    }
    proof_assert!(*x == 0i32 || *x == 5i32);
}

pub fn p2(x: &mut i32, n: u32) {
    let mut i = 0u32;
    while i < n {
        *x = 5i32;
        proof_assert!(*x == 5i32);
        i += 1;
    }
}
