//@ expect: verify
//@ mechanism: the price of D-187: a TRUE `proof_assert!` in a loop body that holds only because of
//@ mechanism: what the loop writes, and that no `#[invariant]` states, is no longer proved: `y` is `x`
//@ mechanism: or `x + 1` at the head of every iteration of `while i < n { ..; y = x + 1; .. }`, but
//@ mechanism: with no invariant the loop-head value of `y` is unconstrained (Creusot's implicit
//@ mechanism: `invariant true`).
//@ xfail: D-187 reads a loop-carried local at the loop head, which only the loop's condition and
//@ xfail: invariants constrain; the counterexample over the loop-head symbol is reported unknown,
//@ xfail: never FAILED. Measured: on 5f9337a5 (D-186) the assertion verified (from the first
//@ xfail: iteration's value).
//@ xfail-verdict: unknown
//@ fixed-by: n/a (over-refusal guard, priced by D-187)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x < 100i32 && x > -100i32)]
pub fn s565(x: i32, n: u32) {
    let mut y = x;
    let mut i = 0u32;
    while i < n {
        proof_assert!(y == x || y == x + 1i32);
        y = x + 1i32;
        i += 1;
    }
}
