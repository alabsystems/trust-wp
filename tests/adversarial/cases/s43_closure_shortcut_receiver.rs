//@ expect: reject
//@ mechanism: find_body_for_receiver's single-body shortcut bound ANY unresolved closure-spec
//@ mechanism: receiver (a function item T::rem / T::add, a generic F, a &dyn Fn parameter) to
//@ mechanism: the only registered closure body - the proof_assert! marker lambda - pinning the
//@ mechanism: call result to that lambda's value 1.
//@ fixed-by: wp-s43 afef1166 (shortcuts refuse path receivers and unnamed bodies)
//@ accept-means: an unrelated closure body is again inlined as a call's postcondition.
//@ WHY THE CONTRACTS ARE FALSE: 5 + 2 == 7, 8 % 3 == 2, and f is arbitrary, never 1 by fiat.
//@ teeth: before afef1166 every function here verified (base_exit_code=0 on single-fn crates),
//@ teeth: measured on three single-fn probe programs (p_add1, p_generic_f, p_recv).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::ops::{Add, Rem};

pub fn add_call_one() {
    let r = (5i32).add(2);
    proof_assert!(r@ == 1);
}

pub fn rem_call_pos_one() {
    let r = (8i32).rem(3);
    proof_assert!(r@ == 1);
}

#[requires(forall<x: i32> f.precondition((x,)))]
pub fn call_generic_one<F: Fn(i32) -> i32>(f: F) {
    let r = f(5);
    proof_assert!(r@ == 1);
}

#[requires(forall<x: i32> f.precondition((x,)))]
pub fn dyn_one(f: &dyn Fn(i32) -> i32) {
    let r = f(5);
    proof_assert!(r@ == 1);
}
