//@ expect: verify
//@ mechanism: control for proof_assert_param_rebind_reads_entry_requires: re-binding a by-value parameter
//@ mechanism: withdraws only the entry facts naming it. An assertion before the write keeps the
//@ mechanism: precondition; one about the value written needs none; one about another parameter keeps that
//@ mechanism: parameter's conjunct of a precondition that also names the re-bound one; a parameter re-bound to
//@ mechanism: another parameter's value reads that one's precondition; a `&mut x` call leaves `x` named by
//@ mechanism: its prophecy, no re-binding, so the callee's postcondition still meets the entry fact.
//@ accept-means: n/a (control)
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 1)]
pub fn before_write(mut x: u32, y: u32) {
    proof_assert!(x@ == 1);
    x = y;
    proof_assert!(x@ == y@);
}

#[requires(x@ < 10)]
pub fn written_value(mut x: u32) {
    x = 7;
    proof_assert!(x@ == 7);
}

#[requires(x@ == 1 && y@ == 2)]
pub fn other_conjunct(mut x: u32, y: u32) {
    x = 3;
    proof_assert!(y@ == 2);
    let _ = x;
}

#[requires(a@ == 1)]
pub fn from_other_param(mut x: u32, a: u32) {
    x = a;
    proof_assert!(x@ == 1);
}

#[requires(a@ < 100)]
#[ensures((^a)@ == (*a)@ + 1)]
pub fn inc(a: &mut u32) {
    *a += 1;
}

#[requires(x@ == 1)]
pub fn through_mut_call(mut x: u32) {
    inc(&mut x);
    proof_assert!(x@ == 2);
}
