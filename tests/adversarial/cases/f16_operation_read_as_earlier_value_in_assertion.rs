//@ expect: reject
//@ mechanism: the `proof_assert!` substitution walk (`SubstitutionVisitor::on_assign_local`) keeps a local's
//@ mechanism: earlier binding when it cannot translate an assignment to it, and D-215 left every operator and
//@ mechanism: cast over an `f16` or `f128` untranslated: after `let mut a = 0u32; a = h as u32;` the walk
//@ mechanism: still read `a` as `0`, so `proof_assert!(a == 0u32)` was proved. The spellings: an `f16` cast to
//@ mechanism: an integer, an `f16` sum, an `f16` comparison, an integer cast into `f16` read back out, and an
//@ mechanism: `f128` negation. Under D-217 each operation is an uninterpreted function of its operands and is
//@ mechanism: never left untranslated. The walk's own defect, which these spellings reached and which
//@ mechanism: D-217 does not close, is assertion_reads_local_before_untranslated_reassignment.rs (RED).
//@ mechanism: f16_operation_is_a_function_of_its_operands_control.rs claims what the same bodies do compute.
//@ accept-means: `cast(2.0)`, `arith(1.0)`, `from_int(3)` and `wide(-2.0)` reach their assertion with `a` not
//@ accept-means: `0`, and `compare(h)` with `b == false` for every `h`; an accept claims each assertion holds.
//@ fixed-by: D-217
//@ teeth: ACCEPTED on the merged campaign tip before D-217 (each of the five assertions verified, exit 0);
//@ teeth: each assertion FAILED under D-217.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(f16)]
#![feature(f128)]
#![allow(unused_assignments)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn cast(h: f16) {
    let mut a = 0u32;
    a = h as u32;
    proof_assert!(a == 0u32);
}

pub fn arith(h: f16) {
    let mut a = 0u32;
    a = (h + h) as u32;
    proof_assert!(a == 0u32);
}

pub fn compare(h: f16) {
    let mut b = true;
    b = h < h;
    proof_assert!(b);
}

pub fn from_int(n: u32) {
    let mut h = 0.0f16;
    h = n as f16;
    let mut a = 0u32;
    a = h as u32;
    proof_assert!(a == 0u32);
}

pub fn wide(q: f128) {
    let mut a = 0u32;
    a = (-q) as u32;
    proof_assert!(a == 0u32);
}
