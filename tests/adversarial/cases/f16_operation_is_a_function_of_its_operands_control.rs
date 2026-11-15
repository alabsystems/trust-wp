//@ expect: verify
//@ mechanism: the control of f16_operation_read_as_earlier_value_in_assertion.rs: the same assignments, each
//@ mechanism: followed by the same operation over the same operands, and the assertion claims the two
//@ mechanism: results are equal. Rust's `f16`/`f128` operations are functions of their operands, and D-217
//@ mechanism: reads each as an uninterpreted function of them, so congruence proves the claim; the
//@ mechanism: assertion says nothing about which value the operation computes.
//@ accept-means: n/a (control) — each assertion compares two evaluations of one operation on one operand.
//@ fixed-by: n/a (control)
//@ teeth: on the merged campaign tip before D-217 each assertion FAILED (the walk read `a` at its earlier
//@ teeth: value); under D-217 all five verify. The campaign tip, which read the operations over the reals,
//@ teeth: left `from_int_twice` unproved.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(f16)]
#![feature(f128)]
#![allow(unused_assignments)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn cast_twice(h: f16) {
    let mut a = 0u32;
    a = h as u32;
    let b = h as u32;
    proof_assert!(a == b);
}

pub fn arith_twice(h: f16) {
    let mut a = 0u32;
    a = (h + h) as u32;
    let b = (h + h) as u32;
    proof_assert!(a == b);
}

pub fn compare_twice(h: f16, g: f16) {
    let mut a = true;
    a = h < g;
    let b = h < g;
    proof_assert!(a == b);
}

pub fn from_int_twice(n: u32) {
    let mut a = 0u32;
    a = (n as f16) as u32;
    let b = (n as f16) as u32;
    proof_assert!(a == b);
}

pub fn wide_twice(q: f128) {
    let mut a = 0u32;
    a = (-q) as u32;
    let b = (-q) as u32;
    proof_assert!(a == b);
}
