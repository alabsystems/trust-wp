//@ expect: verify
//@ mechanism: control for v13_caller_inherits_a_lent_parameter_final: a caller keeps the credit it
//@ mechanism: takes from a callee whose own lane proves its contract, and a callee that lends its
//@ mechanism: argument keeps its own.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*x < 100i32)]
#[ensures(^x == *x + 1i32)]
pub fn inc(x: &mut i32) {
    *x += 1;
}

#[ensures(result == 4i32)]
pub fn inc_caller() -> i32 {
    let mut a = 3i32;
    inc(&mut a);
    a
}

#[ensures(^x == ^result)]
#[ensures(*x == *result)]
pub fn lend(x: &mut i32) -> &mut i32 {
    x
}

