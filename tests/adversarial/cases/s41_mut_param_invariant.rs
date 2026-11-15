//@ expect: reject
//@ mechanism: wp-s41 — the loop-invariant call-obligation lane names a parameter by its ENTRY name
//@ mechanism: (the one `requires` constrains) even when the loop assigns it, so need_zero(x) after
//@ mechanism: `x = 5` on the previous iteration was discharged against the entry value x == 0.
//@ accept-means: the second-iteration call need_zero(5) was proved from `requires(x@ == 0)`.
//@ fixed-by: wp-s41 extraction.rs loop_assigns_by_value_parameter (fail closed)
//@ also-verified: need_zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
fn need_zero(x: i32) {}

#[requires(x@ == 0)]
pub fn f(mut x: i32) {
    let mut i = 0;
    #[invariant(true)]
    while i < 2 {
        need_zero(x);
        x = 5;
        i += 1;
    }
}
