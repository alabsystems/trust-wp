//@ expect: verify
//@ mechanism: control for v7_callsite_old_dialect_swap: the true reading of the callee's contract.
//@ accept-means: n/a (control)
//@ teeth: n/a (control). MEASURED on d73d0571: unknown (the call read the callee's clause at the
//@ teeth: call's entry state, so the final values stayed unconstrained); on the D-101 tree: verified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(*a == old(*b) && *b == old(*a))]
pub fn swap(a: &mut i32, b: &mut i32) {
    let t = *a;
    *a = *b;
    *b = t;
}

#[ensures(^x == *y && ^y == *x)]
pub fn swap_caller(x: &mut i32, y: &mut i32) {
    swap(x, y)
}
