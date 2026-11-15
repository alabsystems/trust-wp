//@ expect: verify
//@ mechanism: the integer twin of f64_comparison_panics_at_nan.rs: over `i64` and `i32`, `x == x`,
//@ mechanism: `x <= y || x > y` and `!(x < y) ==> x >= y` hold and `x != x` is false, so no panic in
//@ mechanism: these bodies is reachable.
//@ accept-means: n/a (control) — none of these functions can panic.
//@ fixed-by: n/a (control)
//@ teeth: verified before and after D-215 (each function verified).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn assert_self_eq(x: i64) {
    assert!(x == x);
}

#[ensures(true)]
pub fn assert_total(x: i64, y: i64) {
    assert!(x <= y || x > y);
}

#[ensures(true)]
pub fn not_lt_then_ge(x: i64, y: i64) {
    if !(x < y) {
        assert!(x >= y);
    }
}

#[ensures(true)]
pub fn unreachable_on_ne_self(x: i32) {
    if x != x {
        unreachable!()
    }
}

#[ensures(true)]
pub fn loop_body_panics(x: i64) {
    let mut i = 0i32;
    #[invariant(i <= 3i32)]
    while i < 3i32 {
        if !(x <= x) {
            panic!("unordered")
        }
        i += 1;
    }
}
