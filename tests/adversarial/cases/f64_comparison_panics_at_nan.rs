//@ expect: reject
//@ mechanism: a panic whose reachability turns on a float comparison: `assert!(x == x)`,
//@ mechanism: `assert!(x <= y || x > y)`, `assert!(x >= y)` in the arm taken on `!(x < y)`,
//@ mechanism: `unreachable!()` in the arm taken on `x != x` (over `f32`), and a `panic!` in a loop body
//@ mechanism: taken on `!(x <= x)`. Over the reals each panic is dead; over IEEE-754 each is reached at NaN, so
//@ mechanism: the function's panic-freedom is false. The panic lane's twin of the postcondition cases
//@ mechanism: D-215 lists; i64_comparison_panic_unreached_control.rs is the same bodies over `i64`/`i32`.
//@ accept-means: `assert_self_eq(f64::NAN)`, `assert_total(f64::NAN, 0.0)`,
//@ accept-means: `not_lt_then_ge(f64::NAN, 0.0)`, `unreachable_on_ne_self(f32::NAN)` and
//@ accept-means: `loop_body_panics(f64::NAN)` each panic; an accept claims none of them can.
//@ fixed-by: D-215
//@ teeth: ACCEPTED at the merged campaign tip before D-215 (all five functions verified: the reals make
//@ teeth: each panic unreachable); under D-215 the first four are FAILED (postcondition) and
//@ teeth: `loop_body_panics` is `unknown` (loop call obligations).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn assert_self_eq(x: f64) {
    assert!(x == x);
}

#[ensures(true)]
pub fn assert_total(x: f64, y: f64) {
    assert!(x <= y || x > y);
}

#[ensures(true)]
pub fn not_lt_then_ge(x: f64, y: f64) {
    if !(x < y) {
        assert!(x >= y);
    }
}

#[ensures(true)]
pub fn unreachable_on_ne_self(x: f32) {
    if x != x {
        unreachable!()
    }
}

#[ensures(true)]
pub fn loop_body_panics(x: f64) {
    let mut i = 0i32;
    #[invariant(i <= 3i32)]
    while i < 3i32 {
        if !(x <= x) {
            panic!("unordered")
        }
        i += 1;
    }
}
