//@ expect: reject
//@ mechanism: a closure's clause read in ANOTHER closure's body (D-239). f's `requires(x@ == 5)`
//@ mechanism: names its capture of the function's parameter `x`; h calls f, and h's own parameter
//@ mechanism: is also `x`. D-238 left a captured parameter's name as written (a parameter keeps
//@ mechanism: its name in every body), so at the call in h the clause read h's `x`, which h's
//@ mechanism: precondition fixes to 5: h verified. cc3 is the same with `move` closures; cc4 has
//@ mechanism: h bind a local `x` instead of taking a parameter. f itself verifies (its body has
//@ mechanism: no obligation); each function errs on the closure-calls-closure sort conflict.
//@ accept-means: a closure precondition over a capture is discharged from a calling closure's
//@ accept-means: own binding of the same name.
//@ WHY THE CONTRACT IS FALSE: the function's `x` is 0, so f's precondition `x@ == 5` (about its
//@ WHY THE CONTRACT IS FALSE: capture of that x) is false at h's call of f.
//@ also-verified: cc2::{closure#2}, cc3::{closure#2}, cc4::{closure#2}
//@ fixed-by: D-239
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified): on 62994450 (D-238) h of cc2
//@ teeth: and of cc3 VERIFIED; with D-239 each is FAILED. cc4's h is FAILED on both (a guard).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
pub fn cc2(x: i32) {
    let f = #[requires(x@ == 5)]
    || {
        let _z = x;
    };
    let h = #[requires(x@ == 5)]
    |x: i32| {
        let _ = x;
        f();
    };
    h(5);
}

#[requires(x@ == 0)]
pub fn cc3(x: i32) {
    let f = #[requires(x@ == 5)]
    move || {
        let _z = x;
    };
    let h = #[requires(x@ == 5)]
    move |x: i32| {
        let _ = x;
        f();
    };
    h(5);
}

#[requires(x@ == 0)]
pub fn cc4(x: i32) {
    let f = #[requires(x@ == 5)]
    || {
        let _z = x;
    };
    let h = #[ensures(true)]
    || {
        let x = 5i32;
        let _ = x;
        f();
    };
    h();
}
