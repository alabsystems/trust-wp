//@ expect: reject
//@ mechanism: a closure's contract text names its captures (D-238). D-237 renames the shadowing
//@ mechanism: `let x` apart and lets the parameter keep its name, but the closure's
//@ mechanism: `#[requires(x@ == 5)]` was not resolved at the closure: its `x` met the capture
//@ mechanism: substitution as the bare source name, which no capture field is called, and the
//@ mechanism: caller's call-site precondition read it as the PARAMETER `x`, which the function's
//@ mechanism: own precondition fixes to 5. cs1 has a postcondition, cc1 none; in both the closure
//@ mechanism: does not capture `x`. cw1 captures it, and its argument `p` is the parameter: the
//@ mechanism: capture substitution at the call projected every name `x` from the closure's state,
//@ mechanism: the argument's too. cf1/cf2 call the closure through a struct field, where the
//@ mechanism: closure's state is no tuple to project and `x` stayed the caller's name. cp5 captures
//@ mechanism: the parameter itself, which a later `let` shadows.
//@ accept-means: the call-site precondition of a closure is read about the parameter its capture
//@ accept-means: shadows.
//@ WHY THE CONTRACT IS FALSE: the closure's x is the local x, which is 0, so each call violates
//@ WHY THE CONTRACT IS FALSE: `x@ == 5`; in cw1 `a` is 5 and x is 0; in cp5 the captured parameter is 0.
//@ also-verified: cw1::{closure#3}, cf1::{closure#3}, cp5::{closure#3}
//@ fixed-by: D-238
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified): before D-238 cs1, cc1, cw1, cf1
//@ teeth: and cf2 VERIFIED; with D-238 cw1 and cf1 FAILED and the others refused. cp5 FAILED on both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 5)]
#[ensures(true)]
pub fn cs1(x: i32) {
    let x = 0i32;
    let f = #[requires(x@ == 5)]
    move || {
        let _ = x;
    };
    f();
}

#[requires(x@ == 5)]
pub fn cc1(x: i32) {
    let x = 0i32;
    let f = #[requires(x@ == 5)]
    move || {
        let _ = x;
    };
    f();
}

#[requires(x@ == 5)]
#[ensures(true)]
pub fn cw1(x: i32) {
    let p = x;
    let x = 0i32;
    let f = #[requires(a@ == x@)]
    move |a: i32| {
        let _z = x;
        let _ = a;
    };
    f(p);
}

pub struct Holder<F> {
    f: F,
}

#[requires(x@ == 5)]
#[ensures(true)]
pub fn cf1(x: i32) {
    let x = 0i32;
    let f = #[requires(x@ == 5)]
    move || {
        let _z = x;
    };
    let h = Holder { f };
    (h.f)();
}

#[requires(x@ == 5)]
#[ensures(true)]
pub fn cf2(x: i32) {
    let x = 0i32;
    let f = #[requires(x@ == 5)]
    move || {};
    let h = Holder { f };
    (h.f)();
    let _ = x;
}

#[requires(x@ == 0)]
#[ensures(true)]
pub fn cp5(x: i32) {
    let f = #[requires(x@ == 5)]
    move || {
        let _z = x;
    };
    let x = 5i32;
    let _ = x;
    f();
}
