//@ expect: verify
//@ mechanism: control for r26_closure_contract_capture_shadows_parameter.rs (D-238): the closure's
//@ mechanism: precondition names the capture that shadows the parameter, and the capture holds
//@ mechanism: what it asks (ok1, and ok4 whose argument is the parameter); ok2: a capture of the
//@ mechanism: parameter itself (ok5: one a later `let` shadows); ok3: a closure parameter named as
//@ mechanism: the function's parameter.
//@ accept-means: n/a (control) - every precondition holds at its call.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
#[ensures(true)]
pub fn ok1(x: i32) {
    let x = 5i32;
    let f = #[requires(x@ == 5)]
    move || {
        let _z = x;
    };
    f();
}

#[requires(x@ == 5)]
#[ensures(true)]
pub fn ok2(x: i32) {
    let f = #[requires(x@ == 5)]
    move || {
        let _z = x;
    };
    f();
}

#[requires(x@ == 0)]
#[ensures(true)]
pub fn ok3(x: i32) {
    let f = #[requires(x@ == 5)]
    |x: i32| {
        let _ = x;
    };
    f(5i32);
}

#[requires(x@ == 0)]
#[ensures(true)]
pub fn ok4(x: i32) {
    let p = x;
    let x = 0i32;
    let f = #[requires(a@ == x@)]
    move |a: i32| {
        let _z = x;
        let _ = a;
    };
    f(p);
}

#[requires(x@ == 5)]
#[ensures(true)]
pub fn ok5(x: i32) {
    let f = #[requires(x@ == 5)]
    move || {
        let _z = x;
    };
    let x = 0i32;
    let _ = x;
    f();
}
