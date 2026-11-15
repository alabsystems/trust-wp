//@ expect: verify
//@ mechanism: control for r31_closure_clause_read_in_calling_closure.rs (D-239): f's precondition
//@ mechanism: over its capture of the parameter `x` holds (x is 5), called from the function body
//@ mechanism: (co1) beside a closure whose own parameter is `x`; co2: a closure's precondition
//@ mechanism: over its own parameter `x` is still read about that parameter.
//@ accept-means: n/a (control) - every precondition holds at its call.
//@ teeth: MEASURED: verifies on 62994450 (D-238) and with D-239 (the rename costs these nothing).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 5)]
pub fn co1(x: i32) {
    let f = #[requires(x@ == 5)]
    || {
        let _z = x;
    };
    let h = |x: i32| {
        let _ = x;
    };
    h(0);
    f();
}

#[requires(x@ == 0)]
pub fn co2(x: i32) {
    let _z = x;
    let h = #[requires(x@ == 5)]
    |x: i32| {
        proof_assert!(x@ == 5);
    };
    h(5);
}
