//@ expect: verify
//@ mechanism: control: a `move` closure's postcondition over its captures' views,
//@ mechanism: `result@ == a@ + b@`, under a precondition that keeps the sum in range. It is how a
//@ mechanism: closure contract of two attributes states machine-integer arithmetic under D-232.
//@ WHY THE CONTRACT IS TRUE: the body returns a + b, which the precondition keeps in i32, so its
//@ WHY THE CONTRACT IS TRUE: view is a@ + b@.
//@ xfail: refuted (a counterexample to a true contract) at the campaign base and here: a capture's
//@ xfail: view in a closure postcondition is not read as the captured value.
//@ xfail-verdict: failed
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(stmt_expr_attributes, proc_macro_hygiene)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn sum_of_captures(a: i32, b: i32) {
    let _closure = {
        #[requires(a@ + b@ >= i32::MIN@ && a@ + b@ <= i32::MAX@)]
        #[ensures(result@ == a@ + b@)]
        move || -> i32 { a + b }
    };
}
