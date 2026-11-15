//@ expect: verify
//@ mechanism: control for r26_macro_let_captures_caller_assertion.rs (D-238): the same bodies with
//@ mechanism: true assertions about the caller's binding, which hygiene keeps apart from the
//@ mechanism: macro's `let x`; ok6 asserts about a binding the macro reads through an expression
//@ mechanism: argument; oi1 states a loop invariant over the caller's `x`.
//@ accept-means: n/a (control) - every assertion holds.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

macro_rules! zero_x {
    () => {
        let x = 0i32;
        let _ = x;
    };
}

macro_rules! five_x {
    () => {
        let x = 5i32;
        let _ = x;
    };
}

macro_rules! bump_local {
    () => {
        let mut x = 0i32;
        x += 7;
        let _ = x;
    };
}

macro_rules! bind_x_to {
    ($e:expr) => {
        let x = $e;
        let _ = x;
    };
}

#[requires(x@ == 5)]
pub fn ok1(x: i32) {
    zero_x!();
    proof_assert!(x@ == 5);
}

pub fn ok2() {
    let x = 0i32;
    five_x!();
    proof_assert!(x@ == 0);
}

pub fn ok4() {
    let x = 1i32;
    {
        bump_local!();
        proof_assert!(x@ == 1);
    }
}

#[requires(x@ == 1)]
pub fn ok5(x: i32) {
    bind_x_to!(9i32);
    proof_assert!(x@ == 1);
}

pub fn ok6() {
    let y = 3i32;
    bind_x_to!(y);
    proof_assert!(y@ == 3);
}

#[requires(x@ == 5)]
#[ensures(true)]
pub fn oi1(x: i32) {
    zero_x!();
    let mut i = 0i32;
    #[invariant(x@ == 5)]
    while i < 3 {
        i += 1;
    }
}
